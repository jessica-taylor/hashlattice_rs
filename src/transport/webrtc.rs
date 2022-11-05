use core::pin::Pin;
use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;
use std::mem;
use std::cell::RefCell;
use std::ops::DerefMut;

use bytes::Bytes;
use futures::Future;
use futures::channel::oneshot;
use anyhow::{anyhow, bail};
use serde::{Serialize, Deserialize, de::DeserializeOwned};
use webrtc::api::APIBuilder;
use webrtc::data_channel::RTCDataChannel;
use webrtc::data_channel::data_channel_message::DataChannelMessage;
use webrtc::peer_connection::RTCPeerConnection;
use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;
use webrtc::peer_connection::configuration::RTCConfiguration;
use webrtc::ice_transport::ice_server::RTCIceServer;
use webrtc::ice_transport::ice_candidate::RTCIceCandidateInit;
use webrtc::peer_connection::peer_connection_state::RTCPeerConnectionState;

use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode};
use crate::error::{Res, to_string_result};
use crate::lattice::{HashLookup, LatMerkleNode};

// https://github.com/webrtc-rs/webrtc/blob/master/examples/examples/data-channels-create/data-channels-create.rs

trait RemoteAccessibleContext : HashLookup {
    fn lattice_lookup(self: Arc<Self>, key: &[u8]) -> Res<Option<Hash<LatMerkleNode<Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>>>>>;
}

trait RTCSignalClient : Send + Sync {
    fn send_session_description(&self, sdp: RTCSessionDescription);
    fn on_remote_session_description(&self, fun: Box<dyn Fn(RTCSessionDescription) -> Pin<Box<dyn Future<Output = Res<()>>>>>);
    fn send_ice_candidate(&self, candidate: RTCIceCandidateInit);
    fn on_remote_ice_candidate(&self, fun: Box<dyn Fn(RTCIceCandidateInit) -> Pin<Box<dyn Future<Output = Res<()>>>>>);
}

struct DataChannel<T> {
    channel: Arc<RTCDataChannel>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Serialize + DeserializeOwned + Send + Sync + 'static> DataChannel<T> {
    fn new(channel: Arc<RTCDataChannel>) -> Self {
        Self {
            channel,
            _phantom: std::marker::PhantomData,
        }
    }

    async fn send(&self, value: &T) -> Res<()> {
        let bs = rmp_serde::to_vec(value)?;
        let len = bs.len();
        let n = self.channel.send(&Bytes::from(bs)).await?;
        if n != len {
            bail!("Failed to send all bytes");
        }
        Ok(())
    }

    async fn on_receive(&self, fun: Box<dyn Send + Sync + Fn(T) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) -> Res<()> {
        let fun = Arc::new(fun);
        self.channel.on_message(Box::new(move |message: DataChannelMessage| {
            let fun = fun.clone();
            Box::pin(async move {
                if message.is_string {
                    println!("Ignoring non-binary message {:?}", message);
                } else {
                    let value: T = match rmp_serde::from_slice(&message.data) {
                        Ok(value) => value,
                        Err(e) => {
                            println!("Failed to deserialize message: {:?}", e);
                            return;
                        }
                    };
                    match fun(value).await {
                        Ok(()) => (),
                        Err(e) => println!("Failed to handle message: {:?}", e),
                    }
                }
            })
        })).await;
        Ok(())
    }

}

type QueryId = u64;

struct QueryState<M: TaggedMapping> {
    query_count: QueryId,
    query_receivers: BTreeMap<QueryId, oneshot::Sender<Res<M::Value>>>,
}

struct QueryChannel<M: TaggedMapping> {
    query_state: Mutex<QueryState<M>>,
    query_channel: DataChannel<(QueryId, M::Key)>,
    result_channel: DataChannel<(QueryId, Result<M::Value, String>)>,
    remote_query_channel: DataChannel<(QueryId, M::Key)>,
    remote_result_channel: DataChannel<(QueryId, Result<M::Value, String>)>,
}

impl<M: TaggedMapping + 'static> QueryChannel<M> {
    fn new(query_channel: DataChannel<(QueryId, M::Key)>,
           result_channel: DataChannel<(QueryId, Result<M::Value, String>)>,
           remote_query_channel: DataChannel<(QueryId, M::Key)>,
           remote_result_channel: DataChannel<(QueryId, Result<M::Value, String>)>) -> Self {
        Self {
            query_state: Mutex::new(QueryState {
                query_count: 0,
                query_receivers: BTreeMap::new(),
            }),
            query_channel,
            result_channel,
            remote_query_channel,
            remote_result_channel,
        }
    }
    async fn send_result(&self, qid: QueryId, value: Res<M::Value>) -> Res<()> {
        self.result_channel.send(&(qid, to_string_result(value))).await
    }
    async fn got_result(&self, qid: QueryId, value: Result<M::Value, String>) -> Res<()> {
        let mut query_state = self.query_state.lock().unwrap();
        let sender = query_state.query_receivers.remove(&qid);
        if let Some(sender) = sender {
            sender.send(value.map_err(|e| anyhow!("{}", e))).unwrap();
        }
        Ok(())
    }
    async fn query(&self, key: M::Key) -> Res<M::Value> {
        let (sender, receiver) = oneshot::channel();
        let qid = {
            let mut query_state = self.query_state.lock().unwrap();
            let qid = query_state.query_count;
            query_state.query_count += 1;
            query_state.query_receivers.insert(qid, sender);
            qid
        };
        self.query_channel.send(&(qid, key)).await?;
        receiver.await.unwrap()
    }
}

struct HashLookupMapping;
impl TaggedMapping for HashLookupMapping {
    type Key = HashCode;
    type Value = Vec<u8>;
}

struct LatticeLookupMapping;
impl TaggedMapping for LatticeLookupMapping {
    type Key = Vec<u8>;
    type Value = Hash<Option<LatMerkleNode<Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>>>>;
}


// what's the API?
// we should have:
// - hash lookup
// - lattice lookup
// - computations? lattice computations? get cached values only
struct PeerConnection {
    accessible_context: Arc<dyn RemoteAccessibleContext>,
    signal_client: Arc<dyn RTCSignalClient>,
    rtc_connection: Arc<RTCPeerConnection>,
    hash_lookup_channel: oneshot::Receiver<QueryChannel<HashLookupMapping>>,
    lattice_lookup_channel: oneshot::Receiver<QueryChannel<LatticeLookupMapping>>,
}

impl PeerConnection {
    async fn new(accessible_context: Arc<dyn RemoteAccessibleContext>, signal_client: Arc<dyn RTCSignalClient>) -> Res<Self> {
        let api = APIBuilder::new().build();

        let config = RTCConfiguration {
            ice_servers: vec![RTCIceServer {
                urls: vec!["stun:stun.l.google.com:19302".to_string()],
                ..Default::default()
            }],
            ..Default::default()
        };
        let rtc_connection = Arc::new(api.new_peer_connection(config).await?);
        let (hl_sender, hl_receiver) = oneshot::channel();
        let (ll_sender, ll_receiver) = oneshot::channel();
        let mut res = Self {
            accessible_context,
            signal_client,
            rtc_connection,
            hash_lookup_channel: hl_receiver,
            lattice_lookup_channel: ll_receiver,
        };
        res.initialize(hl_sender, ll_sender).await?;
        Ok(res)
    }

    async fn initialize(&mut self, hl_sender: oneshot::Sender<QueryChannel<HashLookupMapping>>, ll_sender: oneshot::Sender<QueryChannel<LatticeLookupMapping>>) -> Res<()> {

        let rtc_connection = self.rtc_connection.clone();

        self.signal_client.clone().on_remote_session_description(Box::new(move |sdp| {
            let rtc_connection = rtc_connection.clone();
            Box::pin(async move {
                rtc_connection.set_remote_description(sdp).await?;
                Ok(())
            })
        }));

        let offer = self.rtc_connection.create_offer(None).await?;
        self.rtc_connection.set_local_description(offer.clone()).await?;
        self.signal_client.send_session_description(offer);

        let rtc_connection = self.rtc_connection.clone();

        self.signal_client.clone().on_remote_ice_candidate(Box::new(move |candidate| {
            let rtc_connection = rtc_connection.clone();
            Box::pin(async move {
                rtc_connection.add_ice_candidate(candidate).await?;
                Ok(())
            })
        }));

        self.rtc_connection.on_peer_connection_state_change(Box::new(|s: RTCPeerConnectionState| Box::pin(async move {
            println!("Peer Connection State has changed: {}", s);

            if s == RTCPeerConnectionState::Failed {
                panic!("Peer Connection has gone to failed exiting");
            }

        }))).await;

        let signal_client = self.signal_client.clone();

        self.rtc_connection.on_ice_candidate(Box::new(move |candidate| {
            let signal_client = signal_client.clone();
            Box::pin(async move {
                println!("ICE Candidate: {:?}", candidate);
                if let Some(candidate) = candidate {
                    signal_client.send_ice_candidate(candidate.to_json().await.unwrap());
                }
            })
        })).await;

        let hl_local_channel = self.create_data_channel("hash_lookup").await?;
        let hl_local_result_channel = self.create_data_channel("hash_lookup_result").await?;
        let ll_local_channel = self.create_data_channel("lattice_lookup").await?;
        let ll_local_result_channel = self.create_data_channel("lattice_lookup_result").await?;

        let (hl_remote_channel_sender, hl_remote_channel_receiver) = oneshot::channel::<Arc<RTCDataChannel>>();
        let (hl_remote_result_channel_sender, hl_remote_result_channel_receiver) = oneshot::channel::<Arc<RTCDataChannel>>();
        let (ll_remote_channel_sender, ll_remote_channel_receiver) = oneshot::channel::<Arc<RTCDataChannel>>();
        let (ll_remote_result_channel_sender, ll_remote_result_channel_receiver) = oneshot::channel::<Arc<RTCDataChannel>>();

        let hl_remote_channel_sender = Arc::new(Mutex::new(Some(hl_remote_channel_sender)));
        let hl_remote_result_channel_sender = Arc::new(Mutex::new(Some(hl_remote_result_channel_sender)));
        let ll_remote_channel_sender = Arc::new(Mutex::new(Some(ll_remote_channel_sender)));
        let ll_remote_result_channel_sender = Arc::new(Mutex::new(Some(ll_remote_result_channel_sender)));

        self.rtc_connection.on_data_channel(Box::new(move |channel: Arc<RTCDataChannel>| {
            let hl_remote_channel_sender = hl_remote_channel_sender.clone();
            let hl_remote_result_channel_sender = hl_remote_result_channel_sender.clone();
            let ll_remote_channel_sender = ll_remote_channel_sender.clone();
            let ll_remote_result_channel_sender = ll_remote_result_channel_sender.clone();
            Box::pin(async move {
                println!("Got data channel '{}':'{}'.", channel.label(), channel.id());
                let label = channel.label();
                if label == "hash_lookup" {
                    let mut chan = hl_remote_channel_sender.lock().unwrap();
                    if let Some(s) = mem::replace(chan.deref_mut(), None) {
                        s.send(channel).map_err(|_| format!("failed to send channel")).unwrap();
                    }

                } else if label == "hash_lookup_result" {
                    let mut chan = hl_remote_result_channel_sender.lock().unwrap();
                    if let Some(s) = mem::replace(chan.deref_mut(), None) {
                        s.send(channel).map_err(|_| format!("failed to send channel")).unwrap();
                    }
                } else if label == "lattice_lookup" {
                    let mut chan = ll_remote_channel_sender.lock().unwrap();
                    if let Some(s) = mem::replace(chan.deref_mut(), None) {
                        s.send(channel).map_err(|_| format!("failed to send channel")).unwrap();
                    }
                } else if label == "lattice_lookup_result" {
                    let mut chan = ll_remote_result_channel_sender.lock().unwrap();
                    if let Some(s) = mem::replace(chan.deref_mut(), None) {
                        s.send(channel).map_err(|_| format!("failed to send channel")).unwrap();
                    }
                } else {
                    println!("unknown channel label");
                    // TODO panic?
                }
            })
            // })).await;
            // channel.on_error(Box::new(|err| Box::pin(async move {
            //     println!("Got data channel error: {:?}", err);
            // }))).await;
            // channel.on_close(Box::new(|| Box::pin(async move {
            //     println!("Got data channel close.");
            // }))).await;
        })).await;

        let hl_remote_channel = DataChannel::new(hl_remote_channel_receiver.await.unwrap());
        let hl_remote_result_channel = DataChannel::new(hl_remote_result_channel_receiver.await.unwrap());
        let ll_remote_channel = DataChannel::new(ll_remote_channel_receiver.await.unwrap());
        let ll_remote_result_channel = DataChannel::new(ll_remote_result_channel_receiver.await.unwrap());

        hl_sender.send(QueryChannel::new(hl_local_channel, hl_remote_channel, hl_local_result_channel, hl_remote_result_channel)).map_err(|_| format!("failed to send channel")).unwrap();
        ll_sender.send(QueryChannel::new(ll_local_channel, ll_remote_channel, ll_local_result_channel, ll_remote_result_channel)).map_err(|_| format!("failed to send channel")).unwrap();

        Ok(())
    }
    async fn create_data_channel<T: Serialize + DeserializeOwned + Send + Sync + 'static>(&mut self, label: &str) -> Res<DataChannel<T>> {
        let channel = self.rtc_connection.create_data_channel(label, None).await?;
        Ok(DataChannel::new(channel))
    }
}

// impl RemoteAccessibleContext for PeerConnection
