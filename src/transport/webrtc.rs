use core::pin::Pin;
use core::task::Poll;
use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;




use async_trait::async_trait;
use bytes::Bytes;
use futures::{Future};
use futures::future::poll_fn;
use futures::channel::oneshot;
use anyhow::{anyhow, bail};
use serde::{Serialize, de::DeserializeOwned};
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

#[async_trait]
pub trait RemoteAccessibleContext : HashLookup {
    async fn lattice_lookup(self: Arc<Self>, key: Vec<u8>) -> Res<Option<Hash<LatMerkleNode<Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>>>>>;
}

pub trait RTCSignalClient : Send + Sync {

    fn send_session_description(&self, sdp: RTCSessionDescription);

    fn on_remote_session_description(&self, fun: Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>);

    fn send_ice_candidate(&self, candidate: RTCIceCandidateInit);

    fn on_remote_ice_candidate(&self, fun: Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>);
}

struct DataChannel<T> {
    channel: Arc<RTCDataChannel>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Serialize + DeserializeOwned + Send + Sync + 'static> DataChannel<T> {
    async fn new(channel: Arc<RTCDataChannel>) -> Self {

        channel.on_error(Box::new(|err| Box::pin(async move {
            println!("Got data channel error: {:?}", err);
        }))).await;

        channel.on_close(Box::new(|| Box::pin(async move {
            println!("Got data channel close.");
        }))).await;

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
    query_handler: Box<dyn Send + Sync + Fn(M::Key) -> Pin<Box<dyn Send + Future<Output = Res<M::Value>>>>>,
}

impl<M: TaggedMapping + 'static> QueryChannel<M> {
    async fn new(query_channel: DataChannel<(QueryId, M::Key)>,
           result_channel: DataChannel<(QueryId, Result<M::Value, String>)>,
           remote_query_channel: DataChannel<(QueryId, M::Key)>,
           remote_result_channel: DataChannel<(QueryId, Result<M::Value, String>)>,
           query_handler: impl 'static + Send + Sync + Fn(M::Key) -> Pin<Box<dyn Send + Future<Output = Res<M::Value>>>>) -> Arc<Self> {
        let this = Arc::new(Self {
            query_state: Mutex::new(QueryState {
                query_count: 0,
                query_receivers: BTreeMap::new(),
            }),
            query_channel,
            result_channel,
            remote_query_channel,
            remote_result_channel,
            query_handler: Box::new(query_handler),
        });

        let this2 = this.clone();
        this.remote_query_channel.on_receive(Box::new(move |(query_id, key)| {
            let this = this2.clone();
            Box::pin(async move {
                let value = (this.query_handler)(key).await;
                this.remote_result_channel.send(&(query_id, to_string_result(value))).await?;
                Ok(())
            })
        })).await.unwrap();

        let this2 = this.clone();
        this.remote_result_channel.on_receive(Box::new(move |(query_id, res)| {
            let this = this2.clone();
            Box::pin(async move {
                let mut query_state = this.query_state.lock().unwrap();
                let sender = query_state.query_receivers.remove(&query_id);
                if let Some(sender) = sender {
                    sender.send(res.map_err(|e| anyhow!("{}", e))).unwrap();
                }
                Ok(())
            })
        })).await.unwrap();

        this
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
    type Value = Option<Hash<LatMerkleNode<Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>>>>;
}

fn send_mutex_oneshot<T>(sender: &Mutex<Option<oneshot::Sender<T>>>, value: T) -> Res<()> {
    let mut sender = sender.lock().unwrap();
    if let Some(sender) = sender.take() {
        sender.send(value).map_err(|_| format!("failed to send oneshot")).unwrap();
    } else {
        bail!("Sender already sent");
    }
    Ok(())
}

async fn poll_mutex_option<T: Clone>(mutex: &Mutex<Option<T>>) -> T {
    poll_fn(|_| {
        let lock = mutex.lock().unwrap();
        if let Some(value) = lock.as_ref() {
            Poll::Ready(value.clone())
        } else {
            Poll::Pending
        }
    }).await
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
    hash_lookup_channel: Mutex<Option<Arc<QueryChannel<HashLookupMapping>>>>,
    lattice_lookup_channel: Mutex<Option<Arc<QueryChannel<LatticeLookupMapping>>>>,
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
        let mut res = Self {
            accessible_context,
            signal_client,
            rtc_connection,
            hash_lookup_channel: Mutex::new(None),
            lattice_lookup_channel: Mutex::new(None),
        };
        res.initialize().await?;
        Ok(res)
    }

    async fn initialize(&mut self) -> Res<()> {

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
                    send_mutex_oneshot(&*hl_remote_channel_sender, channel).unwrap();
                } else if label == "hash_lookup_result" {
                    send_mutex_oneshot(&*hl_remote_result_channel_sender, channel).unwrap();
                } else if label == "lattice_lookup" {
                    send_mutex_oneshot(&*ll_remote_channel_sender, channel).unwrap();
                } else if label == "lattice_lookup_result" {
                    send_mutex_oneshot(&*ll_remote_result_channel_sender, channel).unwrap();
                } else {
                    println!("unknown channel label {}", label);
                    // TODO panic?
                }
            })
        })).await;

        let hl_remote_channel = DataChannel::new(hl_remote_channel_receiver.await.unwrap()).await;
        let hl_remote_result_channel = DataChannel::new(hl_remote_result_channel_receiver.await.unwrap()).await;
        let ll_remote_channel = DataChannel::new(ll_remote_channel_receiver.await.unwrap()).await;
        let ll_remote_result_channel = DataChannel::new(ll_remote_result_channel_receiver.await.unwrap()).await;

        let accessible_context = self.accessible_context.clone();

        let hl_channel = QueryChannel::new(hl_local_channel, hl_remote_channel, hl_local_result_channel, hl_remote_result_channel, move |hashcode| Box::pin(
            accessible_context.clone().hash_lookup(hashcode)
        )).await;

        self.hash_lookup_channel.lock().unwrap().replace(hl_channel);

        let accessible_context = self.accessible_context.clone();

        let ll_channel = QueryChannel::new(ll_local_channel, ll_remote_channel, ll_local_result_channel, ll_remote_result_channel, move |key: Vec<u8>| Box::pin(
            accessible_context.clone().lattice_lookup(key)
        )).await;

        self.lattice_lookup_channel.lock().unwrap().replace(ll_channel);
        Ok(())
    }
    async fn create_data_channel<T: Serialize + DeserializeOwned + Send + Sync + 'static>(&mut self, label: &str) -> Res<DataChannel<T>> {
        let channel = self.rtc_connection.create_data_channel(label, None).await?;
        Ok(DataChannel::new(channel).await)
    }
}

#[async_trait]
impl HashLookup for PeerConnection {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        poll_mutex_option(&self.hash_lookup_channel).await.query(hash).await
    }
}

#[async_trait]
impl RemoteAccessibleContext for PeerConnection {
    async fn lattice_lookup(self: Arc<Self>, key: Vec<u8>) -> Res<Option<Hash<LatMerkleNode<Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>>>>> {
        poll_mutex_option(&self.lattice_lookup_channel).await.query(key).await
    }
}
