use std::sync::Arc;
use core::pin::Pin;

use futures::Future;

use webrtc::api::APIBuilder;
use webrtc::data_channel::RTCDataChannel;
use webrtc::data_channel::data_channel_message::DataChannelMessage;
use webrtc::peer_connection::RTCPeerConnection;
use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;
use webrtc::peer_connection::configuration::RTCConfiguration;
use webrtc::ice_transport::ice_server::RTCIceServer;
use webrtc::ice_transport::ice_candidate::RTCIceCandidateInit;
use webrtc::peer_connection::peer_connection_state::RTCPeerConnectionState;

use crate::error::Res;

// https://github.com/webrtc-rs/webrtc/blob/master/examples/examples/data-channels-create/data-channels-create.rs

trait RTCSignalClient : Send + Sync {
    fn send_session_description(&self, sdp: RTCSessionDescription);
    fn on_remote_session_description(&self, fun: Box<dyn Fn(RTCSessionDescription) -> Pin<Box<dyn Future<Output = Res<()>>>>>);
    fn send_ice_candidate(&self, candidate: RTCIceCandidateInit);
    fn on_remote_ice_candidate(&self, fun: Box<dyn Fn(RTCIceCandidateInit) -> Pin<Box<dyn Future<Output = Res<()>>>>>);
}

struct PeerConnection {
    signal_client: Arc<dyn RTCSignalClient>,
    rtc_connection: Arc<RTCPeerConnection>,
}

impl PeerConnection {
    async fn new(signal_client: Arc<dyn RTCSignalClient>) -> Res<Self> {
        let api = APIBuilder::new().build();

        let config = RTCConfiguration {
            ice_servers: vec![RTCIceServer {
                urls: vec!["stun:stun.l.google.com:19302".to_string()],
                ..Default::default()
            }],
            ..Default::default()
        };
        let rtc_connection = Arc::new(api.new_peer_connection(config).await?);
        Ok(Self {signal_client, rtc_connection})
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

        self.rtc_connection.on_data_channel(Box::new(|channel: Arc<RTCDataChannel>| Box::pin(async move {
            println!("Got data channel '{}':'{}'.", channel.label(), channel.id());
            channel.on_message(Box::new(|message: DataChannelMessage| Box::pin(async move {
                println!("Got data channel message: {:?}", message);
            }))).await;
            channel.on_error(Box::new(|err| Box::pin(async move {
                println!("Got data channel error: {:?}", err);
            }))).await;
            channel.on_close(Box::new(|| Box::pin(async move {
                println!("Got data channel close.");
            }))).await;
        }))).await;

        let offer = self.rtc_connection.create_offer(None).await?;
        self.rtc_connection.set_local_description(offer.clone()).await?;
        self.signal_client.send_session_description(offer);
        Ok(())
    }
    async fn create_data_channel(&mut self, label: &str) -> Res<Arc<RTCDataChannel>> {
        let channel = self.rtc_connection.create_data_channel(label, None).await?;
        let channel2 = channel.clone();
        channel.on_open(Box::new(move || Box::pin(async move {
            println!("Data channel '{}':'{}' open.", channel2.label(), channel2.id());
        }))).await;
        Ok(channel)
    }
}
