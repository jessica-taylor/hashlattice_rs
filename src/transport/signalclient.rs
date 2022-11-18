use core::pin::Pin;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use futures::{Future, StreamExt};
use tokio::net::TcpStream;
use tungstenite::protocol::Message;
use tokio_tungstenite::{WebSocketStream, MaybeTlsStream, connect_async};
use webrtc::ice_transport::ice_candidate::RTCIceCandidateInit;
use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;

use crate::error::Res;
use crate::transport::signalmessage::SignalMessageToClient;
use crate::transport::webrtc::RTCSignalClient;

pub struct SignalClient {
    ws_stream: WebSocketStream<MaybeTlsStream<TcpStream>>,
    remote_session_description_handler: Mutex<Option<Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>>>,
    remote_ice_candidate_handler: Mutex<Option<Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>>>,
}

impl SignalClient {
    pub async fn new(addr: &str) -> Res<Self> {
        let (ws_stream, _) = connect_async(addr).await?;
        Ok(Self {
            ws_stream,
            remote_session_description_handler: Mutex::new(None),
            remote_ice_candidate_handler: Mutex::new(None),
        })
    }
}

#[async_trait]
impl RTCSignalClient for SignalClient {
    async fn send_session_description(self: Arc<Self>, sdp: RTCSessionDescription) -> Res<()> {
        unimplemented!()
    }

    async fn on_remote_session_description(self: Arc<Self>, fun: Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) -> Res<()> {
        let mut handler = self.remote_session_description_handler.lock().unwrap();
        *handler = Some(fun);
        Ok(())
    }

    async fn send_ice_candidate(self: Arc<Self>, candidate: RTCIceCandidateInit) -> Res<()> {
        unimplemented!()
    }

    async fn on_remote_ice_candidate(self: Arc<Self>, fun: Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) -> Res<()> {
        let mut handler = self.remote_ice_candidate_handler.lock().unwrap();
        *handler = Some(fun);
        Ok(())
    }
}


// https://github.com/snapview/tokio-tungstenite/blob/master/examples/autobahn-client.rs


async fn runclient(addr: &str) -> Res<()> {
    let (mut ws_stream, _) = connect_async(addr).await?;
    while let Some(msg) = ws_stream.next().await {
        match msg? {
            Message::Binary(bs) => {
                let msg: SignalMessageToClient = rmp_serde::from_slice(&bs)?;
                println!("Received a message: {:?}", msg);
                // ...
            }
            other => {
                println!("Received a message which is not binary: {:?}", other);
            }
        }
    }

    Ok(())
}
