use core::pin::Pin;
use std::sync::Mutex;

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
    async fn new(addr: &str) -> Res<Self> {
        let (ws_stream, _) = connect_async(addr).await?;
        Ok(Self {
            ws_stream,
            remote_session_description_handler: Mutex::new(None),
            remote_ice_candidate_handler: Mutex::new(None),
        })
    }
}

impl RTCSignalClient for SignalClient {
    fn send_session_description(&self, sdp: RTCSessionDescription) {
        unimplemented!()
    }

    fn on_remote_session_description(&self, fun: Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) {
        let mut handler = self.remote_session_description_handler.lock().unwrap();
        *handler = Some(fun);
    }

    fn send_ice_candidate(&self, candidate: RTCIceCandidateInit) {
        unimplemented!()
    }

    fn on_remote_ice_candidate(&self, fun: Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) {
        let mut handler = self.remote_ice_candidate_handler.lock().unwrap();
        *handler = Some(fun);
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
