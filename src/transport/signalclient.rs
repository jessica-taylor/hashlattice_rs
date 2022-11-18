use core::pin::Pin;
use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;

use async_mutex::Mutex as AsyncMutex;
use async_trait::async_trait;
use futures::{Future, StreamExt, SinkExt};
use tokio::net::TcpStream;
use tungstenite::protocol::Message;
use tokio_tungstenite::{WebSocketStream, MaybeTlsStream, connect_async};
use webrtc::ice_transport::ice_candidate::RTCIceCandidateInit;
use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;

use crate::error::Res;
use crate::transport::signalmessage::{SignalMessageToClient, SignalMessageToServer, Peer};
use crate::transport::webrtc::RTCSignalClient;

pub struct SignalClient {
    ws_stream: AsyncMutex<WebSocketStream<MaybeTlsStream<TcpStream>>>,
    remote_session_description_handler: Mutex<BTreeMap<Peer, Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>>>,
    remote_ice_candidate_handler: Mutex<BTreeMap<Peer, Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>>>,
}

impl SignalClient {
    pub async fn new(addr: &str) -> Res<Self> {
        let (ws_stream, _) = connect_async(addr).await?;
        Ok(Self {
            ws_stream: AsyncMutex::new(ws_stream),
            remote_session_description_handler: Mutex::new(BTreeMap::new()),
            remote_ice_candidate_handler: Mutex::new(BTreeMap::new()),
        })
    }

    pub async fn handle_messages(self: &Arc<Self>) -> Res<()> {
        loop {
            if let Some(msg) = {
                let mut ws_stream = self.ws_stream.lock().await;
                ws_stream.next().await
            } {
                match msg? {
                    Message::Binary(bs) => {
                        let msg: SignalMessageToClient = rmp_serde::from_slice(&bs)?;
                        match msg {
                            SignalMessageToClient::SessionDescription(peer, desc) => {
                                if let Some(handler) = self.remote_session_description_handler.lock().unwrap().get(&peer) {
                                    handler(desc).await?;
                                }
                            },
                            SignalMessageToClient::IceCandidate(peer, candidate) => {
                                if let Some(handler) = self.remote_ice_candidate_handler.lock().unwrap().get(&peer) {
                                    handler(candidate).await?;
                                }
                            },
                            _ => {
                                println!("Received unexpected message: {:?}", msg);
                            }
                        }
                    }
                    other => {
                        println!("Received a message which is not binary: {:?}", other);
                    }
                }
            }
        }
    }
}

#[async_trait]
impl RTCSignalClient for SignalClient {
    async fn send_session_description(self: Arc<Self>, peer: Peer, sdp: RTCSessionDescription) -> Res<()> {
        let msg = SignalMessageToServer::SessionDescription(peer, sdp);
        let mut ws_stream = self.ws_stream.lock().await;
        ws_stream.send(Message::Binary(serde_json::to_vec(&msg)?)).await?;
        Ok(())
    }

    async fn on_remote_session_description(self: Arc<Self>, peer: Peer, fun: Box<dyn Send + Sync + Fn(RTCSessionDescription) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) -> Res<()> {
        let mut handler = self.remote_session_description_handler.lock().unwrap();
        handler.insert(peer, fun);
        Ok(())
    }

    async fn send_ice_candidate(self: Arc<Self>, peer: Peer, candidate: RTCIceCandidateInit) -> Res<()> {
        let msg = SignalMessageToServer::IceCandidate(peer, candidate);
        let mut ws_stream = self.ws_stream.lock().await;
        ws_stream.send(Message::Binary(serde_json::to_vec(&msg)?)).await?;
        Ok(())
    }

    async fn on_remote_ice_candidate(self: Arc<Self>, peer: Peer, fun: Box<dyn Send + Sync + Fn(RTCIceCandidateInit) -> Pin<Box<dyn Send + Future<Output = Res<()>>>>>) -> Res<()> {
        let mut handler = self.remote_ice_candidate_handler.lock().unwrap();
        handler.insert(peer, fun);
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
