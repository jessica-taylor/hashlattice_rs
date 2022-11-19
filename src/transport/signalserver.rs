use core::mem::drop;
use std::net::SocketAddr;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use anyhow::anyhow;
use async_mutex::Mutex as AsyncMutex;
use futures::{StreamExt, SinkExt};

use tokio_tungstenite::{WebSocketStream, MaybeTlsStream, connect_async};
use tokio::net::{TcpListener, TcpStream};
use tungstenite::protocol::Message;


use crate::error::Res;
use crate::transport::signalmessage::{Peer, SignalMessageToClient, SignalMessageToServer};

// https://github.com/snapview/tokio-tungstenite/blob/master/examples/autobahn-server.rs

pub struct SignalServer {
    peer_streams: Mutex<BTreeMap<Peer, Arc<AsyncMutex<WebSocketStream<TcpStream>>>>>,
}

impl SignalServer {
    pub fn new() -> Self {
        let peer_streams = Mutex::new(BTreeMap::new());
        SignalServer { peer_streams }
    }
    pub async fn listen(self: Arc<Self>, addr: &str) -> Res<()> {
        let addr = "127.0.0.1:2020";

        // Create the event loop and TCP listener we'll accept connections on.
        let listener = TcpListener::bind(&addr).await?;
        println!("Listening on: {}", addr);

        while let Ok((stream, _)) = listener.accept().await {
            tokio::spawn(self.clone().accept_connection(stream));
        }

        Ok(())
    }

    async fn accept_connection(self: Arc<Self>, stream: TcpStream) {
        let addr = stream.peer_addr().expect("connected streams should have a peer address");
        println!("Peer address: {}", addr);


        println!("New WebSocket connection: {}", addr);

        if let Err(e) = self.handle_connection(addr, stream).await {
            println!("Error handling websocket connection: {}", e);
        }
    }

    async fn send_to(self: &Arc<Self>, remote_peer: Peer, message: SignalMessageToClient) -> Res<()> {
        let opt_stream = {
            let peer_streams = self.peer_streams.lock().unwrap();
            peer_streams.get(&remote_peer).cloned()
        };
        if let Some(stream) = opt_stream {
            let mut stream = stream.lock().await;
            let bs = rmp_serde::to_vec(&message)?;
            stream.send(Message::Binary(bs)).await?;
        }
        Ok(())
    }

    async fn handle_connection(self: Arc<Self>, peer: SocketAddr, stream: TcpStream) -> Res<()> {
        let mut ws_stream = Arc::new(AsyncMutex::new(tokio_tungstenite::accept_async(stream).await?));
        let mut this_peer: Option<Peer> = None;
        loop {
            let mut stream = ws_stream.lock().await;
            let opt_msg = stream.next().await;
            drop(stream);
            match opt_msg {
                None => return Ok(()),
                Some(msg) => match msg? {
                    Message::Binary(bs) => {
                        let msg: SignalMessageToServer = rmp_serde::from_slice(&bs)?;
                        match msg {
                            SignalMessageToServer::SetPeer(peer) => {
                                let mut peer_streams = self.peer_streams.lock().unwrap();
                                peer_streams.insert(peer, ws_stream.clone());
                                this_peer = Some(peer);
                            }
                            SignalMessageToServer::SessionDescription(remote_peer, session_desc) => {
                                let msg = SignalMessageToClient::SessionDescription(this_peer.ok_or(anyhow!("must set peer first"))?, session_desc);
                                self.send_to(remote_peer, msg).await?;
                            }
                            SignalMessageToServer::IceCandidate(remote_peer, candidate) => {
                                let msg = SignalMessageToClient::IceCandidate(this_peer.ok_or(anyhow!("must set peer first"))?, candidate);
                                self.send_to(remote_peer, msg).await?;
                            }
                            _ => println!("Received a message from {}: {:?}", peer, msg),
                        }
                    }
                    other => {
                        println!("Received a message which is not binary: {:?}", other);
                    }
                }
            }
        }
        Ok(())
    }
}

