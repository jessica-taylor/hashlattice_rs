use std::net::SocketAddr;
use std::collections::BTreeMap;
use std::sync::Mutex;

use futures::{StreamExt};

use tokio_tungstenite::{WebSocketStream, MaybeTlsStream, connect_async};
use tokio::net::{TcpListener, TcpStream};
use tungstenite::protocol::Message;


use crate::error::Res;
use crate::transport::signalmessage::{Peer, SignalMessageToClient, SignalMessageToServer};

// https://github.com/snapview/tokio-tungstenite/blob/master/examples/autobahn-server.rs

struct SignalServer {
    peer_streams: Mutex<BTreeMap<Peer, WebSocketStream<MaybeTlsStream<TcpStream>>>>,
}

async fn runserver() -> Res<()> {
    // let addr = env::args().nth(1).unwrap_or_else(|| "127.0.0.1:8080".to_string());
    let addr = "127.0.0.1:2020";

    // Create the event loop and TCP listener we'll accept connections on.
    let listener = TcpListener::bind(&addr).await?;
    println!("Listening on: {}", addr);

    while let Ok((stream, _)) = listener.accept().await {
        tokio::spawn(accept_connection(stream));
    }

    Ok(())
}

async fn accept_connection(stream: TcpStream) {
    let addr = stream.peer_addr().expect("connected streams should have a peer address");
    println!("Peer address: {}", addr);


    println!("New WebSocket connection: {}", addr);

    if let Err(e) = handle_connection(addr, stream).await {
        println!("Error handling websocket connection: {}", e);
    }
}

async fn handle_connection(peer: SocketAddr, stream: TcpStream) -> Res<()> {
    let mut ws_stream = tokio_tungstenite::accept_async(stream).await?;
    while let Some(msg) = ws_stream.next().await {
        match msg? {
            Message::Binary(bs) => {
                let msg: SignalMessageToServer = rmp_serde::from_slice(&bs)?;
                println!("Received a message from {}: {:?}", peer, msg);
                // ...
            }
            other => {
                println!("Received a message which is not binary: {:?}", other);
            }
        }
    }
    Ok(())
}
