use std::net::SocketAddr;

use futures::{future, StreamExt, TryStreamExt};

use tokio::net::{TcpListener, TcpStream};
use tungstenite::protocol::Message;
use tokio_tungstenite::WebSocketStream;

// https://github.com/snapview/tokio-tungstenite/blob/master/examples/autobahn-server.rs

async fn runserver() -> Result<(), String> {
    // let addr = env::args().nth(1).unwrap_or_else(|| "127.0.0.1:8080".to_string());
    let addr = "127.0.0.1:2020";

    // Create the event loop and TCP listener we'll accept connections on.
    let listener = TcpListener::bind(&addr).await.map_err(|e| e.to_string())?;
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

async fn handle_connection(peer: SocketAddr, stream: TcpStream) -> Result<(), String> {
    let mut ws_stream = tokio_tungstenite::accept_async(stream)
        .await
        .expect("Error during the websocket handshake occurred");
    while let Some(msg) = ws_stream.next().await {
        let msg = msg.map_err(|e| e.to_string())?;
        match msg {
            Message::Binary(bs) => {
                println!("Received a message from {}: {:?}", peer, bs);
                // ...
            }
            other => {
                println!("Received a message which is not binary: {:?}", other);
            }
        }
    }
    Ok(())
}
