
use futures::StreamExt;
use tungstenite::protocol::Message;
use tokio_tungstenite::connect_async;

use crate::error::Res;
use crate::transport::signalmessage::SignalMessageToClient;


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
