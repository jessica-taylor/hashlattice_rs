use std::sync::Arc;

use webrtc::api::APIBuilder;
use webrtc::data_channel::data_channel_message::DataChannelMessage;
use webrtc::peer_connection::configuration::RTCConfiguration;
use webrtc::ice_transport::ice_server::RTCIceServer;
use webrtc::peer_connection::peer_connection_state::RTCPeerConnectionState;

use crate::error::Res;

// https://github.com/webrtc-rs/webrtc/blob/master/examples/examples/data-channels-create/data-channels-create.rs

async fn test() -> Res<()> {
    let api = APIBuilder::new().build();

    let config = RTCConfiguration {
        ice_servers: vec![RTCIceServer {
            urls: vec!["stun:stun.l.google.com:19302".to_string()],
            ..Default::default()
        }],
        ..Default::default()
    };
    let peer_connection = api.new_peer_connection(config).await?;

    let data_channel = peer_connection.create_data_channel("data", None).await?;

    peer_connection
        .on_peer_connection_state_change(Box::new(move |s: RTCPeerConnectionState| {
            println!("Peer Connection State has changed: {}", s);

            if s == RTCPeerConnectionState::Failed {
                panic!("Peer Connection has gone to failed exiting");
            }

            Box::pin(async {})
        }))
        .await;

    let d1 = Arc::clone(&data_channel);

    data_channel.on_open(Box::new(move || {
        println!("Data channel '{}':'{}' open.", d1.label(), d1.id());

        // let d2 = Arc::clone(&d1);
        Box::pin(async move {
            // let mut result = Result::<usize>::Ok(0);
            // while result.is_ok() {
            //     let timeout = tokio::time::sleep(Duration::from_secs(5));
            //     tokio::pin!(timeout);

            //     tokio::select! {
            //         _ = timeout.as_mut() =>{
            //             let message = math_rand_alpha(15);
            //             println!("Sending '{}'", message);
            //             result = d2.send_text(message).await.map_err(Into::into);
            //         }
            //     };
            // }
        })
    })).await;

    // Register text message handling
    let d_label = data_channel.label().to_owned();
    data_channel
        .on_message(Box::new(move |msg: DataChannelMessage| {
            let msg_str = String::from_utf8(msg.data.to_vec()).unwrap();
            println!("Message from DataChannel '{}': '{}'", d_label, msg_str);
            Box::pin(async {})
        }))
        .await;

    // Create an offer to send to the browser
    let offer = peer_connection.create_offer(None).await?;

    // Create channel that is blocked until ICE Gathering is complete
    let mut gather_complete = peer_connection.gathering_complete_promise().await;

    // Sets the LocalDescription, and starts our UDP listeners
    peer_connection.set_local_description(offer).await?;

    Ok(())
}
