
use serde::{Serialize, Deserialize};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToServer {
    GetPeers,
    Send(String, Vec<u8>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToClient {
    Peers(Vec<String>),
    Received(String, Vec<u8>),
}
