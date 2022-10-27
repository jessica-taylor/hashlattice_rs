
use serde::{Serialize, Deserialize};

use crate::crypto::{Hash, PublicKey};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToServer {
    GetPeers,
    Send(Hash<PublicKey>, Vec<u8>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToClient {
    Peers(Vec<Hash<PublicKey>>),
    Received(Hash<PublicKey>, Vec<u8>),
}
