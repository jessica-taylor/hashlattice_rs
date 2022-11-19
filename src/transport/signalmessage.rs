
use webrtc::ice_transport::ice_candidate::RTCIceCandidateInit;
use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;
use serde::{Serialize, Deserialize};

use crate::crypto::{Hash, PublicKey};

pub type Peer = Hash<PublicKey>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToServer {
    SetPeer(Peer),
    GetPeers(Peer),
    SessionDescription(Peer, RTCSessionDescription),
    IceCandidate(Peer, RTCIceCandidateInit),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SignalMessageToClient {
    Peers(Vec<Peer>),
    SessionDescription(Peer, RTCSessionDescription),
    IceCandidate(Peer, RTCIceCandidateInit),
}
