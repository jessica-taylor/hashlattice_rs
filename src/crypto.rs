//! Cryptographic types and operations.

use std::cmp::{Ord, Ordering, PartialOrd};
use std::convert::TryInto;
use std::default::Default;
use std::marker::PhantomData;

// use ed25519_dalek::{Signer, Verifier};
use rand::prelude::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/* QUESTION: tell me more about how much of this is table stakes
for a generic implementation, how much of it is reusable with
cosmos, and how much of it is somewhere in between? */

/// A SHA256 hash code.
pub type HashCode = [u8; 32];

// pub type PublicKey = ed25519_dalek::PublicKey;
// 
// pub type Keypair = ed25519_dalek::Keypair;
// 
// pub type Signature = ed25519_dalek::Signature;

/// A hash code that is tagged as being a hash code of a particular serializable type.
#[derive(Serialize, Deserialize, Debug)]
pub struct Hash<T> {
    /// The hash code.
    pub code: HashCode,
    /// Phantom data for the type `T`.
    pub(crate) phantom: std::marker::PhantomData<fn() -> T>,
}

impl<T> Default for Hash<T> {
    fn default() -> Self {
        Self {
            code: HashCode::default(),
            phantom: PhantomData,
        }
    }
}

impl<T> Clone for Hash<T> {
    fn clone(&self) -> Self {
        Self {
            code: self.code,
            phantom: PhantomData,
        }
    }
}

impl<T> Copy for Hash<T> {}

impl<T> PartialEq for Hash<T> {
    fn eq(&self, other: &Self) -> bool {
        self.code == other.code
    }
}

impl<T> Eq for Hash<T> {}

impl<T> PartialOrd for Hash<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.code.partial_cmp(&other.code)
    }
}

impl<T> Ord for Hash<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.code.cmp(&other.code)
    }
}

impl<T> Hash<T> {
    pub fn to_hex(&self) -> String {
        hex::encode(self.code)
    }
    pub fn from_hex(hexrep: &str) -> Result<Self, hex::FromHexError> {
        let code_bs: Vec<u8> = hex::decode(hexrep)?;
        let code: HashCode = code_bs
            .try_into()
            .map_err(|_| hex::FromHexError::InvalidStringLength)?;
        Ok(Self {
            code,
            phantom: PhantomData,
        })
    }
    pub fn as_bytes(&self) -> &[u8] {
        &self.code
    }
    pub fn from_bytes(bs: &[u8]) -> Result<Self, String> {
        let code: HashCode = bs
            .try_into()
            .map_err(|_| "bad hash bytes length".to_string())?;
        Ok(Self {
            code,
            phantom: PhantomData,
        })
    }
}

/// Gets the SHA256 hash code of a byte array. Note that this is the hash function used by Cosmos.
pub fn hash_of_bytes(bs: &[u8]) -> HashCode {
    let mut hasher = Sha256::new();
    hasher.update(bs);
    hasher
        .finalize()
        .try_into()
        .expect("slice with incorrect length")
}

/// Gets the hash of a serialiable data.
pub fn hash<T: Serialize>(v: &T) -> Hash<T> {
    Hash {
        code: hash_of_bytes(rmp_serde::to_vec_named(v).unwrap().as_slice()),
        phantom: std::marker::PhantomData,
    }
}

// /// An ed25519 signature that is tagged as being the signature of a particular serializable type.
// #[derive(Serialize, Deserialize, Debug)]
// pub struct Sig<T> {
//     /// The signature.
//     pub signature: Signature,
//     /// The public key.
//     pub key: PublicKey,
//     /// Phantom data for the type `T`.
//     phantom: std::marker::PhantomData<T>,
// }
// 
// impl<T> Sig<T> {
//     pub fn account(&self) -> Account {
//         hash(&self.key)
//     }
// }
// 
// impl<T> Clone for Sig<T> {
//     fn clone(&self) -> Self {
//         Self {
//             signature: self.signature,
//             key: self.key,
//             phantom: PhantomData,
//         }
//     }
// }
// 
// impl<T> Copy for Sig<T> {}
// 
// impl<T> PartialEq for Sig<T> {
//     fn eq(&self, other: &Self) -> bool {
//         self.signature == other.signature
//     }
// }
// 
// impl<T> Eq for Sig<T> {}
// 
// impl<T> PartialOrd for Sig<T> {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         rmp_serde::to_vec_named(self)
//             .unwrap()
//             .partial_cmp(&rmp_serde::to_vec_named(other).unwrap())
//     }
// }
// 
// impl<T> Ord for Sig<T> {
//     fn cmp(&self, other: &Self) -> Ordering {
//         rmp_serde::to_vec_named(self)
//             .unwrap()
//             .cmp(&rmp_serde::to_vec_named(other).unwrap())
//     }
// }
// 
// /// Generates a ed25519 private key.
// pub fn gen_private_key() -> Keypair {
//     Keypair::generate(&mut thread_rng())
// }
// 
// /// Signs a serializable with a given ed25519 key.
// pub fn sign<T: Serialize>(key: &Keypair, msg: T) -> Sig<T> {
//     Sig {
//         signature: key.sign(&rmp_serde::to_vec_named(&msg).unwrap()),
//         key: key.public,
//         phantom: std::marker::PhantomData,
//     }
// }
// 
// impl<T: Serialize> Sig<T> {
//     /// Verifies that a given signature of a given serializable is valid.
//     pub fn verify(&self, msg: &T) -> bool {
//         self.key
//             .verify(&rmp_serde::to_vec_named(msg).unwrap(), &self.signature)
//             .is_ok()
//     }
// }
