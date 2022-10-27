//! Cryptographic types and operations.

use std::cmp::{Ord, Ordering, PartialOrd};
use std::convert::TryInto;
use std::default::Default;
use std::marker::PhantomData;

use rand::thread_rng;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use rsa::pkcs1v15::{SigningKey, VerifyingKey};
use rsa::pkcs1v15::Signature as RsaSignature;
use rsa::{RsaPrivateKey, RsaPublicKey};
use rsa::PublicKey as RsaPublicKeyTrait;
use signature::{Signer, Verifier, DigestVerifier};
use signature::Signature as SignatureTrait;

/// A SHA256 hash code.
pub type HashCode = [u8; 32];

pub type PublicKey = RsaPublicKey;

pub type Keypair = RsaPrivateKey;

pub type Signature = Vec<u8>;

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

/// An ed25519 signature that is tagged as being the signature of a particular serializable type.
#[derive(Serialize, Deserialize, Debug)]
pub struct Sig<T> {
    /// The signature.
    pub signature: Signature,
    /// The public key.
    pub key: PublicKey,
    /// Phantom data for the type `T`.
    phantom: std::marker::PhantomData<T>,
}

impl<T> Sig<T> {
    // pub fn account(&self) -> Account {
    //     hash(&self.key)
    // }
}

impl<T> Clone for Sig<T> {
    fn clone(&self) -> Self {
        Self {
            signature: self.signature.clone(),
            key: self.key.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T> PartialEq for Sig<T> {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature
    }
}

impl<T> Eq for Sig<T> {}

impl<T> PartialOrd for Sig<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        rmp_serde::to_vec_named(self)
            .unwrap()
            .partial_cmp(&rmp_serde::to_vec_named(other).unwrap())
    }
}

impl<T> Ord for Sig<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        rmp_serde::to_vec_named(self)
            .unwrap()
            .cmp(&rmp_serde::to_vec_named(other).unwrap())
    }
}

/// Generates a ed25519 private key.
pub fn gen_private_key() -> Keypair {
    let mut rng = rand::thread_rng();
    let bits = 2048;
    Keypair::new(&mut rng, bits).expect("failed to generate keypair")
}

/// Signs a serializable with a given ed25519 key.
pub fn sign<T: Serialize>(key: &Keypair, msg: T) -> Sig<T> {
    let sign_key = SigningKey::<Sha256>::new(key.clone());
    let sig = sign_key.sign(&rmp_serde::to_vec_named(&msg).unwrap());
    Sig {
        signature: sig.to_vec(),
        key: key.to_public_key(),
        phantom: std::marker::PhantomData,
    }
}

impl<T: Serialize> Sig<T> {
    /// Verifies that a given signature of a given serializable is valid.
    pub fn verify(&self, msg: &T) -> bool {
        let verify_key: VerifyingKey<_> = VerifyingKey::<Sha256>::new(self.key.clone());
        let sig = RsaSignature::from(self.signature.clone());
        verify_key
            .verify(&rmp_serde::to_vec_named(msg).unwrap(), &sig)
            .is_ok()
    }
}
