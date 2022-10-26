use std::collections::{BTreeSet, BTreeMap};
use std::cmp::Ordering;
use std::sync::Arc;
use std::future::Future;

use serde::{Serialize, Deserialize, de::DeserializeOwned};
use async_trait::async_trait;

use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping, Tag, TaggedKey, TaggedValue};

pub trait HashLookup : Send + Sync {

    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String>;
}

pub struct NullHashLookup;

impl HashLookup for NullHashLookup {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        Err(format!("NullHashLookup: no hash lookup for {:?}", hash))
    }
}

pub trait ImmutComputationContext<CI: TaggedMapping> : HashLookup {

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String>;
}

pub trait MutComputationContext<CI: TaggedMapping> : ImmutComputationContext<CI> {

    fn hash_put(&mut self, value: Vec<u8>) -> Result<HashCode, String>;

}

pub trait ComputationLibrary<CI: TaggedMapping> : Send + Sync {

    fn eval_immut(&self, key: &CI::Key, ctx: &mut dyn ImmutComputationContext<CI>) -> Result<CI::Value, String>;
}

pub trait LatticeLibrary<CI: TaggedMapping, L: TaggedMapping> : Send + Sync {

    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &mut dyn ImmutComputationContext<CI>) -> Result<(), String>;

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &mut dyn MutComputationContext<CI>) -> Result<L::Value, String>;
}

pub trait LatticeContext<CI: TaggedMapping, L: TaggedMapping> : MutComputationContext<CI> {

    fn get_lattice(&self, key: &L::Key) -> Option<L::Value>;

    fn join_lattice(&mut self, key: &L::Key, value: L::Value) -> Result<L::Value, String>;
}

