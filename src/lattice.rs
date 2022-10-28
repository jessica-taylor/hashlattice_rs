

use crate::error::{str_error, Res};
use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping};

pub trait HashLookup : Send + Sync {

    fn hash_lookup(&mut self, hash: HashCode) -> Res<Vec<u8>>;
}

pub struct NullHashLookup;

impl HashLookup for NullHashLookup {
    fn hash_lookup(&mut self, hash: HashCode) -> Res<Vec<u8>> {
        str_error(&format!("NullHashLookup: no hash lookup for {:?}", hash))
    }
}

pub trait ImmutComputationContext<CI: TaggedMapping> : HashLookup {

    fn eval_immut(&mut self, key: &CI::Key) -> Res<CI::Value>;
}

pub trait MutComputationContext<CI: TaggedMapping> : ImmutComputationContext<CI> {

    fn hash_put(&mut self, value: Vec<u8>) -> Res<HashCode>;

}

pub trait ComputationLibrary<CI: TaggedMapping> : Send + Sync {

    fn eval_immut(&self, key: &CI::Key, ctx: &mut dyn ImmutComputationContext<CI>) -> Res<CI::Value>;
}

pub trait LatticeLibrary<CI: TaggedMapping, L: TaggedMapping> : Send + Sync {

    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &mut dyn ImmutComputationContext<CI>) -> Res<()>;

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &mut dyn MutComputationContext<CI>) -> Res<L::Value>;
}

pub trait LatticeContext<CI: TaggedMapping, L: TaggedMapping> : MutComputationContext<CI> {

    fn get_lattice(&self, key: &L::Key) -> Option<L::Value>;

    fn join_lattice(&mut self, key: &L::Key, value: L::Value) -> Res<L::Value>;
}

