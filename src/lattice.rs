

use crate::error::{str_error, Res};
use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping};

pub trait HashLookup : Send + Sync {

    fn hash_lookup(&mut self, hash: HashCode) -> Res<Vec<u8>>;
}

pub struct EmptyHashLookup;

impl HashLookup for EmptyHashLookup {
    fn hash_lookup(&mut self, hash: HashCode) -> Res<Vec<u8>> {
        str_error(&format!("EmptyHashLookup: no hash lookup for {:?}", hash))
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

pub struct EmptyComputationLibrary;

impl<CI: TaggedMapping> ComputationLibrary<CI> for EmptyComputationLibrary {
    fn eval_immut(&self, key: &CI::Key, ctx: &mut dyn ImmutComputationContext<CI>) -> Res<CI::Value> {
        str_error(&format!("EmptyComputationLibrary: no computation for {:?}", key))
    }
}

pub trait LatticeLibrary<CI: TaggedMapping, L: TaggedMapping> : Send + Sync {

    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &mut dyn ImmutComputationContext<CI>) -> Res<()>;

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &mut dyn MutComputationContext<CI>) -> Res<L::Value>;
}

pub struct EmptyLatticeLibrary;

impl<CI: TaggedMapping, L: TaggedMapping> LatticeLibrary<CI, L> for EmptyLatticeLibrary {
    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &mut dyn ImmutComputationContext<CI>) -> Res<()> {
        str_error(&format!("EmptyLatticeLibrary: no check_elem for {:?} {:?}", key, value))
    }

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &mut dyn MutComputationContext<CI>) -> Res<L::Value> {
        str_error(&format!("EmptyLatticeLibrary: no join for {:?} {:?} {:?}", key, a, b))
    }
}

pub trait LatticeContext<CI: TaggedMapping, L: TaggedMapping> : MutComputationContext<CI> {

    fn get_lattice(&self, key: &L::Key) -> Option<L::Value>;

    fn join_lattice(&mut self, key: &L::Key, value: L::Value) -> Res<L::Value>;
}

