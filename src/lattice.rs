use std::collections::{BTreeSet, BTreeMap};
use std::cmp::Ordering;
use std::sync::Arc;
use std::future::Future;

use serde::{Serialize, Deserialize, de::DeserializeOwned};
use async_trait::async_trait;

use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping, Tag, TaggedKey, TaggedValue};

pub trait ImmutComputationContext<CI: TaggedMapping> : Send + Sync {

    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String>;

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


// pub trait LatGraph : Send + Sync + TaggedMapping {
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
//         Ok(LatLookup::Done(()))
//     }
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;
// 
//     fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
//         Ok(LatLookup::Done(LatLookup::Done(value.clone())))
//     }
// }
// 
// pub trait TaggableLatGraph : Send + Sync + TaggedMapping {
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> TagLatLookupResult<()> {
//         Ok(LatLookup::Done(()))
//     }
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> TagLatLookupResult<Self::Value>;
// 
//     fn bottom(&self, key: &Self::Key) -> TagLatLookupResult<Self::Value>;
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value) -> TagLatLookupResult<TagLatLookup<Self::Value>> {
//         Ok(LatLookup::Done(LatLookup::Done(value.clone())))
//     }
// 
// }
// 
// pub struct TaggedLatGraph<G: TaggableLatGraph> {
//     latgraph: G,
//     tag: Tag<G>,
// }
// 
// impl<G: TaggableLatGraph + 'static> TaggedLatGraph<G> {
//     fn new(latgraph: G, tag: Tag<G>) -> Self {
//         TaggedLatGraph { latgraph, tag }
//     }
//     // fn map_lookup<T: 'static>(tag: Tag<G>, lookup: LatLookup<G::Key, G::Value, T>) -> LatLookup<TaggedKey, TaggedValue, T> {
//     //     lookup.map_kv(move |k| TaggedKey::new(tag, &k), move |v: &TaggedValue| v.get_as(tag))
//     // }
// }
// 
// impl<G: TaggableLatGraph> TaggedMapping for TaggedLatGraph<G> {
//     type Key = TaggedKey;
//     type Value = TaggedValue;
// 
//     fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
//         self.latgraph.cmp_keys(&key1.get_as(self.tag)?, &key2.get_as(self.tag)?)
//     }
// }
// 
// impl<G: TaggableLatGraph + 'static> LatGraph for TaggedLatGraph<G> {
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
//         self.latgraph.check_elem(&key.get_as(self.tag)?, &value.get_as(self.tag)?)
//     }
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
//         let tag = self.tag;
//         Ok(self.latgraph.join(&key.get_as(tag)?, &value1.get_as(tag)?, &value2.get_as(tag)?)?.map(move |v| {
//             TaggedValue::new(tag, &v)
//         }))
//     }
// 
//     fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
//         let tag = self.tag;
//         Ok(self.latgraph.bottom(&key.get_as(tag)?)?.map(move |v| {
//             TaggedValue::new(tag, &v)
//         }))
//     }
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
//         let tag = self.tag;
//         Ok(self.latgraph.transport(&key.get_as(tag)?, &value.get_as(tag)?)?.map(move |lookup| {
//             lookup.map(move |v| TaggedValue::new(tag, &v))
//         }))
//     }
// }
// 
// pub struct MultiLatGraph {
//     latgraphs: Vec<Box<dyn LatGraph<Key = TaggedKey, Value = TaggedValue>>>,
// }
// 
// impl MultiLatGraph {
//     pub fn new() -> Self {
//         Self { latgraphs: Vec::new() }
//     }
//     pub fn register<G: TaggableLatGraph + 'static>(&mut self, latgraph: G) -> Tag<G> {
//         let tag = Tag::new(self.latgraphs.len());
//         self.latgraphs.push(Box::new(TaggedLatGraph::new(latgraph, tag)));
//         tag
//     }
//     fn get_latgraph(&self, ix: usize) -> Result<&dyn LatGraph<Key = TaggedKey, Value = TaggedValue>, String> {
//         self.latgraphs.get(ix).map(|g| g.as_ref()).ok_or(format!("No latgraph with tag {}", ix))
//     }
// }
// 
// impl TaggedMapping for MultiLatGraph {
//     type Key = TaggedKey;
//     type Value = TaggedValue;
// 
//     fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
//         let ix_cmp = key1.get_index().cmp(&key2.get_index());
//         if ix_cmp != Ordering::Equal {
//             return Ok(ix_cmp);
//         }
//         self.get_latgraph(key1.get_index())?.cmp_keys(key1, key2)
//     }
// }
// 
// impl LatGraph for MultiLatGraph {
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
//         self.get_latgraph(key.get_index())?.check_elem(key, value)
//     }
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
//         self.get_latgraph(key.get_index())?.join(key, value1, value2)
//     }
// 
//     fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
//         self.get_latgraph(key.get_index())?.bottom(key)
//     }
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
//         self.get_latgraph(key.get_index())?.transport(key, value)
//     }
// }
// 
