use std::collections::{BTreeSet, BTreeMap};
use std::cmp::Ordering;
use std::sync::Arc;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

use crate::tagged_mapping::{TaggedMapping, Tag, TaggedKey, TaggedValue};

pub enum LatLookup<K, V, T> {
    Done(Result<T, String>),
    Lookup(K, Box<dyn Send + Sync + FnOnce(V) -> LatLookup<K, V, T>>)
}

impl<K: Ord + 'static, V: 'static, T : 'static> LatLookup<K, V, T> {
    fn to_set(self, mut lookup: impl FnMut(K) -> Result<V, String>) -> Result<(BTreeSet<K>, T), String> {
        let mut this = self;
        let set = BTreeSet::new();
        loop {
            match this {
                LatLookup::Done(Err(e)) => { return Err(e); },
                LatLookup::Done(Ok(res)) => { return Ok((set, res)); },
                LatLookup::Lookup(k, f) => {
                    let v = lookup(k)?;
                    this = f(v);
                }
            }
        }
    }
    fn and_then<T2>(self, f: impl 'static + Send + Sync + FnOnce(T) -> LatLookup<K, V, T2>) -> LatLookup<K, V, T2> {
        match self {
            LatLookup::Done(Err(e)) => { LatLookup::Done(Err(e)) },
            LatLookup::Done(Ok(res)) => { f(res) },
            LatLookup::Lookup(k, g) => {
                LatLookup::Lookup(k, Box::new(move |v| g(v).and_then(f)))
            }
        }
    }
    fn map<T2>(self, f: impl 'static + Send + Sync + FnOnce(T) -> T2) -> LatLookup<K, V, T2> {
        self.and_then(move |res| LatLookup::Done(Ok(f(res))))
    }
    fn map_latgraph<K2: Ord + 'static, V2: 'static>(self, conv_k: impl 'static + Send + Sync + Fn(K) -> K2, conv_v: impl 'static + Send + Sync + Fn(V2) -> Result<V, String>) -> LatLookup<K2, V2, T> {
        match self {
            LatLookup::Done(res) => LatLookup::Done(res),
            LatLookup::Lookup(k, f) => LatLookup::Lookup(conv_k(k), Box::new(move |v| {
                match conv_v(v) {
                    Err(e) => LatLookup::Done(Err(e)),
                    Ok(v) => f(v).map_latgraph(conv_k, conv_v)
                }
            }))
        }
    }
}

pub trait LatGraph : Send + Sync + TaggedMapping {

    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        key1.partial_cmp(key2).ok_or("Keys are not comparable".to_string())
    }

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, ()> {
        LatLookup::Done(Ok(()))
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookup<Self::Key, Self::Value, Self::Value>;

    fn bottom(&self, key: &Self::Key) -> LatLookup<Self::Key, Self::Value, Self::Value>;

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        LatLookup::Done(Ok(LatLookup::Done(Ok(value.clone()))))
    }
}

pub struct TaggedLatGraph<G: LatGraph> {
    latgraph: G,
    tag: Tag<G>,
}

impl<G: LatGraph + 'static> TaggedLatGraph<G> {
    fn new(latgraph: G, tag: Tag<G>) -> Self {
        TaggedLatGraph { latgraph, tag }
    }
    fn map_lookup<T: 'static>(tag: Tag<G>, lookup: LatLookup<G::Key, G::Value, T>) -> LatLookup<TaggedKey, TaggedValue, T> {
        lookup.map_latgraph(move |k| TaggedKey::new(tag, &k), move |v: TaggedValue| v.get_as(tag))
    }
}

impl<G: LatGraph> TaggedMapping for TaggedLatGraph<G> {
    type Key = TaggedKey;
    type Value = TaggedValue;
}

impl<G: LatGraph + 'static> LatGraph for TaggedLatGraph<G> {
    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        match key1.get_as(self.tag) {
            Err(e) => Err(e),
            Ok(k1) => match key2.get_as(self.tag) {
                Err(e) => Err(e),
                Ok(k2) => self.latgraph.cmp_keys(&k1, &k2)
            }
        }
    }

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, ()> {
        match key.get_as(self.tag) {
            Err(e) => LatLookup::Done(Err(e)),
            Ok(k) => match value.get_as(self.tag) {
                Err(e) => LatLookup::Done(Err(e)),
                Ok(v) => Self::map_lookup(self.tag, self.latgraph.check_elem(&k, &v))
            }
        }
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookup<Self::Key, Self::Value, Self::Value> {
        let tag = self.tag;
        match key.get_as(tag) {
            Err(e) => LatLookup::Done(Err(e)),
            Ok(k) => match value1.get_as(tag) {
                Err(e) => LatLookup::Done(Err(e)),
                Ok(v1) => match value2.get_as(tag) {
                    Err(e) => LatLookup::Done(Err(e)),
                    Ok(v2) => Self::map_lookup(tag, self.latgraph.join(&k, &v1, &v2)).map(move |v| TaggedValue::new(tag, &v))
                }
            }
        }
    }

    fn bottom(&self, key: &Self::Key) -> LatLookup<Self::Key, Self::Value, Self::Value> {
        let tag = self.tag;
        match key.get_as(tag) {
            Err(e) => LatLookup::Done(Err(e)),
            Ok(k) => Self::map_lookup(tag, self.latgraph.bottom(&k)).map(move |v| TaggedValue::new(tag, &v))
        }
    }

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        let tag = self.tag;
        match key.get_as(tag) {
            Err(e) => LatLookup::Done(Err(e)),
            Ok(k) => match value.get_as(tag) {
                Err(e) => LatLookup::Done(Err(e)),
                Ok(v) => Self::map_lookup(tag, self.latgraph.transport(&k, &v)).map(move |lookup| Self::map_lookup(tag, lookup).map(move |v| TaggedValue::new(tag, &v)))
            }
        }
    }
}

pub struct MultiLatGraph {
    latgraphs: Vec<Box<dyn LatGraph<Key = TaggedKey, Value = TaggedValue>>>,
}

impl MultiLatGraph {
    pub fn new() -> Self {
        Self { latgraphs: Vec::new() }
    }
    pub fn register<G: LatGraph + 'static>(&mut self, latgraph: G) -> Tag<G> {
        let tag = Tag::new(self.latgraphs.len());
        self.latgraphs.push(Box::new(TaggedLatGraph::new(latgraph, tag)));
        tag
    }
    fn get_latgraph(&self, ix: usize) -> Result<&dyn LatGraph<Key = TaggedKey, Value = TaggedValue>, String> {
        self.latgraphs.get(ix).map(|g| g.as_ref()).ok_or(format!("No latgraph with tag {}", ix))
    }
    fn with_latgraph<T>(&self, ix: usize, then: impl FnOnce(&dyn LatGraph<Key = TaggedKey, Value = TaggedValue>) -> LatLookup<TaggedKey, TaggedValue, T>) -> LatLookup<TaggedKey, TaggedValue, T> {
        match self.get_latgraph(ix) {
            Err(e) => LatLookup::Done(Err(e)),
            Ok(latgraph) => then(latgraph)
        }
    }
}

impl TaggedMapping for MultiLatGraph {
    type Key = TaggedKey;
    type Value = TaggedValue;
}

impl LatGraph for MultiLatGraph {
    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        let ix_cmp = key1.get_index().cmp(&key2.get_index());
        if ix_cmp != Ordering::Equal {
            return Ok(ix_cmp);
        }
        self.get_latgraph(key1.get_index())?.cmp_keys(key1, key2)
    }

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, ()> {
        self.with_latgraph(key.get_index(), |g| g.check_elem(key, value))
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookup<Self::Key, Self::Value, Self::Value> {
        self.with_latgraph(key.get_index(), |g| g.join(key, value1, value2))
    }

    fn bottom(&self, key: &Self::Key) -> LatLookup<Self::Key, Self::Value, Self::Value> {
        self.with_latgraph(key.get_index(), |g| g.bottom(key))
    }

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookup<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        self.with_latgraph(key.get_index(), |g| g.transport(key, value))
    }
}

