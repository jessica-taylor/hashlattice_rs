use std::collections::{BTreeSet, BTreeMap};
use std::cmp::Ordering;
use std::sync::Arc;
use std::future::Future;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

use crate::tagged_mapping::{TaggedMapping, Tag, TaggedKey, TaggedValue};

pub enum LatLookup<K, V, T> {
    Done(T),
    Lookup(K, Box<dyn Send + Sync + FnOnce(&V) -> LatLookupResult<K, V, T>>)
}

type LatLookupResult<K, V, T> = Result<LatLookup<K, V, T>, String>;

impl<K: Ord + 'static, V: 'static, T : 'static> LatLookup<K, V, T> {
    pub fn evaluate(self, mut lookup: impl FnMut(&K) -> Result<V, String>) -> Result<(BTreeMap<K, V>, T), String> {
        let mut this = self;
        let mut map = BTreeMap::new();
        loop {
            match this {
                LatLookup::Done(res) => { return Ok((map, res)); },
                LatLookup::Lookup(k, f) => {
                    let v = lookup(&k)?;
                    this = f(&v)?;
                    map.insert(k, v);
                }
            }
        }
    }
    pub async fn evaluate_async<F: Future<Output = Result<V, String>>>(self, mut lookup: impl Send + Sync + FnMut(&K) -> F) -> Result<(BTreeMap<K, V>, T), String> {
        let mut this = self;
        let mut map = BTreeMap::new();
        loop {
            match this {
                LatLookup::Done(res) => { return Ok((map, res)); },
                LatLookup::Lookup(k, f) => {
                    let v = lookup(&k).await?;
                    this = f(&v)?;
                    map.insert(k, v);
                }
            }
        }
    }
    pub fn and_then<T2>(self, f: impl 'static + Send + Sync + FnOnce(T) -> LatLookupResult<K, V, T2>) -> LatLookupResult<K, V, T2> {
        match self {
            LatLookup::Done(res) => { f(res) },
            LatLookup::Lookup(k, g) => {
                Ok(LatLookup::Lookup(k, Box::new(move |v| g(v)?.and_then(f))))
            }
        }
    }
    pub fn map<T2>(self, f: impl 'static + Send + Sync + FnOnce(T) -> T2) -> LatLookup<K, V, T2> {
        match self {
            LatLookup::Done(res) => { LatLookup::Done(f(res)) },
            LatLookup::Lookup(k, g) => {
                LatLookup::Lookup(k, Box::new(move |v| g(v).map(|x| x.map(f))))
            }
        }
    }
    pub fn map_kv<K2: Ord + 'static, V2: 'static>(self, conv_k: impl 'static + Send + Sync + Fn(&K) -> K2, conv_v: impl 'static + Send + Sync + Fn(&V2) -> Result<V, String>) -> LatLookup<K2, V2, T> {
        match self {
            LatLookup::Done(res) => LatLookup::Done(res),
            LatLookup::Lookup(k, f) => LatLookup::Lookup(conv_k(&k), Box::new(move |v| {
                Ok(f(&conv_v(v)?)?.map_kv(conv_k, conv_v))
            }))
        }
    }
}

type TagLatLookup<T> = LatLookup<TaggedKey, TaggedValue, T>;
type TagLatLookupResult<T> = LatLookupResult<TaggedKey, TaggedValue, T>;

impl<T> TagLatLookup<T> {
    pub fn lookup<M: TaggedMapping + Send + Sync + 'static>(tag: Tag<M>, key: &M::Key, cont: impl 'static + Send + Sync + FnOnce(&M::Value) -> TagLatLookupResult<T>) -> TagLatLookup<T> {
        LatLookup::Lookup(TaggedKey::new(tag, key), Box::new(move |v| cont(&v.get_as(tag)?)))
    }

}

pub trait LatGraph : Send + Sync + TaggedMapping {

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
        Ok(LatLookup::Done(()))
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;

    fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        Ok(LatLookup::Done(LatLookup::Done(value.clone())))
    }
}

pub trait TaggableLatGraph : Send + Sync + TaggedMapping {
    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> TagLatLookupResult<()> {
        Ok(LatLookup::Done(()))
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> TagLatLookupResult<Self::Value>;

    fn bottom(&self, key: &Self::Key) -> TagLatLookupResult<Self::Value>;

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> TagLatLookupResult<TagLatLookup<Self::Value>> {
        Ok(LatLookup::Done(LatLookup::Done(value.clone())))
    }

}

pub struct TaggedLatGraph<G: TaggableLatGraph> {
    latgraph: G,
    tag: Tag<G>,
}

impl<G: TaggableLatGraph + 'static> TaggedLatGraph<G> {
    fn new(latgraph: G, tag: Tag<G>) -> Self {
        TaggedLatGraph { latgraph, tag }
    }
    // fn map_lookup<T: 'static>(tag: Tag<G>, lookup: LatLookup<G::Key, G::Value, T>) -> LatLookup<TaggedKey, TaggedValue, T> {
    //     lookup.map_kv(move |k| TaggedKey::new(tag, &k), move |v: &TaggedValue| v.get_as(tag))
    // }
}

impl<G: TaggableLatGraph> TaggedMapping for TaggedLatGraph<G> {
    type Key = TaggedKey;
    type Value = TaggedValue;

    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        self.latgraph.cmp_keys(&key1.get_as(self.tag)?, &key2.get_as(self.tag)?)
    }
}

impl<G: TaggableLatGraph + 'static> LatGraph for TaggedLatGraph<G> {

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
        self.latgraph.check_elem(&key.get_as(self.tag)?, &value.get_as(self.tag)?)
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
        let tag = self.tag;
        Ok(self.latgraph.join(&key.get_as(tag)?, &value1.get_as(tag)?, &value2.get_as(tag)?)?.map(move |v| {
            TaggedValue::new(tag, &v)
        }))
    }

    fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
        let tag = self.tag;
        Ok(self.latgraph.bottom(&key.get_as(tag)?)?.map(move |v| {
            TaggedValue::new(tag, &v)
        }))
    }

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        let tag = self.tag;
        Ok(self.latgraph.transport(&key.get_as(tag)?, &value.get_as(tag)?)?.map(move |lookup| {
            lookup.map(move |v| TaggedValue::new(tag, &v))
        }))
    }
}

pub struct MultiLatGraph {
    latgraphs: Vec<Box<dyn LatGraph<Key = TaggedKey, Value = TaggedValue>>>,
}

impl MultiLatGraph {
    pub fn new() -> Self {
        Self { latgraphs: Vec::new() }
    }
    pub fn register<G: TaggableLatGraph + 'static>(&mut self, latgraph: G) -> Tag<G> {
        let tag = Tag::new(self.latgraphs.len());
        self.latgraphs.push(Box::new(TaggedLatGraph::new(latgraph, tag)));
        tag
    }
    fn get_latgraph(&self, ix: usize) -> Result<&dyn LatGraph<Key = TaggedKey, Value = TaggedValue>, String> {
        self.latgraphs.get(ix).map(|g| g.as_ref()).ok_or(format!("No latgraph with tag {}", ix))
    }
}

impl TaggedMapping for MultiLatGraph {
    type Key = TaggedKey;
    type Value = TaggedValue;

    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        let ix_cmp = key1.get_index().cmp(&key2.get_index());
        if ix_cmp != Ordering::Equal {
            return Ok(ix_cmp);
        }
        self.get_latgraph(key1.get_index())?.cmp_keys(key1, key2)
    }
}

impl LatGraph for MultiLatGraph {

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, ()> {
        self.get_latgraph(key.get_index())?.check_elem(key, value)
    }

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
        self.get_latgraph(key.get_index())?.join(key, value1, value2)
    }

    fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value> {
        self.get_latgraph(key.get_index())?.bottom(key)
    }

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
        self.get_latgraph(key.get_index())?.transport(key, value)
    }
}

