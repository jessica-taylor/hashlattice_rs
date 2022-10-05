use std::cmp::Ordering;
use std::marker::PhantomData;
use std::collections::BTreeMap;
use std::fmt::Debug;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

pub trait TaggedMapping {
    type Key : Eq + Ord + Clone + Send + Sync + Debug + Serialize + DeserializeOwned;

    type Value : Eq + Clone + Send + Sync + Debug + Serialize + DeserializeOwned;

    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        key1.partial_cmp(key2).ok_or(format!("Cannot compare keys: {:?} and {:?}", key1, key2))
    }

}

#[derive(Debug, Serialize, Deserialize)]
pub struct Tag<M> {
    index: usize,
    phantom: PhantomData<M>
}

impl<M: TaggedMapping> Tag<M> {
    pub fn new(index: usize) -> Self {
        Self {
            index,
            phantom: PhantomData
        }
    }
}

impl<M: TaggedMapping> Clone for Tag<M> {
    fn clone(&self) -> Self {
        Self {
            index: self.index,
            phantom: PhantomData,
        }
    }
}

impl<M: TaggedMapping> Copy for Tag<M> {}

impl<M: TaggedMapping> PartialEq for Tag<M> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<M: TaggedMapping> Eq for Tag<M> {}

impl<M: TaggedMapping> PartialOrd for Tag<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.index.partial_cmp(&other.index)
    }
}

impl<M: TaggedMapping> Ord for Tag<M> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.index.cmp(&other.index)
    }
}

pub struct TagRegistry {
    n_registered: usize
}

impl TagRegistry {
    pub fn register<M: TaggedMapping>(&mut self) -> Tag<M> {
        let index = self.n_registered;
        self.n_registered += 1;
        Tag::new(index)
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct TaggedKey {
    index: usize,
    key: Vec<u8>,
}

impl TaggedKey {
    pub fn new<M: TaggedMapping>(tag: Tag<M>, key: &M::Key) -> Self {
        Self { index: tag.index, key: rmp_serde::to_vec(key).unwrap() }
    }
    pub fn get_index(&self) -> usize {
        self.index
    }
    pub fn get_as<M: TaggedMapping>(&self, tag: Tag<M>) -> Result<M::Key, String> {
        if self.index == tag.index {
            rmp_serde::from_slice(&self.key).map_err(|e| format!("{:?}", e))
        } else {
            Err(format!("Tag mismatch: expected {}, got {}", tag.index, self.index))
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct TaggedValue {
    index: usize,
    value: Vec<u8>,
}

impl TaggedValue {
    pub fn new<M: TaggedMapping>(tag: Tag<M>, value: &M::Value) -> Self {
        Self { index: tag.index, value: rmp_serde::to_vec(value).unwrap() }
    }
    pub fn get_index(&self) -> usize {
        self.index
    }
    pub fn get_as<M: TaggedMapping>(&self, tag: Tag<M>) -> Result<M::Value, String> {
        if self.index == tag.index {
            rmp_serde::from_slice(&self.value).map_err(|e| format!("{:?}", e))
        } else {
            Err(format!("Tag mismatch: expected {}, got {}", tag.index, self.index))
        }
    }
}

// pub enum TaggedLookup<G, T> {
//     Done(Result<T, String>),
//     Lookup(TaggedKey, Box<dyn Send + Sync + FnOnce(&G, TaggedValue) -> TaggedLookup<T>)
// }
// 
// impl<G, T> TaggedLookup<G, T> {
//     fn lookup<M: TaggedMapping>(tag: Tag<M>, key: &M::Key, f: Box<dyn Send + Sync + FnOnce(&G, &M::Value) -> TaggedLookup<G, T>>) -> Self {
//         TaggedLookup::Lookup(TaggedKey::new(tag, key), Box::new(move |graph, value| {
//             let value = value.get_as(tag);
//             f(graph, value)
//         }))
//     }
// }

pub struct TaggedMap {
    map: BTreeMap<TaggedKey, TaggedValue>
}

impl TaggedMap {
    fn new() -> Self {
        Self { map: BTreeMap::new() }
    }
    fn insert<M: TaggedMapping>(&mut self, tag: Tag<M>, key: &M::Key, value: &M::Value) {
        self.map.insert(TaggedKey::new(tag, key), TaggedValue::new(tag, value));
    }
    fn get<M: TaggedMapping>(&self, tag: Tag<M>, key: &M::Key) -> Result<M::Value, String> {
        let tag_value = self.map.get(&TaggedKey::new(tag, key)).ok_or(format!("Key not found: {:?}", key))?;
        tag_value.get_as(tag)
    }
}
