use std::sync::{Arc, Mutex};
use std::rc::Rc;
use core::cmp::Ordering;
use std::sync::mpsc::{Sender, Receiver, TryRecvError};

use async_trait::async_trait;
use anyhow::bail;
use serde::{Serialize, Deserialize};
use deno_core::error::AnyError;
use deno_core::{JsRuntime, Extension, RuntimeOptions, op, OpState, Resource};
use deno_core::serde_json::{Value as SerdeJsValue, to_string as json_to_string};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode, hash};
use crate::lattice::{HashLookup, ComputationImmutContext, ComputationMutContext, ComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext, LatMerkleNode};
use crate::js::runtime_channel::{RuntimeState, LibraryQuery, LibraryResult, CtxQuery, CtxResult, MessageToRuntime, MessageFromRuntime};

#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct JsValue(SerdeJsValue);

impl PartialOrd for JsValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(json_to_string(&self.0).unwrap().cmp(&json_to_string(&other.0).unwrap()))
    }
}

impl Ord for JsValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}


pub struct JsMapping;

impl TaggedMapping for JsMapping {
    type Key = JsValue;
    type Value = JsValue;
}

enum DynContext {
    ComputationImmut(Arc<dyn ComputationImmutContext<JsMapping>>),
    LatticeImmut(Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>),
    LatticeMut(Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>),
}

#[async_trait]
impl HashLookup for DynContext {
    async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
         match self {
             DynContext::ComputationImmut(ctx) => ctx.hash_lookup(hash).await,
             DynContext::LatticeImmut(ctx) => ctx.hash_lookup(hash).await,
             DynContext::LatticeMut(ctx) => ctx.hash_lookup(hash).await,
         }
     }
}

#[async_trait]
impl ComputationImmutContext<JsMapping> for DynContext {
     async fn eval_computation(&self, key: &JsValue) -> Res<JsValue> {
         match self {
             DynContext::ComputationImmut(ctx) => ctx.eval_computation(key).await,
             DynContext::LatticeImmut(ctx) => ctx.eval_computation(key).await,
             DynContext::LatticeMut(ctx) => ctx.eval_computation(key).await,
         }
     }
}

#[async_trait]
impl ComputationMutContext<JsMapping> for DynContext {
     async fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
         match self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot hash_put in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => bail!("Cannot hash_put in LatticeImmutContext"),
             DynContext::LatticeMut(ctx) => ctx.hash_put(value).await,
         }
     }
}


#[async_trait]
impl LatticeImmutContext<JsMapping, JsMapping, JsMapping> for DynContext {
     async fn lattice_lookup(&self, key: &JsValue) -> Res<Option<Hash<LatMerkleNode<JsValue, JsValue, JsValue, JsValue, JsValue>>>> {
         match self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot lattice_lookup in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => ctx.lattice_lookup(key).await,
             DynContext::LatticeMut(ctx) => ctx.lattice_lookup(key).await,
         }
     }
 
     async fn eval_lat_computation(&self, key: &JsValue) -> Res<Hash<LatMerkleNode<JsValue, JsValue, JsValue, JsValue, JsValue>>> {
         match self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot eval_lat_computation in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => ctx.eval_lat_computation(key).await,
             DynContext::LatticeMut(ctx) => ctx.eval_lat_computation(key).await,
         }
     }
}


pub struct JsLibrary {
    sender: Sender<MessageToRuntime>,
    receiver: Receiver<MessageFromRuntime>,
}
