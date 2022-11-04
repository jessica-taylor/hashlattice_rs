use core::cmp::Ordering;
use std::sync::{Arc, Mutex};
use std::rc::Rc;
use std::sync::mpsc::{Sender, Receiver, channel, TryRecvError};
use std::collections::BTreeMap;
use std::thread::{spawn, JoinHandle};

use futures::executor::block_on;
use async_trait::async_trait;
use anyhow::bail;
use serde::{Serialize, Deserialize};
use deno_core::error::AnyError;
use deno_core::{JsRuntime, Extension, RuntimeOptions, op, OpState, Resource};
use deno_core::serde_json::{Value as SerdeJsValue, to_string as json_to_string};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode, hash};
use crate::lattice::{HashLookup, ComputationImmutContext, HashPut, ComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext, LatMerkleNode};
use crate::js::runtime_channel::{RuntimeState, CtxId, QueryId, LibraryQuery, LibraryResult, CtxQuery, CtxResult, MessageToRuntime, MessageFromRuntime};

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

#[derive(Clone)]
enum DynContext {
    ComputationImmut(Arc<dyn ComputationImmutContext<JsMapping>>),
    LatticeImmut(Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>),
    LatticeMut(Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>),
}

impl DynContext {
    fn ptr_eq(&self, other: &DynContext) -> bool {
        match (self, other) {
            (DynContext::ComputationImmut(a), DynContext::ComputationImmut(b)) => Arc::ptr_eq(a, b),
            (DynContext::LatticeImmut(a), DynContext::LatticeImmut(b)) => Arc::ptr_eq(a, b),
            (DynContext::LatticeMut(a), DynContext::LatticeMut(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}

#[async_trait]
impl HashLookup for DynContext {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
         match &*self {
             DynContext::ComputationImmut(ctx) => ctx.clone().hash_lookup(hash).await,
             DynContext::LatticeImmut(ctx) => ctx.clone().hash_lookup(hash).await,
             DynContext::LatticeMut(ctx) => ctx.clone().hash_lookup(hash).await,
         }
     }
}

#[async_trait]
impl HashPut for DynContext {
     async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
         match &*self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot hash_put in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => bail!("Cannot hash_put in LatticeImmutContext"),
             DynContext::LatticeMut(ctx) => ctx.clone().hash_put(value).await,
         }
     }
}


#[async_trait]
impl ComputationImmutContext<JsMapping> for DynContext {
     async fn eval_computation(self: Arc<Self>, key: &JsValue) -> Res<JsValue> {
         match &*self {
             DynContext::ComputationImmut(ctx) => ctx.clone().eval_computation(key).await,
             DynContext::LatticeImmut(ctx) => ctx.clone().eval_computation(key).await,
             DynContext::LatticeMut(ctx) => ctx.clone().eval_computation(key).await,
         }
     }
}


#[async_trait]
impl LatticeImmutContext<JsMapping, JsMapping, JsMapping> for DynContext {
     async fn lattice_lookup(self: Arc<Self>, key: &JsValue) -> Res<Option<Hash<LatMerkleNode<JsValue, JsValue, JsValue, JsValue, JsValue>>>> {
         match &*self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot lattice_lookup in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => ctx.clone().lattice_lookup(key).await,
             DynContext::LatticeMut(ctx) => ctx.clone().lattice_lookup(key).await,
         }
     }
 
     async fn eval_lat_computation(self: Arc<Self>, key: &JsValue) -> Res<Hash<LatMerkleNode<JsValue, JsValue, JsValue, JsValue, JsValue>>> {
         match &*self {
             DynContext::ComputationImmut(ctx) => bail!("Cannot eval_lat_computation in ComputationImmutContext"),
             DynContext::LatticeImmut(ctx) => ctx.clone().eval_lat_computation(key).await,
             DynContext::LatticeMut(ctx) => ctx.clone().eval_lat_computation(key).await,
         }
     }
}


pub struct JsLibrary {
    sender: Mutex<Sender<MessageToRuntime>>,
    receiver: Mutex<Receiver<MessageFromRuntime>>,
    contexts_by_id: Mutex<BTreeMap<CtxId, DynContext>>,
    ids_by_context: Mutex<Vec<(DynContext, CtxId)>>,
    ctx_count: Mutex<CtxId>,
    join_handle: JoinHandle<Res<()>>,
}

impl JsLibrary {
    pub fn new(script: String) -> Self {
        let (from_runtime_sender, from_runtime_receiver) = channel();
        let (to_runtime_sender, to_runtime_receiver) = channel();
        let join_handle = spawn(move || {
            let runtime_state = RuntimeState::new(script, from_runtime_sender, to_runtime_receiver);
            block_on(runtime_state.process_messages())
        });
        Self {
            sender: Mutex::new(to_runtime_sender),
            receiver: Mutex::new(from_runtime_receiver),
            contexts_by_id: Mutex::new(BTreeMap::<CtxId, DynContext>::new()),
            ids_by_context: Mutex::new(Vec::new()),
            ctx_count: Mutex::new(0),
            join_handle
        }
    }
    fn get_ctx_id(&self, immut: &DynContext) -> CtxId {
        let mut ids = self.ids_by_context.lock().unwrap();
        for (ptr, id) in &*ids {
            if ptr.ptr_eq(immut) {
                return *id;
            }
        }
        let mut ctx_count = self.ctx_count.lock().unwrap();
        let id = *ctx_count;
        *ctx_count += 1;
        ids.push((immut.clone(), id));
        self.contexts_by_id.lock().unwrap().insert(id, immut.clone());
        id
    }
}

#[async_trait]
impl ComputationLibrary<JsMapping> for JsLibrary {
    async fn eval_computation(self: Arc<Self>, key: &JsValue, ctx: Arc<dyn ComputationImmutContext<JsMapping>>) -> Res<JsValue> {
        let dyn_ctx = DynContext::ComputationImmut(ctx);
        let ctxid = self.get_ctx_id(&dyn_ctx);
        bail!("Not implemented");
    }
}
