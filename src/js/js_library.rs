use core::cmp::Ordering;
use core::pin::Pin;
use core::task::Poll;
use std::sync::{Arc, Mutex};
use std::rc::Rc;
use std::sync::mpsc::{Sender, Receiver, channel, TryRecvError};
use std::collections::BTreeMap;
use std::thread::{spawn, JoinHandle};

use futures::Future;
use futures::channel::oneshot;
use futures::executor::block_on;
use futures::future::{FutureExt, poll_fn};
use async_trait::async_trait;
use anyhow::bail;
use serde::{Serialize, Deserialize};
use deno_core::error::AnyError;
use deno_core::{JsRuntime, Extension, RuntimeOptions, op, OpState, Resource};
use deno_core::serde_json::{Value as SerdeJsValue, to_string as json_to_string};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode, hash};
use crate::lattice::{HashLookup, ComputationImmutContext, HashPut, ComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext, LatMerkleNode, hash_lookup_generic, hash_put_generic};
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
             DynContext::LatticeImmut(ctx) => bail!("Cannot eval_lat_computation in LatticeimmutContext"),
             DynContext::LatticeMut(ctx) => ctx.clone().eval_lat_computation(key).await,
         }
     }
}

struct OutQueryState {
    query_count: QueryId,
    query_receivers: BTreeMap<QueryId, oneshot::Sender<Res<LibraryResult>>>,
}

pub struct JsLibrary {
    sender: Mutex<Sender<MessageToRuntime>>,
    receiver: Mutex<Receiver<MessageFromRuntime>>,
    contexts_by_id: Mutex<BTreeMap<CtxId, DynContext>>,
    ids_by_context: Mutex<Vec<(DynContext, CtxId)>>,
    ctx_count: Mutex<CtxId>,
    join_handle: JoinHandle<Res<()>>,
    query_state: Mutex<OutQueryState>,
    ctx_futures: Mutex<BTreeMap<QueryId, Pin<Box<dyn Send + Future<Output = Res<CtxResult>>>>>>,
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
            query_state: Mutex::new(OutQueryState {
                query_count: 0,
                query_receivers: BTreeMap::new(),
            }),
            ctx_futures: Mutex::new(BTreeMap::<QueryId, Pin<Box<dyn Send + Future<Output = Res<CtxResult>>>>>::new()),
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
    async fn do_query(&self, query: LibraryQuery) -> Res<LibraryResult> {
        let (query_sender, query_receiver) = oneshot::channel();
        let query_id = {
            let mut query_state = self.query_state.lock().unwrap();
            let query_id = query_state.query_count;
            query_state.query_count += 1;
            query_state.query_receivers.insert(query_id, query_sender);
            query_id
        };
        self.sender.lock().unwrap().send(MessageToRuntime::LibraryQuery(query_id, query)).unwrap();
        query_receiver.await.unwrap()
    }
    pub async fn process_messages(self: Arc<Self>) -> Res<()> {
        poll_fn(move |_| {
            let msg = self.receiver.lock().unwrap().try_recv();
            match msg {
                Err(TryRecvError::Empty) => {
                    return Poll::Pending;
                },
                Err(TryRecvError::Disconnected) => {
                    return Poll::Ready(Ok(()));
                },
                Ok(MessageFromRuntime::LibraryResult(query_id, result)) => {
                    let mut query_state = self.query_state.lock().unwrap();
                    let query_sender = query_state.query_receivers.remove(&query_id).unwrap();
                    query_sender.send(result).unwrap();
                },
                Ok(MessageFromRuntime::CtxQuery(query_id, ctx_id, query)) => {
                    let ctx = Arc::new(self.contexts_by_id.lock().unwrap().get(&ctx_id).unwrap().clone());
                    let fut: Pin<Box<dyn Send + Future<Output = Res<CtxResult>>>> = match query {
                        CtxQuery::HashLookup(hash) => {
                            Box::pin(async move {
                                Ok(CtxResult::HashLookup(hash_lookup_generic(&ctx, hash).await?))
                            })

                        }
                        CtxQuery::HashPut(value) => {
                            Box::pin(async move {
                                Ok(CtxResult::HashPut(hash_put_generic(&ctx, &value).await?))
                            })
                        },
                        CtxQuery::EvalComputation(key) => {
                            Box::pin(async move {
                                Ok(CtxResult::EvalComputation(ctx.eval_computation(&JsValue(key)).await?.0))
                            })
                        },
                        CtxQuery::LatticeLookup(key) => {
                            Box::pin(async move { 
                                let opt_merkle_hash = ctx.clone().lattice_lookup(&JsValue(key)).await?;
                                match opt_merkle_hash {
                                    None => Ok(CtxResult::LatticeLookup(None)),
                                    Some(merkle_hash) => Ok(CtxResult::LatticeLookup(Some(hash_lookup_generic(&ctx, merkle_hash).await?.value.0)))
                                }
                                    
                                    // None => Ok(SerdeJsValue::Null),
                                    // Some(merkle_hash) => Ok(SerdeJsValue::Array(vec![hash_lookup_generic(&ctx, merkle_hash).await?.value.0]))
                            })
                        },
                        CtxQuery::EvalLatComputation(key) => {
                            Box::pin(async move { 
                                let merkle_hash = ctx.clone().eval_lat_computation(&JsValue(key)).await?;
                                Ok(CtxResult::EvalLatComputation(hash_lookup_generic(&ctx, merkle_hash).await?.value.0))
                            })
                        },
                    };
                    self.ctx_futures.lock().unwrap().insert(query_id, Box::pin(fut));
                    // self.sender.lock().unwrap().send(MessageToRuntime::CtxResult(ctx_id, result)).unwrap();
                },
            }
            Poll::Pending
        }).await
    }
}



#[async_trait]
impl ComputationLibrary<JsMapping> for JsLibrary {
    async fn eval_computation(self: Arc<Self>, key: &JsValue, ctx: Arc<dyn ComputationImmutContext<JsMapping>>) -> Res<JsValue> {
        let dyn_ctx = DynContext::ComputationImmut(ctx);
        let ctxid = self.get_ctx_id(&dyn_ctx);
        if let LibraryResult::EvalComputation(result) = self.do_query(LibraryQuery::EvalComputation(key.0.clone(), ctxid)).await? {
            Ok(JsValue(result))
        } else {
            bail!("Unexpected result from eval_computation")
        }
    }
}

#[async_trait]
impl LatticeLibrary<JsMapping, JsMapping, JsMapping> for JsLibrary {
    async fn check_elem(self: Arc<Self>, key: &JsValue, value: &JsValue, ctx: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>) -> Res<()> {
        let dyn_ctx = DynContext::LatticeImmut(ctx);
        let ctxid = self.get_ctx_id(&dyn_ctx);
        if let LibraryResult::CheckElem = self.do_query(LibraryQuery::CheckElem(key.0.clone(), value.0.clone(), ctxid)).await? {
            Ok(())
        } else {
            bail!("Unexpected result from check_elem")
        }
    }

    async fn join(self: Arc<Self>, key: &JsValue, a: &JsValue, b: &JsValue, ctx: Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>) -> Res<Option<JsValue>> {
        let dyn_ctx = DynContext::LatticeMut(ctx);
        let ctxid = self.get_ctx_id(&dyn_ctx);
        if let LibraryResult::Join(result) = self.do_query(LibraryQuery::Join(key.0.clone(), a.0.clone(), b.0.clone(), ctxid)).await? {
            Ok(result.map(JsValue))
        } else {
            bail!("Unexpected result from join")
        }
    }

    async fn transport(self: Arc<Self>, key: &JsValue, value: &JsValue, old_ctx: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>, new_ctx: Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>) -> Res<Option<JsValue>> {
        let dyn_old_ctx = DynContext::LatticeImmut(old_ctx);
        let dyn_new_ctx = DynContext::LatticeMut(new_ctx);
        let old_ctxid = self.get_ctx_id(&dyn_old_ctx);
        let new_ctxid = self.get_ctx_id(&dyn_new_ctx);
        if let LibraryResult::Transport(result) = self.do_query(LibraryQuery::Transport(key.0.clone(), value.0.clone(), old_ctxid, new_ctxid)).await? {
            Ok(result.map(JsValue))
        } else {
            bail!("Unexpected result from transport")
        }
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &JsValue, ctx: Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
        let dyn_ctx = DynContext::LatticeMut(ctx);
        let ctxid = self.get_ctx_id(&dyn_ctx);
        if let LibraryResult::EvalLatComputation(result) = self.do_query(LibraryQuery::EvalLatComputation(key.0.clone(), ctxid)).await? {
            Ok(JsValue(result))
        } else {
            bail!("Unexpected result from eval_lat_computation")
        }
    }
}
