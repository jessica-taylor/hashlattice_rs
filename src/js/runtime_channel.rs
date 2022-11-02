
use std::ops::DerefMut;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{channel, Sender, Receiver, TryRecvError};
use std::rc::Rc;
use core::cmp::Ordering;
use core::pin::Pin;

use futures::task::{Poll, Context};
use futures::Future;
use futures::future::{FutureExt, poll_fn};
use futures::channel::oneshot;
use anyhow::{anyhow, bail};
use serde::{Serialize, Deserialize};
use deno_core::serde_v8::{to_v8, from_v8};
use deno_core::v8::{Value as V8Value, Function as V8Function, Local, Global};
use deno_core::error::AnyError;
use deno_core::{JsRuntime, Extension, RuntimeOptions, op, OpState, Resource};
use deno_core::serde_json::{Value as JsValue, to_string as json_to_string};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode, hash};
use crate::lattice::{HashLookup, ComputationImmutContext, ComputationMutContext, ComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext};

type QueryId = usize;
type CtxId = usize;

#[derive(Debug, Clone, Serialize, Deserialize)]
enum LibraryQuery {
    EvalComputation(JsValue, CtxId),
    CheckElem(JsValue, JsValue, CtxId),
    Join(JsValue, JsValue, JsValue, CtxId),
    Bottom(JsValue),
    Transport(JsValue, JsValue, CtxId, CtxId),
    EvalLatComputation(JsValue, CtxId),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum LibraryResult {
    EvalComputation(JsValue),
    CheckElem,
    Join(JsValue),
    Bottom(JsValue),
    Transport(JsValue),
    EvalLatComputation(JsValue),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum CtxQuery {
    HashLookup(Hash<JsValue>),
    EvalComputation(JsValue),
    HashPut(JsValue),
    LatticeLookup(JsValue),
    EvalLatComputation(JsValue),
    // LatticeJoin(JsValue, JsValue, CtxId),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum CtxResult {
    HashLookup(JsValue),
    EvalComputation(JsValue),
    HashPut(Hash<JsValue>),
    LatticeLookup(JsValue, CtxId),
    EvalLatComputation(JsValue, CtxId),
    // LatticeJoin(JsValue),
}

enum MessageToRuntime {
    LibraryQuery(QueryId, LibraryQuery),
    CtxResult(QueryId, Res<CtxResult>),
}

enum MessageFromRuntime {
    LibraryResult(QueryId, Res<LibraryResult>),
    CtxQuery(QueryId, CtxId, CtxQuery),
}

struct OutQueryState {
    query_count: QueryId,
    query_receivers: BTreeMap<QueryId, oneshot::Sender<Res<CtxResult>>>,
}

struct GlobalResource {
    query_state: Mutex<OutQueryState>,
    sender: Sender<MessageFromRuntime>,
}

impl Resource for GlobalResource {}

async fn op_query(state: &mut OpState, globalid: u32, ctxid: CtxId, query: CtxQuery) -> Res<CtxResult> {
    let global = state.resource_table.get::<GlobalResource>(globalid)?;
    let (query_sender, query_receiver) = oneshot::channel();
    let query_id = {
        let mut query_state = global.query_state.lock().unwrap();
        let query_id = query_state.query_count;
        query_state.query_count += 1;
        query_state.query_receivers.insert(query_id, query_sender);
        query_id
    };
    global.sender.send(MessageFromRuntime::CtxQuery(query_id, ctxid, query)).unwrap();
    query_receiver.await.unwrap()
}


#[op]
async fn op_hash_lookup(state: &mut OpState, globalid: u32, ctxid: CtxId, hash: HashCode) -> Result<JsValue, AnyError> {
    if let CtxResult::HashLookup(value) = op_query(state, globalid, ctxid, CtxQuery::HashLookup(Hash::from_hashcode(hash))).await? {
        Ok(value)
    } else {
        bail!("Hash lookup returned wrong result type")
    }
}

#[op]
async fn op_eval_computation(state: &mut OpState, globalid: u32, ctxid: CtxId, key: JsValue) -> Result<JsValue, AnyError> {
    if let CtxResult::EvalComputation(value) = op_query(state, globalid, ctxid, CtxQuery::EvalComputation(key)).await? {
        Ok(value)
    } else {
        bail!("Eval computation returned wrong result type")
    }
}

#[op]
async fn op_hash_put(state: &mut OpState, globalid: u32, ctxid: CtxId, value: JsValue) -> Result<HashCode, AnyError> {
    if let CtxResult::HashPut(hash) = op_query(state, globalid, ctxid, CtxQuery::HashPut(value)).await? {
        Ok(hash.code)
    } else {
        bail!("Hash put returned wrong result type")
    }
}

#[op]
async fn op_lattice_lookup(state: &mut OpState, globalid: u32, ctxid: CtxId, key: JsValue) -> Result<(JsValue, CtxId), AnyError> {
    if let CtxResult::LatticeLookup(value, v_ctxid) = op_query(state, globalid, ctxid, CtxQuery::LatticeLookup(key)).await? {
        Ok((value, v_ctxid))
    } else {
        bail!("Lattice lookup returned wrong result type")
    }
}

#[op]
async fn op_eval_lat_computation(state: &mut OpState, globalid: u32, ctxid: CtxId, key: JsValue) -> Result<(JsValue, CtxId), AnyError> {
    if let CtxResult::EvalLatComputation(value, v_ctxid) = op_query(state, globalid, ctxid, CtxQuery::EvalLatComputation(key)).await? {
        Ok((value, v_ctxid))
    } else {
        bail!("Eval lat computation returned wrong result type")
    }
}

// #[op]
// async fn op_lattice_join(state: &mut OpState, globalid: u32, ctxid: CtxId, key: JsValue, value: JsValue, ctxid_other: CtxId) -> Result<JsValue, AnyError> {
//     if let CtxResult::LatticeJoin(value) = op_query(state, globalid, ctxid, CtxQuery::LatticeJoin(key, value, ctxid_other)).await? {
//         Ok(value)
//     } else {
//         bail!("Lattice join returned wrong result type")
//     }
// }


#[derive(Clone)]
struct RuntimeState {
    runtime: Arc<Mutex<JsRuntime>>,
    script: String,
    global_id: u32,
    receiver: Arc<Receiver<MessageToRuntime>>,
    library_futures: Arc<Mutex<BTreeMap<QueryId, Pin<Box<dyn Future<Output = Res<LibraryResult>>>>>>>,
}

impl RuntimeState {
    pub fn new(script: String) -> (Self, Sender<MessageToRuntime>, Receiver<MessageFromRuntime>) {
        let ext = Extension::builder()
            .ops(vec![
                op_hash_lookup::decl(),
                op_eval_computation::decl(),
                op_hash_put::decl(),
                op_lattice_lookup::decl(),
                op_eval_lat_computation::decl(),
                // op_lattice_join::decl(),
            ])
            .build();

        let mut runtime = JsRuntime::new(RuntimeOptions {
            extensions: vec![ext],
            ..Default::default()
        });
        let (from_runtime_sender, from_runtime_receiver) = channel();
        let (to_runtime_sender, to_runtime_receiver) = channel();
        let global_id = runtime.op_state().borrow_mut().resource_table.add(GlobalResource {
            query_state: Mutex::new(OutQueryState {
                query_count: 0,
                query_receivers: BTreeMap::new(),
            }),
            sender: from_runtime_sender,
        });
        (Self {
            runtime: Arc::new(Mutex::new(runtime)),
            script,
            receiver: Arc::new(to_runtime_receiver),
            global_id,
            library_futures: Arc::new(Mutex::new(BTreeMap::<QueryId, Pin<Box<dyn Future<Output = Res<LibraryResult>>>>>::new())),
        }, to_runtime_sender, from_runtime_receiver)
    }
    async fn call_function(runtime_arc: Arc<Mutex<JsRuntime>>, path: String, args: Vec<JsValue>) -> Result<JsValue, AnyError> {
        let mut runtime = runtime_arc.lock().unwrap();
        let mut scope = runtime.handle_scope();
        let recv = to_v8(&mut scope, JsValue::Null)?;
        let fun: Local<'_, V8Function> = JsRuntime::grab_global(&mut scope, &path).ok_or(anyhow!("Could not find function {}", path))?;
        let v8_args = args.iter().map(|v| to_v8(&mut scope, v.clone())).collect::<Result<Vec<_>, _>>()?;
        let opt_res = fun.call(&mut scope, recv, &v8_args);
        let res_local = opt_res.ok_or(anyhow!("Could not call function {}", path))?;
        let res_global = Global::new(&mut *scope, res_local);
        let runtime_arc2 = runtime_arc.clone();
        poll_fn(move |ctx| {
            let mut runtime = runtime_arc2.lock().unwrap();
            let poll = runtime.poll_value(&res_global, ctx);
            poll.map(|res_glob| {
                let mut scope = runtime.handle_scope();
                let local = Local::new(&mut scope, res_glob?);
                Ok(from_v8(&mut scope, local)?)
            })
        }).await
    }
    fn register_call_function(&self, query_id: QueryId, path: &str, args: Vec<JsValue>, res_handler: impl 'static + FnOnce(JsValue) -> Res<LibraryResult>) {
        let fut = Self::call_function(self.runtime.clone(), path.to_string(), args).map(|res| res_handler(res?));
        self.library_futures.lock().unwrap().insert(query_id, Box::pin(fut));
    }
    fn poll_events_pending(&self, ctx: &mut Context<'_>) -> Res<bool> {
        let mut is_pending = false;
        if self.runtime.lock().unwrap().poll_event_loop(ctx, false).is_pending() {
            is_pending = true;
        }
        {
            let mut library_futures = self.library_futures.lock().unwrap();
            let mut to_remove = Vec::new();
            for (query_id, mut fut) in library_futures.iter_mut() {
                match Pin::new(fut.deref_mut()).poll(ctx) {
                    Poll::Ready(res) => {
                        let global = self.runtime.lock().unwrap().op_state().borrow_mut().resource_table.get::<GlobalResource>(self.global_id).unwrap();
                        global.sender.send(MessageFromRuntime::LibraryResult(*query_id, res))?;
                        to_remove.push(*query_id);
                    }
                    Poll::Pending => {
                        is_pending = true;
                    }
                }
            }
            for query_id in to_remove {
                library_futures.remove(&query_id);
            }
        }
        match self.receiver.try_recv() {
            Err(TryRecvError::Empty) => {
                is_pending = true;
            },
            Err(TryRecvError::Disconnected) => {},
            Ok(msg) => {
                is_pending = true;
                match msg {
                    MessageToRuntime::LibraryQuery(query_id, query) => {
                        match query {
                            LibraryQuery::EvalComputation(key, ctxid) => {
                                self.register_call_function(query_id, "eval_computation", vec![key, JsValue::from(ctxid)], |res| Ok(LibraryResult::EvalComputation(res)));
                            },
                            LibraryQuery::CheckElem(key, value, ctxid) => {
                                self.register_call_function(query_id, "hash_put", vec![key, value, JsValue::from(ctxid)], |res| Ok(LibraryResult::CheckElem));
                            },
                            LibraryQuery::Join(key, value1, value2, ctxid) => {
                                self.register_call_function(query_id, "lattice_join", vec![key, value1, value2, JsValue::from(ctxid)], |res| Ok(LibraryResult::Join(res)));
                            },
                            LibraryQuery::Bottom(key) => {
                                self.register_call_function(query_id, "lattice_lookup", vec![key], |res| Ok(LibraryResult::Bottom(res)));
                            },
                            LibraryQuery::Transport(key, value, old_ctxid, new_ctxid) => {
                                self.register_call_function(query_id, "eval_lat_computation", vec![key, value, JsValue::from(old_ctxid), JsValue::from(new_ctxid)], |res| Ok(LibraryResult::Transport(res)));
                            },
                            LibraryQuery::EvalLatComputation(key, ctxid) => {
                                self.register_call_function(query_id, "eval_lat_computation", vec![key, JsValue::from(ctxid)], |res| Ok(LibraryResult::EvalLatComputation(res)));
                            },
                        }
                    },
                    MessageToRuntime::CtxResult(query_id, result) => {
                        let global = self.runtime.lock().unwrap().op_state().borrow_mut().resource_table.get::<GlobalResource>(self.global_id).unwrap();
                        let mut query_state = global.query_state.lock().unwrap();
                        let query_receiver = query_state.query_receivers.remove(&query_id).unwrap();
                        query_receiver.send(result).unwrap();
                    },
                }
            }
        }
        Ok(is_pending)
    }
    pub async fn process_messages(&mut self) -> Res<()> {
        let self2 = self.clone();
        poll_fn(move |ctx| {
            match self2.poll_events_pending(ctx) {
                Ok(is_pending) => {
                    if is_pending {
                        Poll::Pending
                    } else {
                        Poll::Ready(Ok(()))
                    }
                }
                Err(err) => Poll::Ready(Err(err)),
            }
        }).await
    }
}

