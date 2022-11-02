
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::rc::Rc;
use core::cmp::Ordering;

use futures::channel::oneshot;
use anyhow::{anyhow, bail};
use serde::{Serialize, Deserialize};
use deno_core::serde_v8::{to_v8, from_v8};
use deno_core::v8::{Value as V8Value, Function as V8Function, Local};
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
    LatticeJoin(JsValue, JsValue, CtxId),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum CtxResult {
    HashLookup(JsValue),
    EvalComputation(JsValue),
    HashPut(Hash<JsValue>),
    LatticeLookup(JsValue, CtxId),
    EvalLatComputation(JsValue, CtxId),
    LatticeJoin(JsValue),
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

#[op]
async fn op_lattice_join(state: &mut OpState, globalid: u32, ctxid: CtxId, key: JsValue, value: JsValue, ctxid_other: CtxId) -> Result<JsValue, AnyError> {
    if let CtxResult::LatticeJoin(value) = op_query(state, globalid, ctxid, CtxQuery::LatticeJoin(key, value, ctxid_other)).await? {
        Ok(value)
    } else {
        bail!("Lattice join returned wrong result type")
    }
}


struct RuntimeState {
    runtime: JsRuntime,
    script: String,
    global_id: u32,
    receiver: Receiver<MessageToRuntime>,
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
                op_lattice_join::decl(),
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
        (Self { runtime, script, receiver: to_runtime_receiver, global_id }, to_runtime_sender, from_runtime_receiver)
    }
    fn call_function(&mut self, path: &str, args: &[JsValue]) -> Result<JsValue, AnyError> {
        let mut scope = self.runtime.handle_scope();
        let recv = to_v8(&mut scope, JsValue::Null)?;
        let fun: Local<'_, V8Function> = JsRuntime::grab_global(&mut scope, path).ok_or(anyhow!("Could not find function {}", path))?;
        let v8_args = args.iter().map(|v| to_v8(&mut scope, v.clone())).collect::<Result<Vec<_>, _>>()?;
        let opt_res = fun.call(&mut scope, recv, &v8_args);
        let res = opt_res.ok_or(anyhow!("Could not call function {}", path))?;
        Ok(from_v8(&mut scope, res)?)
    }
    pub fn process_messages(&mut self) {
        while let Ok(msg) = self.receiver.try_recv() {
            match msg {
                MessageToRuntime::LibraryQuery(query_id, query) => {
                    // let result = match query {
                    //     LibraryQuery::HashLookup(hash) => {
                    //         let value = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).hash_lookup(hash);
                    //         LibraryResult::HashLookup(value)
                    //     },
                    //     LibraryQuery::EvalComputation(key) => {
                    //         let value = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).eval_computation(key);
                    //         LibraryResult::EvalComputation(value)
                    //     },
                    //     LibraryQuery::HashPut(value) => {
                    //         let hash = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).hash_put(value);
                    //         LibraryResult::HashPut(hash)
                    //     },
                    //     LibraryQuery::LatticeLookup(key) => {
                    //         let (value, ctxid) = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).lattice_lookup(key);
                    //         LibraryResult::LatticeLookup(value, ctxid)
                    //     },
                    //     LibraryQuery::EvalLatComputation(key) => {
                    //         let (value, ctxid) = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).eval_lat_computation(key);
                    //         LibraryResult::EvalLatComputation(value, ctxid)
                    //     },
                    //     LibraryQuery::LatticeJoin(key, value, ctxid_other) => {
                    //         let value = self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).lattice_join(key, value, ctxid_other);
                    //         LibraryResult::LatticeJoin(value)
                    //     },
                    // };
                    // self.runtime.op_state().borrow_mut().borrow::<GlobalResource>(self.global_id).sender.send(MessageFromRuntime::LibraryResult(query_id, result)).unwrap();
                },
                MessageToRuntime::CtxResult(query_id, result) => {
                    let global = self.runtime.op_state().borrow_mut().resource_table.get::<GlobalResource>(self.global_id).unwrap();
                    let mut query_state = global.query_state.lock().unwrap();
                    let query_receiver = query_state.query_receivers.remove(&query_id).unwrap();
                    query_receiver.send(result).unwrap();
                },
            }
        }
    }
}

