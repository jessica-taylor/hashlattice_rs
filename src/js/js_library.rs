use std::sync::{Arc, Mutex};
use std::rc::Rc;
use core::cmp::Ordering;

use async_trait::async_trait;
use anyhow::bail;
use serde::{Serialize, Deserialize};
use deno_core::error::AnyError;
use deno_core::{JsRuntime, Extension, RuntimeOptions, op, OpState, Resource};
use deno_core::serde_json::{Value as SerdeJsValue, to_string as json_to_string};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::crypto::{Hash, HashCode, hash};
use crate::lattice::{HashLookup, ComputationImmutContext, ComputationMutContext, ComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext};

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

struct ContextResource {
    context: DynContext,
    deps: Mutex<Vec<u32>>,
}

impl Resource for ContextResource {}


impl ContextResource {
    fn new(context: DynContext) -> Self {
        Self {
            context,
            deps: Mutex::new(vec![]),
        }
    }
    fn clear_deps(&self, state: &mut OpState) -> Res<()> {
        let mut deps = self.deps.lock().unwrap();
        for dep_id in deps.drain(..) {
            let dep: Rc<ContextResource> = state.resource_table.take(dep_id)?;
            dep.clear_deps(state)?;
        }
        Ok(())
    }
    async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => ctx.hash_lookup(hash).await,
            DynContext::LatticeImmut(ctx) => ctx.hash_lookup(hash).await,
            DynContext::LatticeMut(ctx) => ctx.hash_lookup(hash).await,
        }
    }
    async fn eval_computation(&self, key: &JsValue) -> Res<JsValue> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => ctx.eval_computation(key).await,
            DynContext::LatticeImmut(ctx) => ctx.eval_computation(key).await,
            DynContext::LatticeMut(ctx) => ctx.eval_computation(key).await,
        }
    }
    async fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => bail!("Cannot hash_put in ComputationImmutContext"),
            DynContext::LatticeImmut(ctx) => bail!("Cannot hash_put in LatticeImmutContext"),
            DynContext::LatticeMut(ctx) => ctx.hash_put(value).await,
        }
    }
    async fn lattice_lookup(&self, key: &JsValue) -> Res<(JsValue, Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>)> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => bail!("Cannot lattice_lookup in ComputationImmutContext"),
            DynContext::LatticeImmut(ctx) => ctx.lattice_lookup(key).await,
            DynContext::LatticeMut(ctx) => ctx.lattice_lookup(key).await,
        }
    }

    async fn eval_lat_computation(&self, key: &JsValue) -> Res<(JsValue, Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>)> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => bail!("Cannot eval_lat_computation in ComputationImmutContext"),
            DynContext::LatticeImmut(ctx) => ctx.eval_lat_computation(key).await,
            DynContext::LatticeMut(ctx) => ctx.eval_lat_computation(key).await,
        }
    }

    async fn lattice_join(&self, key: &JsValue, value: &JsValue, ctx_other: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
        match &self.context {
            DynContext::ComputationImmut(ctx) => bail!("Cannot lattice_join in ComputationImmutContext"),
            DynContext::LatticeImmut(ctx) => bail!("Cannot lattice_join in LatticeImmutContext"),
            DynContext::LatticeMut(ctx) => ctx.lattice_join(key, value, ctx_other).await,
        }
    }
}

#[op]
async fn op_hash_lookup(state: &mut OpState, ctxid: u32, hash: HashCode) -> Result<Vec<u8>, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    ctx.hash_lookup(hash).await
}

#[op]
async fn op_eval_computation(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<SerdeJsValue, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let value = ctx.eval_computation(&JsValue(key)).await?;
    Ok(value.0)
}

#[op]
async fn op_hash_put(state: &mut OpState, ctxid: u32, value: Vec<u8>) -> Result<HashCode, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    ctx.hash_put(value).await
}

#[op]
async fn op_lattice_lookup(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<(SerdeJsValue, u32), AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let (value, ctx_other) = ctx.lattice_lookup(&JsValue(key)).await?;
    let ctxid_other = state.resource_table.add(ContextResource::new(DynContext::LatticeImmut(ctx_other)));
    ctx.deps.lock().unwrap().push(ctxid_other);
    Ok((value.0, ctxid_other))
}

#[op]
async fn op_eval_lat_computation(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<(SerdeJsValue, u32), AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let (value, ctx_other) = ctx.eval_lat_computation(&JsValue(key)).await?;
    let ctxid_other = state.resource_table.add(ContextResource::new(DynContext::LatticeImmut(ctx_other)));
    ctx.deps.lock().unwrap().push(ctxid_other);
    Ok((value.0, ctxid_other))
}

#[op]
async fn op_lattice_join(state: &mut OpState, ctxid: u32, key: SerdeJsValue, value: SerdeJsValue, ctxid_other: u32) -> Result<SerdeJsValue, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let ctx_other = state.resource_table.get::<ContextResource>(ctxid_other)?;
    let other_arc: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>> = match &ctx_other.context {
        DynContext::ComputationImmut(ctx) => bail!("Cannot lattice_join with ComputationImmutContext"),
        DynContext::LatticeImmut(ctx) => ctx.clone(),
        DynContext::LatticeMut(ctx) => ctx.as_lattice_immut_ctx(),
    };
    let value = ctx.lattice_join(&JsValue(key), &JsValue(value), other_arc).await?;
    Ok(value.0)
}

fn main() {
    // Build a deno_core::Extension providing custom ops
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

  // Initialize a runtime instance
  let mut runtime = JsRuntime::new(RuntimeOptions {
    extensions: vec![ext],
    ..Default::default()
  });

  // Now we see how to invoke the op we just defined. The runtime automatically
  // contains a Deno.core object with several functions for interacting with it.
  // You can find its definition in core.js.
  runtime
    .execute_script(
      "<usage>",
      r#"
// Print helper function, calling Deno.core.print()
function print(value) {
  Deno.core.print(value.toString()+"\n");
}
const arr = [1, 2, 3];
print("The sum of");
print(arr);
print("is");
print(Deno.core.ops.op_sum(arr));
// And incorrect usage
try {
  print(Deno.core.ops.op_sum(0));
} catch(e) {
  print('Exception:');
  print(e);
}
"#,
    )
    .unwrap();
}

#[derive(Clone)]
pub struct JsLibrary {
    runtime: Arc<Mutex<JsRuntime>>,
    script: Arc<String>,
}

impl JsLibrary {
    pub fn new(script: String) -> Self {
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

        let runtime = JsRuntime::new(RuntimeOptions {
            extensions: vec![ext],
            ..Default::default()
        });
        Self { runtime: Arc::new(Mutex::new(runtime)), script: Arc::new(script) }
    }
}

#[async_trait(?Send)]
impl ComputationLibrary<JsMapping> for JsLibrary {
    async fn eval_computation(&self, key: &JsValue, ctx: Arc<dyn ComputationImmutContext<JsMapping>>) -> Res<JsValue> {
        let ctxid = self.runtime.lock().unwrap().op_state().borrow_mut().resource_table.add(ContextResource::new(DynContext::ComputationImmut(ctx)));
        bail!("not implemented")
    }
}
// 
// impl LatticeLibrary<JsMapping, JsMapping, JsMapping> for JsLibrary {
//     fn check_elem(&self, key: &JsValue, value: &JsValue, ctx: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>) -> Res<()> {
//         bail!("check_elem not implemented")
//     }
// 
//     fn join(&self, key: &JsValue, a: &JsValue, b: &JsValue, ctx: Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
//         bail!("join not implemented")
//     }
// 
//     fn bottom(&self, key: &JsValue) -> Res<JsValue> {
//         bail!("bottom not implemented")
//     }
// 
//     fn transport(&self, key: &JsValue, value: &JsValue, old_ctx: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>, new_ctx: Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
//         Ok(value.clone())
//     }
// 
//     fn eval_lat_computation(&self, key: &JsValue, ctx: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
//         bail!("eval_lat_computation not implemented")
//     }
// }
