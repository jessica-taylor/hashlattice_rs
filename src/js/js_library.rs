use std::sync::Arc;
use core::cmp::Ordering;

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

enum ContextResource {
    ComputationImmut(Arc<dyn ComputationImmutContext<JsMapping>>),
    LatticeImmut(Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>),
    LatticeMut(Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>),
}

impl Resource for ContextResource {}

impl ContextResource {
    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        match self {
            ContextResource::ComputationImmut(ctx) => ctx.clone().hash_lookup(hash),
            ContextResource::LatticeImmut(ctx) => ctx.clone().hash_lookup(hash),
            ContextResource::LatticeMut(ctx) => ctx.clone().hash_lookup(hash),
        }
    }
    fn eval_computation(&self, key: &JsValue) -> Res<JsValue> {
        match self {
            ContextResource::ComputationImmut(ctx) => ctx.clone().eval_computation(key),
            ContextResource::LatticeImmut(ctx) => ctx.clone().eval_computation(key),
            ContextResource::LatticeMut(ctx) => ctx.clone().eval_computation(key),
        }
    }
    fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        match self {
            ContextResource::ComputationImmut(ctx) => bail!("Cannot hash_put in ComputationImmutContext"),
            ContextResource::LatticeImmut(ctx) => bail!("Cannot hash_put in LatticeImmutContext"),
            ContextResource::LatticeMut(ctx) => ctx.clone().hash_put(value),
        }
    }
    fn lattice_lookup(&self, key: &JsValue) -> Res<(JsValue, Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>)> {
        match self {
            ContextResource::ComputationImmut(ctx) => bail!("Cannot lattice_lookup in ComputationImmutContext"),
            ContextResource::LatticeImmut(ctx) => ctx.clone().lattice_lookup(key),
            ContextResource::LatticeMut(ctx) => ctx.clone().lattice_lookup(key),
        }
    }

    fn eval_lat_computation(&self, key: &JsValue) -> Res<(JsValue, Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>)> {
        match self {
            ContextResource::ComputationImmut(ctx) => bail!("Cannot eval_lat_computation in ComputationImmutContext"),
            ContextResource::LatticeImmut(ctx) => ctx.clone().eval_lat_computation(key),
            ContextResource::LatticeMut(ctx) => ctx.clone().eval_lat_computation(key),
        }
    }

    fn lattice_join(&self, key: &JsValue, value: &JsValue, ctx_other: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>) -> Res<JsValue> {
        match self {
            ContextResource::ComputationImmut(ctx) => bail!("Cannot lattice_join in ComputationImmutContext"),
            ContextResource::LatticeImmut(ctx) => bail!("Cannot lattice_join in LatticeImmutContext"),
            ContextResource::LatticeMut(ctx) => ctx.clone().lattice_join(key, value, ctx_other),
        }
    }
}

#[op]
async fn op_hash_lookup(state: &mut OpState, ctxid: u32, hash: HashCode) -> Result<Vec<u8>, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    ctx.hash_lookup(hash)
}

#[op]
async fn op_eval_computation(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<SerdeJsValue, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let value = ctx.eval_computation(&JsValue(key))?;
    Ok(value.0)
}

#[op]
async fn op_hash_put(state: &mut OpState, ctxid: u32, value: Vec<u8>) -> Result<HashCode, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    ctx.hash_put(value)
}

#[op]
async fn op_lattice_lookup(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<(SerdeJsValue, u32), AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let (value, ctx_other) = ctx.lattice_lookup(&JsValue(key))?;
    let ctxid_other = state.resource_table.add(ContextResource::LatticeImmut(ctx_other));
    Ok((value.0, ctxid_other))
}

#[op]
async fn op_eval_lat_computation(state: &mut OpState, ctxid: u32, key: SerdeJsValue) -> Result<(SerdeJsValue, u32), AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let (value, ctx_other) = ctx.eval_lat_computation(&JsValue(key))?;
    let ctxid_other = state.resource_table.add(ContextResource::LatticeImmut(ctx_other));
    Ok((value.0, ctxid_other))
}

#[op]
async fn op_lattice_join(state: &mut OpState, ctxid: u32, key: SerdeJsValue, value: SerdeJsValue, ctxid_other: u32) -> Result<SerdeJsValue, AnyError> {
    let ctx = state.resource_table.get::<ContextResource>(ctxid)?;
    let ctx_other = state.resource_table.get::<ContextResource>(ctxid_other)?;
    let other_arc: Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>> = match ctx_other.as_ref() {
        ContextResource::ComputationImmut(ctx) => bail!("Cannot lattice_join with ComputationImmutContext"),
        ContextResource::LatticeImmut(ctx) => ctx.clone(),
        ContextResource::LatticeMut(ctx) => ctx.clone().as_lattice_immut_ctx(),
    };
    let value = ctx.lattice_join(&JsValue(key), &JsValue(value), other_arc)?;
    Ok(value.0)
}

fn main() {
  // Build a deno_core::Extension providing custom ops
  let ext = Extension::builder()
    .ops(vec![
      op_hash_lookup::decl(),
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

// pub struct JsLibrary {
//     script: Script,
//     comp_immut_stack: Vec<Arc<dyn ComputationImmutContext<JsMapping>>>,
//     lat_immut_stack: Vec<Arc<dyn LatticeImmutContext<JsMapping, JsMapping, JsMapping>>>,
//     lat_mut_stack: Vec<Arc<dyn LatticeMutContext<JsMapping, JsMapping, JsMapping>>>,
// }
// 
// impl JsLibrary {
//     pub fn new(script: Script) -> Self {
//         Self {
//             script,
//             comp_immut_stack: vec![],
//             lat_immut_stack: vec![],
//             lat_mut_stack: vec![],
//         }
//     }
//     fn trampoline(&self, value: JsValue) -> Res<JsValue> {
//         if let JsValue::Object(js_map) = value {
//             if let Some(res) = js_map.get("result") {
//                 return Ok(res.clone());
//             }
//             if let Some(JsValue::String(fn_name)) = js_map.get("call") {
//                 if fn_name == "hash_lookup" {
//                     if let Some(JsValue::Number(ctx_num)) = js_map.get("context") {
//                         let ctx = self.comp_immut_stack.get(ctx_num.as_i64().ok_or("bad ctx index".to_string()? as usize)).ok_or("bad ctx index".to_string())?;
//                         if let Some(JsValue::String(hash_code)) = js_map.get("hash") {
//                             let hsh: Hash<JsValue> = Hash::from_hex(&hash_code)?;
//                             let bytes = ctx.clone().hash_lookup(hsh.code)?;
//                             // ... call something with bytes???
//                             return self.trampoline(res);
//                         } else {
//                             return bail!("hash_lookup: hash not found");
//                         }
//                     } else {
//                         return bail!("hash_lookup: context not found");
//                     }
//                 }
//             }
//         } else {
//             bail!("trampoline: expected object")
//         }
//     }
// }
// 
// impl ComputationLibrary<JsMapping> for JsLibrary {
//     fn eval_computation(&self, key: &JsValue, ctx: Arc<dyn ComputationImmutContext<JsMapping>>) -> Res<JsValue> {
//         let ctx_ix = self.comp_immut_stack.len();
//         self.comp_immut_stack.push(ctx);
//         let res = self.script.call("eval_computation_trampoline", (key.clone(), ctx_ix)).and_then(|res| self.trampoline(res));
//         self.comp_immut_stack.pop();
//         res
//     }
// }
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
