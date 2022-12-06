
{-# OPTIONS --cubical --guardedness #-}
module auto_update where



open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Empty
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public
open import Relation.Nullary using (¬_)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Base using (_×_) public

-- case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- case x of f = f x

data Comparison : Type where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

negate-cmp : Comparison → Comparison
negate-cmp LT = GT
negate-cmp EQ = EQ
negate-cmp GT = LT


record Ordinal ℓ : Type (lsuc ℓ) where
  field
    elᵒ : Type ℓ
    compareᵒ : elᵒ → elᵒ → Comparison
    reflᵒ : {x : elᵒ} → compareᵒ x x ≡ EQ
    anticommᵒ : {x y : elᵒ} → compareᵒ x y ≡ negate-cmp (compareᵒ y x)
    is-eqᵒ : {x y : elᵒ} → compareᵒ x y ≡ EQ → x ≡ y
    transᵒ : {x y z : elᵒ} → compareᵒ x y ≡ LT → compareᵒ y z ≡ LT → compareᵒ x z ≡ LT

  type<ᵒ : elᵒ → Type ℓ
  type<ᵒ k = Σ elᵒ (λ k' → compareᵒ k' k ≡ LT)



  field
    inductionᵒ : (P : elᵒ → Type) → ((k : elᵒ) → ((k' : type<ᵒ k) → P (fst k')) → P k) → (k : elᵒ) → P k

  to-type<ᵒ : (k : elᵒ) → elᵒ → Maybe (type<ᵒ k)
  to-type<ᵒ k k' with compareᵒ k' k | inspect (compareᵒ k') k
  ... | LT | [ lt ]ᵢ = just ((k' , lt))
  ... | _ | _ = nothing



open Ordinal

record SemiLat : Type₁ where
  field
    elˢ : Type
    joinˢ : elˢ → elˢ → elˢ 
    bottomˢ : elˢ

open SemiLat

maybe-≤ : {S : Type} → (S → S → Type) → Maybe S → Maybe S → Type
maybe-≤ _ nothing _ = Unit
maybe-≤ _ (just _) nothing = ⊥
maybe-≤ ≤ (just x) (just y) = ≤ x y

maybe-join : {S : Type} → (S → S → S) → Maybe S → Maybe S → Maybe S
maybe-join _ nothing y = y
maybe-join _ x nothing = x
maybe-join join (just x) (just y) = just (join x y)

maybe->>= : {A B : Type} → Maybe A → (A → Maybe B) → Maybe B
maybe->>= nothing _ = nothing
maybe->>= (just x) f = f x
  

record SemiLatGraph : Type₁ where
  field

    keyᵍ : Ordinal lzero
    valueᵍ : Type

  Ctxᵍ : Type
  Ctxᵍ = (elᵒ keyᵍ → Maybe valueᵍ)

  Key<ᵍ : elᵒ keyᵍ → Type
  Key<ᵍ k = Σ (elᵒ keyᵍ) (λ k' → compareᵒ keyᵍ k' k ≡ LT)

  Key≤ᵍ : elᵒ keyᵍ → Type
  Key≤ᵍ k = Σ (elᵒ keyᵍ) (λ k' → ¬ (compareᵒ keyᵍ k' k ≡ GT))

  Ctx<ᵍ : elᵒ keyᵍ → Type
  Ctx<ᵍ k = Key<ᵍ k → Maybe valueᵍ

  Ctx≤ᵍ : elᵒ keyᵍ → Type
  Ctx≤ᵍ k = Key≤ᵍ k → Maybe valueᵍ

  field
    is-elemᵍ : (k : elᵒ keyᵍ) → Ctx<ᵍ k → valueᵍ → Type
    joinᵍ : (k : elᵒ keyᵍ) → Ctx<ᵍ k → valueᵍ → valueᵍ → valueᵍ
    transportᵍ : (k : elᵒ keyᵍ) → Ctx<ᵍ k → Ctx<ᵍ k → valueᵍ → Maybe valueᵍ

  ctx<-to-ctxᵍ : {k : elᵒ keyᵍ} → Ctx<ᵍ k → Ctxᵍ
  ctx<-to-ctxᵍ {k} ctx k' = maybe->>= (to-type<ᵒ keyᵍ k k') ctx

  ctx-filter-<ᵍ : (k : elᵒ keyᵍ) → Ctxᵍ → Ctx<ᵍ k
  ctx-filter-<ᵍ k ctx k' = ctx (fst k')

  ctx<-filter-<ᵍ : {k : elᵒ keyᵍ} → (k' : elᵒ keyᵍ) → Ctx<ᵍ k → Ctx<ᵍ k'
  ctx<-filter-<ᵍ k' ctx = ctx-filter-<ᵍ k' (ctx<-to-ctxᵍ ctx)

  ctx-are-elemsᵍ : Ctxᵍ → Type
  ctx-are-elemsᵍ ctx =
    (k : elᵒ keyᵍ) → case ctx k of
      λ { nothing → Unit;
          (just v) → is-elemᵍ k (ctx-filter-<ᵍ k ctx) v }

    

  ctx<-are-elemsᵍ : {k : elᵒ keyᵍ} → Ctx<ᵍ k → Type
  ctx<-are-elemsᵍ ctx = ctx-are-elemsᵍ (ctx<-to-ctxᵍ ctx)

  ctx-≤ᵍ : Ctxᵍ → Ctxᵍ → Type
  ctx-≤ᵍ ctx1 ctx2 = (k : elᵒ keyᵍ) →
    let v1' = maybe->>= (ctx1 k) (transportᵍ k (ctx-filter-<ᵍ k ctx1) (ctx-filter-<ᵍ k ctx2))
    in maybe-≤ (λ v1 v2 → joinᵍ k (ctx-filter-<ᵍ k ctx2) v1 v2 ≡ v2) v1' (ctx2 k)

  ctx<-≤ᵍ : {k : elᵒ keyᵍ} → Ctx<ᵍ k → Ctx<ᵍ k → Type
  ctx<-≤ᵍ ctx1 ctx2 = ctx-≤ᵍ (ctx<-to-ctxᵍ ctx1) (ctx<-to-ctxᵍ ctx2)
-- case tran
--     case ctx1 k of
--     λ {nothing → Unit;
--        (just v1) → case ctx2 k of
--          λ {nothing → ⊥;
--             (just v2) → case transportᵍ k (ctx-filter-<ᵍ k ctx1) (ctx-filter-<ᵍ k ctx2) v1 of
--               λ {nothing → Unit;
--                  (just v1') → joinᵍ k (ctx-filter-<ᵍ k ctx2) v1' v2 ≡ v2 } } }

  -- ctx-set-to-joinᵍ : elᵒ keyᵍ → Ctxᵍ → Ctxᵍ → Ctxᵍ → Ctxᵍ
  -- ctx-set-to-joinᵍ k ctx1 ctx2 ctx k' = case compareᵒ keyᵍ k' k return (λ _ → Maybe valueᵍ) of
  --   λ { LT → ctx k';
  --       EQ → maybe-join (joinᵍ k ctx) (ctx1 k) (ctx2 k);
  --       GT → nothing }
  -- ctx-include-last : Ctxᵍ → (k : elᵒ keyᵍ) → (type-<ᵒ keyᵍ → Ctxᵍ) → Ctxᵍ
  -- ctx-

  join-in-ctx<ᵍ : (k : elᵒ keyᵍ) → Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k → Maybe valueᵍ → Maybe valueᵍ → Maybe valueᵍ
  join-in-ctx<ᵍ k ctx1 ctx2 ctx-j v1 v2 =
    maybe-join (joinᵍ k ctx-j)
      (maybe->>= v1 (transportᵍ k ctx1 ctx-j))
      (maybe->>= v2 (transportᵍ k ctx2 ctx-j))

  ctx<-joinᵍ : (k : elᵒ keyᵍ) → Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k
  ctx<-joinᵍ = inductionᵒ keyᵍ (λ k → Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k)
    (λ k ind ctx1 ctx2 k' →
      let ctx1' = ctx<-filter-<ᵍ (fst k') ctx1
          ctx2' = ctx<-filter-<ᵍ (fst k') ctx2
          ctx-j = ind k' ctx1' ctx2'
      in join-in-ctx<ᵍ (fst k') ctx1' ctx2' ctx-j (ctx1 k') (ctx2 k'))

  ctx-joinᵍ : Ctxᵍ → Ctxᵍ → Ctxᵍ
  ctx-joinᵍ ctx1 ctx2 k =
    let ctx1' = ctx-filter-<ᵍ (fst k) ctx1
        ctx2' = ctx-filter-<ᵍ (fst k) ctx2
        ctx-j = ctx<-joinᵍ k ctx1' ctx2'
    in join-in-ctx<ᵍ (fst k) ctx1' ctx2' ctx-j (ctx1 k) (ctx2 k)


  field
    join-is-elemᵍ : (k : elᵒ keyᵍ) → (ctx : Ctx<ᵍ k) → ctx<-are-elemsᵍ ctx →
      (v1 v2 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 →
      is-elemᵍ k ctx (joinᵍ k ctx v1 v2)

    join-commutᵍ : (k : elᵒ keyᵍ) → (ctx : Ctx<ᵍ k) → ctx<-are-elemsᵍ ctx →
      (v1 v2 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 →
      joinᵍ k ctx v1 v2 ≡ joinᵍ k ctx v2 v1

    join-assocᵍ : (k : elᵒ keyᵍ) → (ctx : Ctx<ᵍ k) → ctx<-are-elemsᵍ ctx →
      (v1 v2 v3 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 → is-elemᵍ k ctx v3 →
      joinᵍ k ctx (joinᵍ k ctx v1 v2) v3 ≡ joinᵍ k ctx v1 (joinᵍ k ctx v2 v3)

    join-idemᵍ : (k : elᵒ keyᵍ) → (ctx : Ctx<ᵍ k) → ctx<-are-elemsᵍ ctx →
      (v : valueᵍ) → is-elemᵍ k ctx v →
      joinᵍ k ctx v v ≡ v

    tr-is-elemᵍ : (k : elᵒ keyᵍ) → (ctx1 ctx2 : Ctx<ᵍ k) →
      ctx<-are-elemsᵍ ctx1 → ctx<-are-elemsᵍ ctx2 → ctx<-≤ᵍ ctx1 ctx2 →
      (v : valueᵍ) → is-elemᵍ k ctx1 v →
      case transportᵍ k ctx1 ctx2 v of
        λ { nothing → Unit;
            (just v') → is-elemᵍ k ctx2 v' }

    tr-idᵍ : (k : elᵒ keyᵍ) → (ctx : Ctx<ᵍ k) →
      ctx<-are-elemsᵍ ctx →
      (v : valueᵍ) → is-elemᵍ k ctx v →
      transportᵍ k ctx ctx v ≡ just v

    tr-transᵍ : (k : elᵒ keyᵍ) → (ctx1 ctx2 ctx3 : Ctx<ᵍ k) →
      ctx<-are-elemsᵍ ctx1 → ctx<-are-elemsᵍ ctx2 → ctx<-are-elemsᵍ ctx3 →
      ctx<-≤ᵍ ctx1 ctx2 → ctx<-≤ᵍ ctx2 ctx3 →
      (v : valueᵍ) → is-elemᵍ k ctx1 v →
      case transportᵍ k ctx1 ctx2 v of
        λ { nothing → nothing ≡ transportᵍ k ctx1 ctx3 v;
            (just v') → transportᵍ k ctx2 ctx3 v' ≡ transportᵍ k ctx1 ctx3 v }

  
      

  -- elemᵍ : elᵒ keyᵍ → (elᵒ keyᵍ → Maybe valueᵍ) → Type
  -- elemᵍ k ctx = Σ valueᵍ (is-elemᵍ k ctx)
