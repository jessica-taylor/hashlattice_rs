
{-# OPTIONS --cubical --guardedness #-}

module leq-graph where

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

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data UnitL ℓ : Set ℓ where
  <> : UnitL ℓ

data BotL ℓ : Set ℓ where


record PartialOrder {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    leqᵖ : S → S → Type ℓ₂
    leq-propᵖ : (x y : S) → isProp (leqᵖ x y)
    reflᵖ : (x : S) → leqᵖ x x
    transᵖ : (x y z : S) → leqᵖ x y → leqᵖ y z → leqᵖ x z
    antisymmᵖ : (x y : S) → leqᵖ x y → leqᵖ y x → x ≡ y

open PartialOrder

record TotalOrder {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    partialᵗ : PartialOrder ℓ₂ S

  leqᵗ = leqᵖ partialᵗ

  field
    completeᵗ : (x y : S) → leqᵗ x y ⊎ leqᵗ y x

open TotalOrder

record SemiLat {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    partialˢ : PartialOrder ℓ₂ S
    joinˢ : S → S → S

  leqˢ = leqᵖ partialˢ

  field
    left≤joinˢ : (x y : S) → leqˢ x (joinˢ x y)
    right≤joinˢ : (x y : S) → leqˢ y (joinˢ x y)
    join-lubˢ : (x y z : S) → leqˢ x z → leqˢ y z → leqˢ (joinˢ x y) z

open SemiLat

is-or-nothing : {ℓ₁ ℓ₂ : Level} {S : Type ℓ₁} → (S → Type ℓ₂) → Maybe S → Type ℓ₂
is-or-nothing {ℓ₂ = ℓ₂} _ nothing = UnitL ℓ₂
is-or-nothing pred (just x) = pred x

record SemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} (KT : TotalOrder ℓ₂ K) (V : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    is-elemᵍ : K → (K → Maybe V) → V → Type ℓ₂

  maybe-is-elemᵍ : K → (K → Maybe V) → Maybe V → Type ℓ₂
  maybe-is-elemᵍ k ctx = is-or-nothing (is-elemᵍ k ctx)

  elemᵍ : K → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  elemᵍ k ctx = Σ V (is-elemᵍ k ctx)

  field
    semilᵍ : (k : K) → (ctx : K → Maybe V) → SemiLat ℓ₂ (elemᵍ k ctx)
    trᵍ : (k : K) → (ctx1 ctx2 : K → Maybe V) → V → V

  maybe-leqᵍ : (k : K) → (ctx : K → Maybe V) → Maybe (elemᵍ k ctx) → Maybe (elemᵍ k ctx) → Type ℓ₂
  maybe-leqᵍ _ _ nothing nothing = UnitL ℓ₂
  maybe-leqᵍ _ _ nothing (just _) = UnitL ℓ₂
  maybe-leqᵍ _ _ (just _) nothing = BotL ℓ₂
  maybe-leqᵍ k ctx (just x) (just y) = leqˢ (semilᵍ k ctx) x y

  is-ctxᵍ : (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  is-ctxᵍ ctx = (k : K) → maybe-is-elemᵍ k ctx (ctx k)

  Ctxᵍ : Type (ℓ₁ ⊔ ℓ₂)
  Ctxᵍ = Σ (K → Maybe V) is-ctxᵍ

  ctx-lookup : (k : K) → (ctx : Ctxᵍ) → Maybe (elemᵍ k (fst ctx))
  ctx-lookup k (ctx , is-ctx) with ctx k | is-ctx k
  ... | nothing | _ = nothing
  ... | just v | v-is = just (v , v-is)

  ctx-leqᵍ : Ctxᵍ → Ctxᵍ → Type (ℓ₁ ⊔ ℓ₂)
  ctx-leqᵍ ctx1 ctx2 = (k : K) → maybe-leqᵍ k (fst ctx2) {!!} (ctx-lookup k ctx2)

  -- problem: ctx-leqᵍ depends on trᵍ, however the type of trᵍ depends on ctx-leqᵍ

  -- ctx-leqᵍ : (K → Maybe V) → (K → Maybe V) → Type ℓ
  -- ctx-leqᵍ ctx1 ctx2 = (k : K) → {!leqˢ (semilᵍ k ctx2) ? (!}
