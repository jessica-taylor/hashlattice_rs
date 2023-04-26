
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

botL-elim : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₂} → BotL ℓ₁ → A
botL-elim ()

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

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

-- record SemiLat {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
--   field
--     partialˢ : PartialOrder ℓ₂ S
--     joinˢ : S → S → S
-- 
--   leqˢ = leqᵖ partialˢ
-- 
--   field
--     left≤joinˢ : (x y : S) → leqˢ x (joinˢ x y)
--     right≤joinˢ : (x y : S) → leqˢ y (joinˢ x y)
--     join-lubˢ : (x y z : S) → leqˢ x z → leqˢ y z → leqˢ (joinˢ x y) z
-- 
-- open SemiLat

record PreSemiLat {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ lsuc ℓ₂) where
  field
    is-elemˢ : S → Type ℓ₂
    leqˢ : S → S → Type ℓ₂
    joinˢ : S → S → S
    bottomˢ : S

open PreSemiLat

record SemiLat {ℓ₁ ℓ₂} {S : Type ℓ₁} (PS : PreSemiLat ℓ₂ S) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    leq-propˢ : (x y : S) → is-elemˢ PS x → is-elemˢ PS y → isProp (leqˢ PS x y)
    join-elemˢ : (x y : S) → is-elemˢ PS x → is-elemˢ PS y → is-elemˢ PS (joinˢ PS x y)
    bottom-elemˢ : is-elemˢ PS (bottomˢ PS)
    reflˢ : (x : S) → is-elemˢ PS x → leqˢ PS x x
    transˢ : (x y z : S) → is-elemˢ PS x → is-elemˢ PS y → is-elemˢ PS z → leqˢ PS x y → leqˢ PS y z → leqˢ PS x z
    antisymmˢ : (x y : S) → is-elemˢ PS x → is-elemˢ PS y → leqˢ PS x y → leqˢ PS y x → x ≡ y
    left≤joinˢ : (x y : S) → is-elemˢ PS x → is-elemˢ PS y → leqˢ PS x (joinˢ PS x y)
    right≤joinˢ : (x y : S) → is-elemˢ PS x → is-elemˢ PS y → leqˢ PS y (joinˢ PS x y)
    join-lubˢ : (x y z : S) → is-elemˢ PS x → is-elemˢ PS y → is-elemˢ PS z → leqˢ PS x z → leqˢ PS y z → leqˢ PS (joinˢ PS x y) z
    bottom-minˢ : (x : S) → is-elemˢ PS x → leqˢ PS (bottomˢ PS) x
    
record SemiMor {ℓ₁ ℓ₂} {S1 S2 : Type ℓ₁} (PS1 : PreSemiLat ℓ₂ S1) (PS2 : PreSemiLat ℓ₂ S2) (f : S1 → S2) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    ap-elemᵐ : (x : S1) → is-elemˢ PS2 (f x)
    join-distrᵐ : (x y : S1) → is-elemˢ PS1 x → is-elemˢ PS1 y → f (joinˢ PS1 x y) ≡ joinˢ PS2 (f x) (f y)
    

is-or-nothing : {ℓ₁ ℓ₂ : Level} {S : Type ℓ₁} → (S → Type ℓ₂) → Maybe S → Type ℓ₂
is-or-nothing {ℓ₂ = ℓ₂} _ nothing = UnitL ℓ₂
is-or-nothing pred (just x) = pred x

record PreSemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} (KT : TotalOrder ℓ₂ K) (V : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    pre-semiᵍ : K → (K → Maybe V) → PreSemiLat ℓ₂ V
    trᵍ : (k : K) → (K → Maybe V) → (K → Maybe V) → V → V

  is-elemᵍ : K → (K → Maybe V) → V → Type ℓ₂
  is-elemᵍ k ctx = is-elemˢ (pre-semiᵍ k ctx)

  leqᵍ : K → (K → Maybe V) → V → V → Type ℓ₂
  leqᵍ k ctx = leqˢ (pre-semiᵍ k ctx)

  joinᵍ : K → (K → Maybe V) → V → V → V
  joinᵍ k ctx = joinˢ (pre-semiᵍ k ctx)

  bottomᵍ : K → (K → Maybe V) → V
  bottomᵍ k ctx = bottomˢ (pre-semiᵍ k ctx)

  maybe-is-elemᵍ : K → (K → Maybe V) → Maybe V → Type ℓ₂
  maybe-is-elemᵍ k ctx = is-or-nothing (is-elemᵍ k ctx)

  is-ctxᵍ : (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  is-ctxᵍ ctx = (k : K) → maybe-is-elemᵍ k ctx (ctx k)

  maybe-leqᵍ : (k : K) → (ctx : K → Maybe V) → Maybe V → Maybe V → Type ℓ₂
  maybe-leqᵍ _ _ nothing _ = UnitL ℓ₂
  maybe-leqᵍ _ _ (just _) nothing = BotL ℓ₂
  maybe-leqᵍ k ctx (just x) (just y) = leqᵍ k ctx x y

  maybe-trᵍ : K → (K → Maybe V) → (K → Maybe V) → Maybe V → Maybe V
  maybe-trᵍ _ _ _ nothing = nothing
  maybe-trᵍ k ctx1 ctx2 (just v) = just (trᵍ k ctx1 ctx2 v)

  ctx≤ᵍ : (K → Maybe V) → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  ctx≤ᵍ ctx1 ctx2 = (k : K) → maybe-leqᵍ k ctx2 (maybe-trᵍ k ctx1 ctx2 (ctx1 k)) (ctx2 k)

open PreSemiGraph

record SemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} {KT : TotalOrder ℓ₂ K} {V : Type ℓ₁} (PG : PreSemiGraph KT V) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    semiᵍ : (k : K) → (ctx : K → Maybe V) → is-ctxᵍ PG ctx → SemiLat (pre-semiᵍ PG k ctx)
    tr-morᵍ : (k : K) → (ctx1 ctx2 : K → Maybe V) → is-ctxᵍ PG ctx1 → is-ctxᵍ PG ctx2 → ctx≤ᵍ PG ctx1 ctx2 → SemiMor (pre-semiᵍ PG k ctx1) (pre-semiᵍ PG k ctx2) (trᵍ PG k ctx1 ctx2)
    tr-reflᵍ : (k : K) → (ctx : K → Maybe V) → is-ctxᵍ PG ctx → (v : V) → is-elemᵍ PG k ctx v → trᵍ PG k ctx ctx v ≡ v


-- record SemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} (KT : TotalOrder ℓ₂ K) (V : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
--   field
--     is-elemᵍ : K → (K → Maybe V) → V → Type ℓ₂
--     leqᵍ : K → (K → Maybe V) → V → V → Type ℓ₂
--     joinᵍ : K → (K → Maybe V) → V → V → V
--     bottomᵍ : K → (K → Maybe V) → V
--     trᵍ : (k : K) → (K → Maybe V) → (K → Maybe V) → V → V
-- 
--   maybe-is-elemᵍ : K → (K → Maybe V) → Maybe V → Type ℓ₂
--   maybe-is-elemᵍ k ctx = is-or-nothing (is-elemᵍ k ctx)
-- 
--   elemᵍ : K → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
--   elemᵍ k ctx = Σ V (is-elemᵍ k ctx)
-- 
--   -- leq-elemᵍ : (k : K) → (ctx : K → Maybe V) → elemᵍ k ctx → elemᵍ k ctx → Type ℓ₂
--   -- leq-elemᵍ k ctx x y = leqᵍ k ctx (fst x) (fst y)
-- 
--   maybe-leqᵍ : (k : K) → (ctx : K → Maybe V) → Maybe V → Maybe V → Type ℓ₂
--   maybe-leqᵍ _ _ nothing _ = UnitL ℓ₂
--   maybe-leqᵍ _ _ (just _) nothing = BotL ℓ₂
--   maybe-leqᵍ k ctx (just x) (just y) = leqᵍ k ctx x y
-- 
--   maybe-trᵍ : K → (K → Maybe V) → (K → Maybe V) → Maybe V → Maybe V
--   maybe-trᵍ _ _ _ nothing = nothing
--   maybe-trᵍ k ctx1 ctx2 (just v) = just (trᵍ k ctx1 ctx2 v)
-- 
--   is-ctxᵍ : (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
--   is-ctxᵍ ctx = (k : K) → maybe-is-elemᵍ k ctx (ctx k)
-- 
--   Ctxᵍ : Type (ℓ₁ ⊔ ℓ₂)
--   Ctxᵍ = Σ (K → Maybe V) is-ctxᵍ
-- 
--   ctx-lookupᵍ : (k : K) → (ctx : Ctxᵍ) → Maybe (elemᵍ k (fst ctx))
--   ctx-lookupᵍ k (ctx , is-ctx) with ctx k | is-ctx k
--   ... | nothing | _ = nothing
--   ... | just v | v-is = just (v , v-is)
-- 
--   ctx≤ᵍ : (K → Maybe V) → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
--   ctx≤ᵍ ctx1 ctx2 = (k : K) → maybe-leqᵍ k ctx2 (maybe-trᵍ k ctx1 ctx2 (ctx1 k)) (ctx2 k)
-- 
-- 
-- open SemiGraph
-- 
-- record IsSemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} {KT : TotalOrder ℓ₂ K} {V : Type ℓ₁} (G : SemiGraph KT V) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
-- 
--   field
--     -- semilⁱ : (k : K) → (ctx : Ctxᵍ G) → IsSemiLat (is-elemᵍ G k (fst ctx)) (leqᵍ G k (fst ctx)) (joinᵍ G k (fst ctx)) (bottomᵍ G k (fst ctx))
--     leq-propⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → isProp (leqᵍ G k (fst ctx) (fst x) (fst y))
--     leq-reflⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst x)
--     leq-transⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y z : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst y) → leqᵍ G k (fst ctx) (fst y) (fst z) → leqᵍ G k (fst ctx) (fst x) (fst z)
--     leq-antisymmⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst y) → leqᵍ G k (fst ctx) (fst y) (fst x) → x ≡ y
--     join-is-elemⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → is-elemᵍ G k (fst ctx) (joinᵍ G k (fst ctx) (fst x) (fst y))
--     bot-is-elemⁱ : (k : K) → (ctx : Ctxᵍ G) → is-elemᵍ G k (fst ctx) (bottomᵍ G k (fst ctx))
--     left≤joinⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (joinᵍ G k (fst ctx) (fst x) (fst y))
--     right≤joinⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst y) (joinᵍ G k (fst ctx) (fst x) (fst y))
--     join-lubⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y z : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst z) → leqᵍ G k (fst ctx) (fst y) (fst z) → leqᵍ G k (fst ctx) (joinᵍ G k (fst ctx) (fst x) (fst y)) (fst z)
--     bot≤ⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (bottomᵍ G k (fst ctx)) (fst x)
--     tr-is-elemⁱ : (k : K) → (ctx1 ctx2 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → (x : elemᵍ G k (fst ctx1)) → is-elemᵍ G k (fst ctx2) (trᵍ G k (fst ctx1) (fst ctx2) (fst x))
--     tr-joinⁱ : (k : K) → (ctx1 ctx2 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → (x y : elemᵍ G k (fst ctx1)) → trᵍ G k (fst ctx1) (fst ctx2) (joinᵍ G k (fst ctx1) (fst x) (fst y)) ≡ joinᵍ G k (fst ctx2) (trᵍ G k (fst ctx1) (fst ctx2) (fst x)) (trᵍ G k (fst ctx1) (fst ctx2) (fst y))
--     tr-reflⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → trᵍ G k (fst ctx) (fst ctx) (fst x) ≡ fst x
--     tr-transⁱ : (k : K) → (ctx1 ctx2 ctx3 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → ctx≤ᵍ G (fst ctx2) (fst ctx3) → (x : elemᵍ G k (fst ctx1)) → trᵍ G k (fst ctx2) (fst ctx3) (trᵍ G k (fst ctx1) (fst ctx2) (fst x)) ≡ trᵍ G k (fst ctx1) (fst ctx3) (fst x)

  -- joinⁱ : (k : K) → (ctx : Ctxᵍ G) → elemᵍ G k (fst ctx) → elemᵍ G k (fst ctx) → elemᵍ G k (fst ctx)
  -- joinⁱ k ctx x y = (joinᵍ G k (fst ctx) (fst x) (fst y) , join-is-elemⁱ k ctx x y)

  -- bottomⁱ : (k : K) → (ctx : Ctxᵍ G) → elemᵍ G k (fst ctx)
  -- bottomⁱ k ctx = (bottomᵍ G k (fst ctx) , bot-is-elemⁱ k ctx)

  -- tr-monotoneⁱ : (k : K) → (ctx1 ctx2 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → (x y : elemᵍ G k (fst ctx1)) → leqᵍ G k (fst ctx1) (fst x) (fst y) → leqᵍ G k (fst ctx2) (trᵍ G k (fst ctx1) (fst ctx2) (fst x)) (trᵍ G k (fst ctx1) (fst ctx2) (fst y))
  -- tr-monotoneⁱ k ctx1 ctx2 1≤2 x y x≤y = {!!}

  -- ctx≤-reflⁱ : (ctx : Ctxᵍ G) → ctx≤ᵍ G (fst ctx) (fst ctx)
  -- ctx≤-reflⁱ ctx k with fst ctx k | inspect (fst ctx) k | snd ctx k
  -- ... | nothing | [ _ ]ᵢ | _ = <>
  -- ... | just v | [ _ ]ᵢ | v-elem = transport (cong (λ v' → leqᵍ G k (fst ctx) v' v) (sym (tr-reflⁱ k ctx (v , v-elem)))) (leq-reflⁱ k ctx (v , v-elem))

  -- ctx≤-transⁱ : (ctx1 ctx2 ctx3 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → ctx≤ᵍ G (fst ctx2) (fst ctx3) → ctx≤ᵍ G (fst ctx1) (fst ctx3)
  -- ctx≤-transⁱ ctx1 ctx2 ctx3 1≤2 2≤3 k with fst ctx1 k | snd ctx1 k | fst ctx2 k | snd ctx2 k | fst ctx3 k | snd ctx3 k | 1≤2 k | 2≤3 k
  -- ... | nothing | _ | _ | _ | _ | _ | _ | _ = <>
  -- ... | just v1 | _ | nothing | _ | _ | _ | v1≤2 | _ = botL-elim v1≤2
  -- ... | just v1 | _ | just v2 | _ | nothing | _ | _ | v2≤3 = v2≤3
  -- ... | just v1 | v1-elem | just v2 | v2-elem | just v3 | v3-elem | v1≤2 | v2≤3 = {!!}

  

