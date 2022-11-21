{-# OPTIONS --cubical --guardedness #-}

module graph where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

maybe-satisfies : {T : Type} → (T → Bool) → Maybe T → Bool
maybe-satisfies _ nothing = true
maybe-satisfies pred (just x) = pred x

Σ-≡-intro :
  ∀ {α}{A : Set α}{B : A → Set α} {a a' : A} {b : B a} {b' : B a'}
  → (Σ (a ≡ a') λ p → PathP (λ i → B (p i)) b b') → (a , b) ≡ (a' , b')

Σ-≡-intro eqs =
  cong₂ (λ c c' → (c , c'))
    (fst eqs)
    (snd eqs)

data IsTrue : Bool → Type where
  is-true : IsTrue true

false-isnt-true : {T : Type} → IsTrue false → T
false-isnt-true ()

false-neq-true : {T : Type} → false ≡ true → T
false-neq-true ft = false-isnt-true (transport (cong IsTrue (sym ft)) is-true)

record TotalOrder (T : Type) : Type where
  field
    _≤ᵗ_ : T → T → Bool
    reflᵗ : {x : T} → x ≤ᵗ x ≡ true
    transᵗ : {x y z : T} → x ≤ᵗ y ≡ true → y ≤ᵗ z ≡ true → x ≤ᵗ z ≡ true
    antisymmᵗ : {x y : T} → x ≤ᵗ y ≡ true → y ≤ᵗ x ≡ true → x ≡ y
    connectedᵗ : (x y : T) → x ≤ᵗ y ≡ true ⊎ y ≤ᵗ x ≡ true

  leqᵗ : T → T → Bool
  leqᵗ = _≤ᵗ_

  gt-sym-leqᵗ : {x y : T} → x ≤ᵗ y ≡ false → y ≤ᵗ x ≡ true
  gt-sym-leqᵗ {x = x} {y = y} x>y with connectedᵗ x y
  ... | inj₁ x≤y = false-neq-true (sym x>y ∙ x≤y)
  ... | inj₂ y≤x = y≤x

  maxᵗ : T → T → T
  maxᵗ x y = if leqᵗ x y then y else x

  minᵗ : T → T → T
  minᵗ x y = if leqᵗ x y then x else y

  max-symᵗ : {x y : T} → maxᵗ x y ≡ maxᵗ y x
  max-symᵗ {x = x} {y = y} with inspec (leqᵗ x y)
  ... | false with≡ x>y = (if x ≤ᵗ y then y else x)
                          ≡⟨ cong (λ x≤y → if x≤y then y else x) x>y ⟩
                          x
                          ≡⟨ sym (cong (λ y≤x → if y≤x then x else y) (gt-sym-leqᵗ x>y)) ⟩
                          (if y ≤ᵗ x then x else y)
                          ∎
  ... | true with≡ x≤y with inspec (leqᵗ y x)
  ...   | false with≡ y>x = (if x ≤ᵗ y then y else x)
                            ≡⟨ cong (λ x≤y → if x≤y then y else x) x≤y ⟩
                            y
                            ≡⟨ cong (λ y≤x → if y≤x then x else y) (sym y>x) ⟩
                            (if y ≤ᵗ x then x else y)
                            ∎
  ...   | true with≡ y≤x = let x=y = antisymmᵗ x≤y y≤x
                           in (if x ≤ᵗ y then y else x)
                              ≡⟨ cong (λ x' → if x' ≤ᵗ y then y else x') x=y ⟩
                              (if y ≤ᵗ y then y else y)
                              ≡⟨ cong (λ y' → if y ≤ᵗ y' then y' else y) (sym x=y) ⟩
                              (if y ≤ᵗ x then x else y)
                              ∎
                           
                           

  leq-maxᵗ : {x y : T} → x ≤ᵗ maxᵗ x y ≡ true
  leq-maxᵗ {x = x} {y = y} with inspec (leqᵗ x y)
  ... | true with≡ leq = transport (cong (λ xy → x ≤ᵗ (if xy then y else x) ≡ true) (sym leq)) leq
  ... | false with≡ gt = transport (cong (λ xy → x ≤ᵗ (if xy then y else x) ≡ true) (sym gt)) reflᵗ

open TotalOrder


maybe-order : {T : Type} → TotalOrder T → TotalOrder (Maybe T)

_≤ᵗ_ (maybe-order ord) nothing _ = true
_≤ᵗ_ (maybe-order ord) (just _) nothing = false
_≤ᵗ_ (maybe-order ord) (just x) (just y) = leqᵗ ord x y

reflᵗ (maybe-order ord) {x = nothing} = refl
reflᵗ (maybe-order ord) {x = just v} = reflᵗ ord

transᵗ (maybe-order ord) {x = nothing} _ _ = refl
transᵗ (maybe-order ord) {x = just _} {y = nothing} {z = nothing} xy _ = xy
transᵗ (maybe-order ord) {x = just _} {y = nothing} {z = just _} xy _ = false-neq-true xy
transᵗ (maybe-order ord) {x = just _} {y = just _} {z = nothing} _ yz = yz
transᵗ (maybe-order ord) {x = just x'} {y = just y'} {z = just z'} xy yz = transᵗ ord xy yz

antisymmᵗ (maybe-order ord) {x = nothing} {y = nothing} _ _ = refl
antisymmᵗ (maybe-order ord) {x = nothing} {y = just _} _ yz = false-neq-true yz
antisymmᵗ (maybe-order ord) {x = just _} {y = nothing} xy _ = false-neq-true xy
antisymmᵗ (maybe-order ord) {x = just _} {y = just _} xy yz = cong just (antisymmᵗ ord xy yz)

Type-≤ : {T : Type} → (ord : TotalOrder T) → T → Type
Type-≤ {T} ord x = Σ T (λ y → leqᵗ ord y x ≡ true)

Type-maybe-> : {T : Type} → (ord : TotalOrder T) → Maybe T → Type
Type-maybe-> {T} ord k = Σ T (λ k' → maybe-satisfies (λ k'' → not (leqᵗ ord k' k'')) k ≡ true)

record SemiL (L : Type) : Type where
  field
    _∨ˢ_ : L → L → L
    commˢ : (x y : L) → x ∨ˢ y ≡ y ∨ˢ x
    assocˢ : (x y z : L) → (x ∨ˢ y) ∨ˢ z ≡ x ∨ˢ (y ∨ˢ z)
    idemˢ : (x : L) → x ∨ˢ x ≡ x

  joinˢ : L → L → L
  joinˢ = _∨ˢ_

  compeqˢ : (x y z : L) → (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z)) ≡ x ∨ˢ (y ∨ˢ z)
  compeqˢ x y z =
    (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z))
    ≡⟨ cong (joinˢ (x ∨ˢ y)) (assocˢ x y z ⁻¹) ⟩
    (x ∨ˢ y) ∨ˢ ((x ∨ˢ y) ∨ˢ z)
    ≡⟨ assocˢ (x ∨ˢ y) (x ∨ˢ y) z ⁻¹ ⟩
    ((x ∨ˢ y) ∨ˢ (x ∨ˢ y)) ∨ˢ z
    ≡⟨ cong (λ a → a ∨ˢ z) (idemˢ (x ∨ˢ y)) ⟩
    (x ∨ˢ y) ∨ˢ z
    ≡⟨ assocˢ x y z ⟩
    x ∨ˢ (y ∨ˢ z)
    ∎

open SemiL

onepointˢ : SemiL Unit
_∨ˢ_ onepointˢ tt tt = tt
commˢ onepointˢ x y = λ i → tt
assocˢ onepointˢ x y z = λ i → tt
idemˢ onepointˢ x = refl

maybeˢ : {L : Type} → SemiL L → SemiL (Maybe L)

_∨ˢ_ (maybeˢ s) nothing y = y
_∨ˢ_ (maybeˢ s) x nothing = x
_∨ˢ_ (maybeˢ s) (just x) (just y) = just (joinˢ s x y)

commˢ (maybeˢ s) nothing nothing = refl
commˢ (maybeˢ s) nothing (just _) = refl
commˢ (maybeˢ s) (just _) nothing = refl
commˢ (maybeˢ s) (just x) (just y) = cong just (commˢ s x y)

assocˢ (maybeˢ s) nothing _ _ = refl
assocˢ (maybeˢ s) (just _) nothing _ = refl
assocˢ (maybeˢ s) (just _) (just _) nothing = refl
assocˢ (maybeˢ s) (just x) (just y) (just z) = cong just (assocˢ s x y z)

idemˢ (maybeˢ s) nothing = refl
idemˢ (maybeˢ s) (just x) = cong just (idemˢ s x)

record SemiLᵈ {L : Type} (S : SemiL L) (D : L → Type) : Type where
  field

    semilᵈ : (l : L) → SemiL (D l)

    trᵈ : {x y : L} (x' : D x) → D (joinˢ S x y)

    idᵈ : {x : L} (x' : D x) → PathP (λ i → D (idemˢ S x i)) (trᵈ x') x'

    compᵈ : {x y z : L} (x' : D x) →
      PathP (λ i → D (compeqˢ S x y z i)) (trᵈ (trᵈ x')) (trᵈ x') 

    distrᵈ : {x y : L} (x' x'' : D x) →
      trᵈ (joinˢ (semilᵈ x) x' x'') ≡ joinˢ (semilᵈ (joinˢ S x y)) (trᵈ x') (trᵈ x'')

--   trcommᵈ : {x y : L L} → L (semilᵈ (joinˢ L x y)) → L (semilᵈ (joinˢ L y x))
--   trcommᵈ {x} {y} = transport (ap (λ e → L (semilᵈ e)) (commˢ L x y))
--   
--   trrᵈ : {x y : L L} (y' : L (semilᵈ y)) → L (semilᵈ (joinˢ L x y))
--   trrᵈ = trcommᵈ ∘ trᵈ
-- 
-- 
-- open SemiLᵈ
-- 
-- Σ-SemiL : (ℒ : SemiL ℓ₁) (ℳ : SemiLᵈ ℒ ℓ₂) → SemiL (ℓ₁ ⊔ ℓ₂)
-- elˢ (Σ-SemiL ℒ ℳ) = Σ (elˢ ℒ) (elˢ ∘ semilᵈ ℳ)
-- _∨ˢ_ (Σ-SemiL ℒ ℳ) (x , α) (y , β) = joinˢ ℒ x y , joinˢ (semilᵈ ℳ (joinˢ ℒ x y)) (trᵈ ℳ α) (trcommᵈ ℳ (trᵈ ℳ β)) 
-- commˢ (Σ-SemiL ℒ ℳ) = {!!}
-- assocˢ (Σ-SemiL ℒ ℳ) = {!!}
-- idemˢ (Σ-SemiL ℒ ℳ) = {!!}

record CtxTyStr {K : Type} (kOrd : TotalOrder K) (k : Maybe K) : Type₁ where
-- all new keys must be greater than k
  coinductive
  field
    ty : Type-maybe-> kOrd k → Type
    ex : (k' : Type-maybe-> kOrd k) → ty k' → CtxTyStr kOrd (just (fst k'))

mutual

  data Ctx {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) : Maybe K → Type where
    -- `Maybe k` argument is the greatest, last key in the context
    nullᶜ : Ctx kOrd ts nothing
    rconsᶜ : {k : Maybe K} → (c : Ctx kOrd ts k) → (k' : Type-maybe-> kOrd k) → (el : CtxTyStr.ty (exs ts c) k') → Ctx kOrd ts (just (fst k'))

  exs : {K : Type} {kOrd : TotalOrder K} {k : Maybe K} → (ts : CtxTyStr kOrd nothing) → Ctx kOrd ts k → CtxTyStr kOrd k
  exs ts nullᶜ = ts
  exs ts (rconsᶜ c k' el) = CtxTyStr.ex (exs ts c) k' el

record Ctx-promoted {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) (k : Maybe K) : Type where
  field
    keyᵖ : Maybe K
    baseᵖ : Ctx kOrd ts keyᵖ
    key-cmpᵖ : leqᵗ (maybe-order kOrd) keyᵖ k ≡ true

open Ctx-promoted


semilᶜ : {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) (k : Maybe K) → SemiL (Ctx-promoted kOrd ts k)
_∨ˢ_ (semilᶜ kOrd ts k) p1 p2 with (baseᵖ p1)
... | nullᶜ = p2
... | rconsᶜ {k = k1} c1 k1' el1 with (baseᵖ p2)
...   | nullᶜ = p1
...   | rconsᶜ {k = k2} c2 k2' el2  with inspec (leqᵗ kOrd (fst k1') (fst k2'))
...     | false with≡ eq1 = let k3 = maxᵗ (maybe-order kOrd) k1 (just (fst k2'))
                                p1' = record {keyᵖ = k1; baseᵖ = c1; key-cmpᵖ = leq-maxᵗ (maybe-order kOrd)}
                                p2' = record {keyᵖ = just (fst k2'); baseᵖ = baseᵖ p2; key-cmpᵖ = {!!}}
                                rest = rconsᶜ (baseᵖ (joinˢ (semilᶜ kOrd ts k3) p1' p2')) (fst k1' , {!!}) {!!}
                            in record {keyᵖ = just (fst k1'); baseᵖ = rest; key-cmpᵖ = {!!}}

Context : {K : Type} → TotalOrder K → Type → K → Type
Context kOrd V k = Type-≤ kOrd k → Maybe V

demote-context : {K : Type} {kOrd : TotalOrder K} {V : Type} {k : K} → (c : Context kOrd V k) → (k' : Type-≤ kOrd k) → Context kOrd V (fst k')
demote-context {kOrd = kOrd} c k' k'' = c (fst k'' , transᵗ kOrd (snd k'') (snd k'))


record SemiLGraph (K : Type) (kOrd : TotalOrder K) (V : Type) : Type where

  field
    check-elemᵍ : (k : K) → Context kOrd V k → V → Bool


  elemᵍ : (k : K) → Context kOrd V k → Type
  elemᵍ k c = Σ V (λ v → check-elemᵍ k c v ≡ true)

  check-maybe-elemᵍ : (k : K) → Context kOrd V k → Maybe V → Bool
  check-maybe-elemᵍ k c = maybe-satisfies (check-elemᵍ k c)

  -- Contextᵍ : K → Type
  -- Contextᵍ k = Σ (Context kOrd V k) (λ c → (k' : Type-≤ kOrd k) → check-maybe-elemᵍ k c 

  field
    semilᵍ : (k : K) → (c : Context kOrd V k) → SemiL (elemᵍ k c)
    trᵍ : (k : K) → (c1 c2 : Context kOrd V k) → (v : elemᵍ k c1) → Maybe (elemᵍ k c2)

  context-semilᵍ : (k : K) → SemiL (Context kOrd V k)
  _∨ˢ_ (context-semilᵍ k) c1 c2 k' =
    let v = joinˢ (maybeˢ (semilᵍ {!!} {!!})) {!!} {!!} in {!!} -- k' (joinˢ (context-semilᵍ k) c1 c2))) ? ?



