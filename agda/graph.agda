{-# OPTIONS --cubical --guardedness #-}

module graph where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Base using (_×_) public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data UnitL ℓ : Set ℓ where
  <> : UnitL ℓ

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

maybe-satisfies : {T : Type} → (T → Bool) → Maybe T → Bool
maybe-satisfies _ nothing = true
maybe-satisfies pred (just x) = pred x

Σ-≡-intro : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {a a' : A} {b : B a} {b' : B a'}
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

record PartialOrder ℓ : Type (lsuc ℓ) where
  field
    elᵖ : Type ℓ
    leqᵖ : elᵖ → elᵖ → Type

  _≤ᵖ_ : elᵖ → elᵖ → Type
  _≤ᵖ_ = leqᵖ

  field
    leq-propᵖ : {x y : elᵖ} → isProp (x ≤ᵖ y)
    reflᵖ : {x : elᵖ} → x ≤ᵖ x
    transᵖ : {x y z : elᵖ} → x ≤ᵖ y → y ≤ᵖ z → x ≤ᵖ z
    antisymmᵖ : {x y : elᵖ} → x ≤ᵖ y → y ≤ᵖ x → x ≡ y

open PartialOrder

record TotalOrder ℓ : Type (lsuc ℓ) where
  field
    partialᵗ : PartialOrder ℓ

  elᵗ : Type ℓ
  elᵗ = elᵖ partialᵗ

  leqᵗ : elᵗ → elᵗ → Type
  leqᵗ = leqᵖ partialᵗ

  _≤ᵗ_ : elᵗ → elᵗ → Type
  _≤ᵗ_ = leqᵗ

  leq-propᵗ : {x y : elᵗ} → isProp (x ≤ᵗ y)
  leq-propᵗ = leq-propᵖ partialᵗ

  reflᵗ : {x : elᵗ} → x ≤ᵗ x
  reflᵗ = reflᵖ partialᵗ

  transᵗ : {x y z : elᵗ} → x ≤ᵗ y → y ≤ᵗ z → x ≤ᵗ z
  transᵗ = transᵖ partialᵗ

  antisymmᵗ : {x y : elᵗ} → x ≤ᵗ y → y ≤ᵗ x → x ≡ y
  antisymmᵗ = antisymmᵖ partialᵗ

  field
    connectedᵗ : (x y : elᵗ) → x ≤ᵗ y ⊎ y ≤ᵗ x

open TotalOrder

record SemiL ℓ : Type (lsuc ℓ) where
  field
    partialˢ : PartialOrder ℓ

  elˢ : Type ℓ
  elˢ = elᵖ partialˢ
  
  leqˢ : elˢ → elˢ → Type
  leqˢ = leqᵖ partialˢ

  _≤ˢ_ : elˢ → elˢ → Type
  _≤ˢ_ = leqˢ

  leq-propˢ : {x y : elˢ} → isProp (x ≤ˢ y)
  leq-propˢ = leq-propᵖ partialˢ

  reflˢ : {x : elˢ} → x ≤ˢ x
  reflˢ = reflᵖ partialˢ

  transˢ : {x y z : elˢ} → x ≤ˢ y → y ≤ˢ z → x ≤ˢ z
  transˢ = transᵖ partialˢ

  antisymmˢ : {x y : elˢ} → x ≤ˢ y → y ≤ˢ x → x ≡ y
  antisymmˢ = antisymmᵖ partialˢ

  field
    joinˢ : elˢ → elˢ → elˢ

  _∨ˢ_ : elˢ → elˢ → elˢ
  _∨ˢ_ = joinˢ

  field
    inlˢ : (x y : elˢ) → x ≤ˢ (x ∨ˢ y)
    inrˢ : (x y : elˢ) → y ≤ˢ (x ∨ˢ y)
    glueˢ : {x y z : elˢ} → x ≤ˢ z → y ≤ˢ z → (x ∨ˢ y) ≤ˢ z
    bottomˢ : elˢ
    bottom-minˢ : {x : elˢ} → bottomˢ ≤ˢ x

  commˢ : (x y : elˢ) → x ∨ˢ y ≡ y ∨ˢ x
  commˢ x y = antisymmˢ (glueˢ (inrˢ y x) (inlˢ y x)) (glueˢ (inrˢ x y) (inlˢ x y))

  assocˢ : (x y z : elˢ) → (x ∨ˢ y) ∨ˢ z ≡ x ∨ˢ (y ∨ˢ z)
  assocˢ x y z =
    antisymmˢ (glueˢ (glueˢ (inlˢ _ _) (transˢ (inlˢ y z) (inrˢ _ _)))
                     (transˢ (inrˢ y z) (inrˢ _ _)))
              (glueˢ (transˢ (inlˢ x y) (inlˢ _ _))
                     (glueˢ (transˢ (inrˢ x y) (inlˢ _ _)) (inrˢ _ _)))

  idemˢ : (x : elˢ) → x ∨ˢ x ≡ x
  idemˢ x = antisymmˢ (glueˢ reflˢ reflˢ) (inlˢ x x)

open SemiL

onepointˢ : SemiL lzero
elᵖ (partialˢ onepointˢ) = Unit
leqᵖ (partialˢ onepointˢ) _ _ = Unit
leq-propᵖ (partialˢ onepointˢ) _ _ = refl
reflᵖ (partialˢ onepointˢ) = tt
transᵖ (partialˢ onepointˢ) _ _ = tt
antisymmᵖ (partialˢ onepointˢ) _ _ = refl
joinˢ onepointˢ _ _ = tt
inlˢ onepointˢ _ _ = tt
inrˢ onepointˢ _ _ = tt
glueˢ onepointˢ _ _ = tt
bottomˢ onepointˢ = tt
bottom-minˢ onepointˢ = tt

-- maybeˢ : {ℓ : Level} → (L : SemiL ℓ) → SemiL ℓ
-- elᵖ (partialˢ (maybeˢ L)) = Maybe (elˢ L)
-- leqᵖ (partialˢ (maybeˢ L)) nothing _ = Unit
-- leqᵖ (partialˢ (maybeˢ L)) (just _) nothing = ⊥
-- leqᵖ (partialˢ (maybeˢ L)) (just x) (just y) = leqˢ L x y
-- leq-propᵖ (partialˢ (maybeˢ L)) {x = nothing} _ _ = refl
-- leq-propᵖ (partialˢ (maybeˢ L)) {x = just _} {y = nothing} bot _ = ⊥-elim bot
-- leq-propᵖ (partialˢ (maybeˢ L)) {x = just _} {y = just _} = leq-propˢ L
-- reflᵖ (partialˢ (maybeˢ L)) {x = nothing} = tt
-- reflᵖ (partialˢ (maybeˢ L)) {x = just _} = reflˢ L
-- transᵖ (partialˢ (maybeˢ L)) {x = nothing} _ _ = tt
-- transᵖ (partialˢ (maybeˢ L)) {x = just _} {y = nothing} x≤y _ = ⊥-elim x≤y
-- transᵖ (partialˢ (maybeˢ L)) {x = just _} {y = just _} {z = nothing} _ y≤z = ⊥-elim y≤z
-- transᵖ (partialˢ (maybeˢ L)) {x = just _} {y = just _} {z = just _} x≤y y≤z = transˢ L x≤y y≤z
-- antisymmᵖ (partialˢ (maybeˢ L)) {x = nothing} {y = nothing} _ _ = refl
-- antisymmᵖ (partialˢ (maybeˢ L)) {x = nothing} {y = just _} _ y≤x = ⊥-elim y≤x
-- antisymmᵖ (partialˢ (maybeˢ L)) {x = just _} {y = nothing} x≤y _ = ⊥-elim x≤y
-- antisymmᵖ (partialˢ (maybeˢ L)) {x = just _} {y = just _} x≤y y≤x = cong just (antisymmˢ L x≤y y≤x)
-- joinˢ (maybeˢ L) nothing y = y
-- joinˢ (maybeˢ L) x nothing = x
-- joinˢ (maybeˢ L) (just x) (just y) = just (joinˢ L x y)
-- inlˢ (maybeˢ L) nothing y = tt
-- inlˢ (maybeˢ L) (just x) nothing = reflˢ L
-- inlˢ (maybeˢ L) (just x) (just y) = inlˢ L x y
-- inrˢ (maybeˢ L) x nothing = tt
-- inrˢ (maybeˢ L) nothing (just y) = reflˢ L
-- inrˢ (maybeˢ L) (just x) (just y) = inrˢ L x y
-- glueˢ (maybeˢ L) {x = nothing} _ y≤z = y≤z
-- glueˢ (maybeˢ L) {x = just _} {y = nothing} x≤z _ = x≤z
-- glueˢ (maybeˢ L) {x = just _} {y = just _} {z = nothing} x≤z _ = x≤z
-- glueˢ (maybeˢ L) {x = just _} {y = just _} {z = just _} x≤z y≤z = glueˢ L x≤z y≤z

  
record SemiLᵈ {ℓ₁} (L : SemiL ℓ₁) ℓ₂ : Type (lsuc ℓ₁ ⊔ lsuc ℓ₂) where
  field
    semilᵈ : (x : elˢ L) → SemiL ℓ₂
    trᵈ : {x y : elˢ L} → leqˢ L x y → (x' : elˢ (semilᵈ x)) → elˢ (semilᵈ y)
    idᵈ : {x : elˢ L} → (x' : elˢ (semilᵈ x)) → trᵈ (reflˢ L) x' ≡ x'
    compᵈ : {x y z : elˢ L} → (x≤y : leqˢ L x y) → (y≤z : leqˢ L y z) → (x' : elˢ (semilᵈ x)) → trᵈ y≤z (trᵈ x≤y x') ≡ trᵈ (transˢ L x≤y y≤z) x'
    distrᵈ : {x y : elˢ L} → (x≤y : leqˢ L x y) → (x' x'' : elˢ (semilᵈ x)) → trᵈ x≤y (joinˢ (semilᵈ x) x' x'') ≡ joinˢ (semilᵈ y) (trᵈ x≤y x') (trᵈ x≤y x'')
    tr-bottomᵈ : {x y : elˢ L} → (x≤y : leqˢ L x y) → trᵈ x≤y (bottomˢ (semilᵈ x)) ≡ bottomˢ (semilᵈ y)

open SemiLᵈ

-- maybeᵈ : {ℓ₁ ℓ₂ : Level} → (L : SemiL ℓ₁) → (D : SemiLᵈ L ℓ₂) → SemiLᵈ L ℓ₂
-- semilᵈ (maybeᵈ L D) x = maybeˢ (semilᵈ D x)
-- trᵈ (maybeᵈ L D) x≤y nothing = nothing

Σ-SemiL : {ℓ₁ ℓ₂ : Level} → (L : SemiL ℓ₁) → (D : SemiLᵈ L ℓ₂) → SemiL (ℓ₁ ⊔ ℓ₂)
elᵖ (partialˢ (Σ-SemiL L D)) = (Σ (elˢ L) (elˢ ∘ semilᵈ D))
leqᵖ (partialˢ (Σ-SemiL L D)) (x , x') (y , y') = Σ (leqˢ L x y) (λ x≤y → leqˢ (semilᵈ D y) (trᵈ D x≤y x') y')
leq-propᵖ (partialˢ (Σ-SemiL L D)) {y = (y , y')} = isPropΣ (leq-propˢ L) (λ l-prop → leq-propˢ (semilᵈ D y))
reflᵖ (partialˢ (Σ-SemiL L D)) {x = (x , x')} = reflˢ L , subst (λ x'' → leqˢ (semilᵈ D x) x'' x') (sym (idᵈ D x')) (reflˢ (semilᵈ D x))
transᵖ (partialˢ (Σ-SemiL L D)) {x = (x , x')} {y = (y , y')} {z = (z , z')} (x≤y , x'≤y') (y≤z , y'≤z') =
  (transˢ L x≤y y≤z , transˢ (semilᵈ D z) {!!} y'≤z')
antisymmᵖ (partialˢ (Σ-SemiL L D)) {x = (x , x')} {y = (y , y')} (x≤y , x'≤y') (y≤x , y'≤x') =
  Σ-≡-intro (antisymmˢ L x≤y y≤x , {!!})
joinˢ (Σ-SemiL L D) (x , x') (y , y') = joinˢ L x y , joinˢ (semilᵈ D (joinˢ L x y)) (trᵈ D (inlˢ L _ _) x') (trᵈ D (inrˢ L _ _) y')
inlˢ (Σ-SemiL L D) (x , x') (y , y') = (inlˢ L x y , inlˢ (semilᵈ D (joinˢ L x y)) _ _)
inrˢ (Σ-SemiL L D) (x , x') (y , y') = (inrˢ L x y , inrˢ (semilᵈ D (joinˢ L x y)) _ _)
glueˢ (Σ-SemiL L D) {x = (x , x')} {y = (y , y')} {z = (z , z')} (x≤z , x'≤z') (y≤z , y'≤z') =
  (glueˢ L x≤z y≤z , {!!})
bottomˢ (Σ-SemiL L D) = (bottomˢ L , bottomˢ (semilᵈ D (bottomˢ L)))
bottom-minˢ (Σ-SemiL L D) {x = (x , x')} = (bottom-minˢ L , subst (λ b → leqˢ (semilᵈ D x) b x') (sym (tr-bottomᵈ D (bottom-minˢ L))) (bottom-minˢ (semilᵈ D x)))

CtxArg : ℕ → Type₁
Ctx : (n : ℕ) → CtxArg n → SemiL lzero

CtxArg 0 = UnitL (lsuc lzero)
CtxArg (suc n) = Σ (CtxArg n) (λ arg → SemiLᵈ (Ctx n arg) lzero)

Ctx 0 <> = onepointˢ
Ctx (suc n) (arg-n , D) = Σ-SemiL (Ctx n arg-n) D

pair : {A B : Type₁} → A → B → A × B
pair a b = a , b

module _ (K : TotalOrder lzero) where
  mutual
    record KCtxArgSuc (n : ℕ) : Type₁ where
      inductive
      field
        key : elᵗ K
        butlast : KCtxArg n
        D : SemiLᵈ (KCtx n butlast) lzero

    KCtxArg : ℕ → Type₁
    KCtxArg 0 = UnitL (lsuc lzero)
    KCtxArg (suc n) = KCtxArgSuc n

    KCtx : (n : ℕ) → KCtxArg n → SemiL lzero
    KCtx 0 <> = onepointˢ
    KCtx (suc n) arg-suc = Σ-SemiL (KCtx n (KCtxArgSuc.butlast arg-suc)) (KCtxArgSuc.D arg-suc)

  kctx-rcons-bot : (n : ℕ) → (arg-suc : KCtxArgSuc n) → elˢ (KCtx n (KCtxArgSuc.butlast arg-suc)) → elˢ (KCtx (suc n) arg-suc)
  kctx-rcons-bot n arg-suc ctx = (ctx , bottomˢ (semilᵈ (KCtxArgSuc.D arg-suc) ctx))


-- record TotalOrder {ℓ} (T : Type ℓ) : Type ℓ where
--   field
--     leqᵗ : T → T → Bool
-- 
--   _≤ᵗ_ : T → T → Bool
--   _≤ᵗ_ = leqᵗ
-- 
--   field
--     reflᵗ : {x : T} → x ≤ᵗ x ≡ true
--     transᵗ : {x y z : T} → x ≤ᵗ y ≡ true → y ≤ᵗ z ≡ true → x ≤ᵗ z ≡ true
--     antisymmᵗ : {x y : T} → x ≤ᵗ y ≡ true → y ≤ᵗ x ≡ true → x ≡ y
--     connectedᵗ : (x y : T) → x ≤ᵗ y ≡ true ⊎ y ≤ᵗ x ≡ true
-- 
-- 
--   gt-sym-leqᵗ : {x y : T} → x ≤ᵗ y ≡ false → y ≤ᵗ x ≡ true
--   gt-sym-leqᵗ {x = x} {y = y} x>y with connectedᵗ x y
--   ... | inj₁ x≤y = false-neq-true (sym x>y ∙ x≤y)
--   ... | inj₂ y≤x = y≤x
-- 
--   maxᵗ : T → T → T
--   maxᵗ x y = if leqᵗ x y then y else x
-- 
--   minᵗ : T → T → T
--   minᵗ x y = if leqᵗ x y then x else y
-- 
--   max-leq-rᵗ : {x y : T} → x ≤ᵗ y ≡ true → maxᵗ x y ≡ y
--   max-leq-rᵗ {x = x} {y = y} x≤y = cong (λ x≤y → if x≤y then y else x) x≤y
-- 
--   max-leq-lᵗ : {x y : T} → y ≤ᵗ x ≡ true → maxᵗ x y ≡ x
--   max-leq-lᵗ {x = x} {y = y} y≤x with inspec (x ≤ᵗ y)
--   ... | true with≡ x≤y = cong (λ x≤y → if x≤y then y else x) x≤y ∙ antisymmᵗ y≤x x≤y
--   ... | false with≡ x>y = cong (λ x≤y → if x≤y then y else x) x>y
-- 
--   max-symᵗ : {x y : T} → maxᵗ x y ≡ maxᵗ y x
--   max-symᵗ {x = x} {y = y} with connectedᵗ x y
--   ... | inj₁ x≤y = max-leq-rᵗ x≤y ∙ sym (max-leq-lᵗ x≤y)
--   ... | inj₂ y≤x = max-leq-lᵗ y≤x ∙ sym (max-leq-rᵗ y≤x)
--                            
-- 
--   leq-max-lᵗ : {x y : T} → x ≤ᵗ maxᵗ x y ≡ true
--   leq-max-lᵗ {x = x} {y = y} with inspec (leqᵗ x y)
--   ... | true with≡ leq = transport (cong (λ xy → x ≤ᵗ (if xy then y else x) ≡ true) (sym leq)) leq
--   ... | false with≡ gt = transport (cong (λ xy → x ≤ᵗ (if xy then y else x) ≡ true) (sym gt)) reflᵗ
-- 
--   leq-max-rᵗ : {x y : T} → y ≤ᵗ maxᵗ x y ≡ true
--   leq-max-rᵗ {x = x} {y = y} = y ≤ᵗ maxᵗ x y
--                                ≡⟨ cong (λ m → y ≤ᵗ m) max-symᵗ ⟩
--                                y ≤ᵗ maxᵗ y x
--                                ≡⟨ leq-max-lᵗ ⟩
--                                true
--                                ∎


-- open TotalOrder
-- 
-- 
-- maybeᵗ : {T : Type} → TotalOrder T → TotalOrder (Maybe T)
-- 
-- leqᵗ (maybeᵗ ord) nothing _ = true
-- leqᵗ (maybeᵗ ord) (just _) nothing = false
-- leqᵗ (maybeᵗ ord) (just x) (just y) = leqᵗ ord x y
-- 
-- reflᵗ (maybeᵗ ord) {x = nothing} = refl
-- reflᵗ (maybeᵗ ord) {x = just v} = reflᵗ ord
-- 
-- transᵗ (maybeᵗ ord) {x = nothing} _ _ = refl
-- transᵗ (maybeᵗ ord) {x = just _} {y = nothing} {z = nothing} xy _ = xy
-- transᵗ (maybeᵗ ord) {x = just _} {y = nothing} {z = just _} xy _ = false-neq-true xy
-- transᵗ (maybeᵗ ord) {x = just _} {y = just _} {z = nothing} _ yz = yz
-- transᵗ (maybeᵗ ord) {x = just x'} {y = just y'} {z = just z'} xy yz = transᵗ ord xy yz
-- 
-- antisymmᵗ (maybeᵗ ord) {x = nothing} {y = nothing} _ _ = refl
-- antisymmᵗ (maybeᵗ ord) {x = nothing} {y = just _} _ yz = false-neq-true yz
-- antisymmᵗ (maybeᵗ ord) {x = just _} {y = nothing} xy _ = false-neq-true xy
-- antisymmᵗ (maybeᵗ ord) {x = just _} {y = just _} xy yz = cong just (antisymmᵗ ord xy yz)
-- 
-- connectedᵗ (maybeᵗ ord) nothing _ = inj₁ refl
-- connectedᵗ (maybeᵗ ord) (just _) nothing = inj₂ refl
-- connectedᵗ (maybeᵗ ord) (just x) (just y) = connectedᵗ ord x y
-- 
-- Type-≤ : {T : Type} → (ord : TotalOrder T) → T → Type
-- Type-≤ {T} ord x = Σ T (λ y → leqᵗ ord y x ≡ true)
-- 
-- Type-maybe-> : {T : Type} → (ord : TotalOrder T) → Maybe T → Type
-- Type-maybe-> {T} ord k = Σ T (λ k' → maybe-satisfies (λ k'' → not (leqᵗ ord k' k'')) k ≡ true)
-- 
-- record SemiL {ℓ} (L : Type ℓ) : Type ℓ where
--   field
--     joinˢ : L → L → L
-- 
--   _∨ˢ_ : L → L → L
--   _∨ˢ_ = joinˢ
-- 
--   field
--     commˢ : (x y : L) → x ∨ˢ y ≡ y ∨ˢ x
--     assocˢ : (x y z : L) → (x ∨ˢ y) ∨ˢ z ≡ x ∨ˢ (y ∨ˢ z)
--     idemˢ : (x : L) → x ∨ˢ x ≡ x
-- 
-- 
--   compeqˢ : (x y z : L) → (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z)) ≡ x ∨ˢ (y ∨ˢ z)
--   compeqˢ x y z =
--     (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z))
--     ≡⟨ cong (joinˢ (x ∨ˢ y)) (assocˢ x y z ⁻¹) ⟩
--     (x ∨ˢ y) ∨ˢ ((x ∨ˢ y) ∨ˢ z)
--     ≡⟨ assocˢ (x ∨ˢ y) (x ∨ˢ y) z ⁻¹ ⟩
--     ((x ∨ˢ y) ∨ˢ (x ∨ˢ y)) ∨ˢ z
--     ≡⟨ cong (λ a → a ∨ˢ z) (idemˢ (x ∨ˢ y)) ⟩
--     (x ∨ˢ y) ∨ˢ z
--     ≡⟨ assocˢ x y z ⟩
--     x ∨ˢ (y ∨ˢ z)
--     ∎
-- 
-- open SemiL
-- 
-- 
-- maybeˢ : {L : Type} → SemiL L → SemiL (Maybe L)
-- 
-- joinˢ (maybeˢ s) nothing y = y
-- joinˢ (maybeˢ s) x nothing = x
-- joinˢ (maybeˢ s) (just x) (just y) = just (joinˢ s x y)
-- 
-- commˢ (maybeˢ s) nothing nothing = refl
-- commˢ (maybeˢ s) nothing (just _) = refl
-- commˢ (maybeˢ s) (just _) nothing = refl
-- commˢ (maybeˢ s) (just x) (just y) = cong just (commˢ s x y)
-- 
-- assocˢ (maybeˢ s) nothing _ _ = refl
-- assocˢ (maybeˢ s) (just _) nothing _ = refl
-- assocˢ (maybeˢ s) (just _) (just _) nothing = refl
-- assocˢ (maybeˢ s) (just x) (just y) (just z) = cong just (assocˢ s x y z)
-- 
-- idemˢ (maybeˢ s) nothing = refl
-- idemˢ (maybeˢ s) (just x) = cong just (idemˢ s x)
-- 
-- record SemiLᵈ {ℓ₁ ℓ₂} {S : Type ℓ₁} (L : SemiL S) (D : S → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
--   field
-- 
--     semilᵈ : (l : S) → SemiL (D l)
-- 
--     trᵈ : {x y : S} → D x → D (joinˢ L x y)
-- 
--     idᵈ : {x : S} (x' : D x) → PathP (λ i → D (idemˢ L x i)) (trᵈ x') x'
-- 
--     compᵈ : {x y z : S} (x' : D x) →
--       PathP (λ i → D (compeqˢ L x y z i)) (trᵈ (trᵈ x')) (trᵈ x') 
-- 
--     distrᵈ : {x y : S} (x' x'' : D x) →
--       trᵈ (joinˢ (semilᵈ x) x' x'') ≡ joinˢ (semilᵈ (joinˢ L x y)) (trᵈ x') (trᵈ x'')
-- 
--   trcommᵈ : {x y : S} → D (joinˢ L x y) → D (joinˢ L y x)
--   trcommᵈ {x} {y} = transport (cong D (commˢ L x y))
--   
--   trrᵈ : {x y : S} → D y → D (joinˢ L x y)
--   trrᵈ = trcommᵈ ∘ trᵈ
-- 
-- 
-- 
-- open SemiLᵈ
-- 
-- Σ-SemiL : {ℓ₁ ℓ₂ : Level} → {S : Type ℓ₁} → (L : SemiL S) → {D : S → Type ℓ₂} → (DL : SemiLᵈ L D) → SemiL (Σ S D)
-- joinˢ (Σ-SemiL L DL) (x , x') (y , y') = joinˢ L x y , joinˢ (semilᵈ DL (joinˢ L x y)) (trᵈ DL x') (trrᵈ DL y')
-- commˢ (Σ-SemiL L DL) (x , x') (y , y') = Σ-≡-intro (commˢ L x y , (λ i → {!!}))
-- assocˢ (Σ-SemiL L DL) (x , x') (y , y') (z , z') = {!!}
-- idemˢ (Σ-SemiL L {D} DL) (x , x') = Σ-≡-intro (idemˢ L x , λ i → transp
--   {!!}
--   (~ i) x')
-- Goal: PathP (λ i → D (idemˢ L x i))
--       (joinˢ (semilᵈ DL (joinˢ L x x)) (trᵈ DL x')
--        (trrᵈ DL x'))
--       x'


-- 
-- Σ-SemiL : (ℒ : SemiL ℓ₁) (ℳ : SemiLᵈ ℒ ℓ₂) → SemiL (ℓ₁ ⊔ ℓ₂)
-- elˢ (Σ-SemiL ℒ ℳ) = Σ (elˢ ℒ) (elˢ ∘ semilᵈ ℳ)
-- _∨ˢ_ (Σ-SemiL ℒ ℳ) (x , α) (y , β) = joinˢ ℒ x y , joinˢ (semilᵈ ℳ (joinˢ ℒ x y)) (trᵈ ℳ α) (trcommᵈ ℳ (trᵈ ℳ β)) 
-- commˢ (Σ-SemiL ℒ ℳ) = {!!}
-- assocˢ (Σ-SemiL ℒ ℳ) = {!!}
-- idemˢ (Σ-SemiL ℒ ℳ) = {!!}

    

-- record CtxTyStr {K : Type} (kOrd : TotalOrder K) (k : Maybe K) : Type₁ where
-- -- all new keys must be greater than k
--   coinductive
--   field
--     ty : Type-maybe-> kOrd k → Type
--     ex : (k' : Type-maybe-> kOrd k) → ty k' → CtxTyStr kOrd (just (fst k'))
-- 
-- open CtxTyStr
-- 
-- mutual
-- 
-- 
--   data Ctx {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) : Maybe K → Type where
--     -- `Maybe k` argument is the greatest, last key in the context
--     nullᶜ : Ctx kOrd ts nothing
--     rconsᶜ : {k : Maybe K} → (c : Ctx kOrd ts k) → (k' : Type-maybe-> kOrd k) → (el : ty (exs ts c) k') → Ctx kOrd ts (just (fst k'))
-- 



--   record CtxTyStr (k : Maybe K) : Type₁ where
--     -- all new keys must be greater than k
--     coinductive
--     field
--       ty : Type-maybe-> kOrd k → Type
--       semi-ty : (k' : Type-maybe-> kOrd k) → SemiL (ty k')
--       ex : (k' : Type-maybe-> kOrd k) → ty k' → CtxTyStr (just (fst k'))

--   mutual
--     data SemiLStr : ℕ → Type₁ where
--       empty-str : SemiLStr 0
--       rcons-str : (n : ℕ) → (prev : SemiLStr n) → (Ctx n prev → Type) → SemiLStr (suc n)
    
      
--     data Ctx : (n : ℕ) → SemiLStr n → Type₁ where
--       emptyᶜ : Ctx 0 empty-str

--   exs : {K : Type} {kOrd : TotalOrder K} {k : Maybe K} → (ts : CtxTyStr kOrd nothing) → Ctx kOrd ts k → CtxTyStr kOrd k
--   exs ts nullᶜ = ts
--   exs ts (rconsᶜ c k' el) = ex (exs ts c) k' el
-- join-ctx : {K : Type} → (kOrd : TotalOrder K) → (ts : CtxTyStr kOrd nothing) → (k1 k2 : Maybe K) → Ctx kOrd ts k1 → Ctx kOrd ts k2 → Ctx kOrd ts (maxᵗ (maybeᵗ kOrd) k1 k2)
-- join-ctx _ _ nothing nothing nullᶜ nullᶜ = nullᶜ
-- join-ctx _ _ nothing (just k2) nullᶜ c2 = c2
-- join-ctx _ _ (just k1) nothing c1 nullᶜ = c1
-- join-ctx kOrd ts (just k1) (just k2) c1@(rconsᶜ {k = k1''} c1' k1' el1) c2@(rconsᶜ {k = k2''} c2' k2' el2) with inspec (leqᵗ kOrd (fst k1') (fst k2'))
-- ... | true with≡ k1'≤k2' = {!!}
-- ... | false with≡ k1'>k2' =
--         let k2'≤k1' = gt-sym-leqᵗ (maybeᵗ kOrd) k1'>k2' in
--         transport (cong (Ctx kOrd ts) (max-leq-rᵗ (maybeᵗ kOrd) k2'≤k1'))
--         (rconsᶜ (join-ctx kOrd ts k1'' (just k2) c1' c2)
--                 (transport (cong (Type-maybe-> kOrd) (max-leq-rᵗ (maybeᵗ kOrd) k2'≤k1')) k1')
--                 {!!})
--                 -- darn, gotta transport el1...
-- record Ctx-promoted {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) (k : Maybe K) : Type where
--   field
--     keyᵖ : Maybe K
--     baseᵖ : Ctx kOrd ts keyᵖ
--     key-cmpᵖ : leqᵗ (maybeᵗ kOrd) keyᵖ k ≡ true
-- 
-- open Ctx-promoted


-- semilᶜ : {K : Type} (kOrd : TotalOrder K) (ts : CtxTyStr kOrd nothing) (k : Maybe K) → SemiL (Ctx-promoted kOrd ts k)
-- _∨ˢ_ (semilᶜ kOrd ts k) p1 p2 with (baseᵖ p1)
-- ... | nullᶜ = p2
-- ... | rconsᶜ {k = k1} c1 k1' el1 with (baseᵖ p2)
-- ...   | nullᶜ = p1
-- ...   | rconsᶜ {k = k2} c2 k2' el2  with inspec (leqᵗ kOrd (fst k1') (fst k2'))
-- ...     | false with≡ eq1 = let k3 = maxᵗ (maybeᵗ kOrd) k1 (just (fst k2'))
--                                 p1' = record {keyᵖ = k1; baseᵖ = c1; key-cmpᵖ = leq-max-lᵗ (maybeᵗ kOrd)}
--                                 p2' = record {keyᵖ = just (fst k2'); baseᵖ = baseᵖ p2; key-cmpᵖ = leq-max-rᵗ (maybeᵗ kOrd)}
--                                 rest = rconsᶜ (baseᵖ (joinˢ (semilᶜ kOrd ts k3) p1' p2')) (fst k1' , {!!}) {!!}
--                             in record {keyᵖ = just (fst k1'); baseᵖ = rest; key-cmpᵖ = {!!}}
-- 
-- Context : {K : Type} → TotalOrder K → Type → K → Type
-- Context kOrd V k = Type-≤ kOrd k → Maybe V
-- 
-- demote-context : {K : Type} {kOrd : TotalOrder K} {V : Type} {k : K} → (c : Context kOrd V k) → (k' : Type-≤ kOrd k) → Context kOrd V (fst k')
-- demote-context {kOrd = kOrd} c k' k'' = c (fst k'' , transᵗ kOrd (snd k'') (snd k'))
-- 
-- 
-- record SemiLGraph (K : Type) (kOrd : TotalOrder K) (V : Type) : Type where
-- 
--   field
--     check-elemᵍ : (k : K) → Context kOrd V k → V → Bool
-- 
-- 
--   elemᵍ : (k : K) → Context kOrd V k → Type
--   elemᵍ k c = Σ V (λ v → check-elemᵍ k c v ≡ true)
-- 
--   check-maybe-elemᵍ : (k : K) → Context kOrd V k → Maybe V → Bool
--   check-maybe-elemᵍ k c = maybe-satisfies (check-elemᵍ k c)
-- 
--   -- Contextᵍ : K → Type
--   -- Contextᵍ k = Σ (Context kOrd V k) (λ c → (k' : Type-≤ kOrd k) → check-maybe-elemᵍ k c 
-- 
--   field
--     semilᵍ : (k : K) → (c : Context kOrd V k) → SemiL (elemᵍ k c)
--     trᵍ : (k : K) → (c1 c2 : Context kOrd V k) → (v : elemᵍ k c1) → Maybe (elemᵍ k c2)
-- 
--   context-semilᵍ : (k : K) → SemiL (Context kOrd V k)
--   _∨ˢ_ (context-semilᵍ k) c1 c2 k' =
--     let v = joinˢ (maybeˢ (semilᵍ {!!} {!!})) {!!} {!!} in {!!} -- k' (joinˢ (context-semilᵍ k) c1 c2))) ? ?



