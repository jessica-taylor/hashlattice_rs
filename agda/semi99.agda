
{-# OPTIONS --cubical --guardedness #-}

module semi99 where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Empty
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

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

Σ-≡-intro : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {a a' : A} {b : B a} {b' : B a'}
  → (Σ (a ≡ a') λ p → PathP (λ i → B (p i)) b b') → (a , b) ≡ (a' , b')

Σ-≡-intro eqs =
  cong₂ (λ c c' → (c , c'))
    (fst eqs)
    (snd eqs)

data Promote {ℓ₁ ℓ₂} (A : Type ℓ₁) : Type (ℓ₁ ⊔ ℓ₂) where
  promote : A → Promote A

record Category ℓ₁ ℓ₂ : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    elᶜ : Type ℓ₁
    morᶜ : elᶜ → elᶜ → Type ℓ₂
    idᶜ : (x : elᶜ) → morᶜ x x
    compᶜ : {x y z : elᶜ} → morᶜ y z → morᶜ x y → morᶜ x z
    id-compᶜ : {x y : elᶜ} → (m : morᶜ x y) → compᶜ (idᶜ y) m ≡ m
    comp-idᶜ : {x y : elᶜ} → (m : morᶜ x y) → compᶜ m (idᶜ x) ≡ m
    assocᶜ : {a b c d : elᶜ} → (cd : morᶜ c d) → (bc : morᶜ b c) → (ab : morᶜ a b) → compᶜ cd (compᶜ bc ab) ≡ compᶜ (compᶜ cd bc) ab

open Category

set-cat : {ℓ : Level} → Category (lsuc ℓ) ℓ
elᶜ (set-cat {ℓ}) = Type ℓ
morᶜ set-cat t1 t2 = t1 → t2
idᶜ set-cat _ x = x
compᶜ set-cat f g = f ∘ g
id-compᶜ set-cat _ = refl
comp-idᶜ set-cat _ = refl
assocᶜ set-cat _ _ _ = refl

record Functor {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (C : Category ℓ₁ ℓ₂) (D : Category ℓ₃ ℓ₄) : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    objᶠ : elᶜ C → elᶜ D
    morᶠ : {a b : elᶜ C} → morᶜ C a b → morᶜ D (objᶠ a) (objᶠ b)
    mor-idᶠ : (a : elᶜ C) → morᶠ (idᶜ C a) ≡ idᶜ D (objᶠ a)
    mor-compᶠ : {a b c : elᶜ C} → (bc : morᶜ C b c) → (ab : morᶜ C a b) → morᶠ (compᶜ C bc ab) ≡ compᶜ D (morᶠ bc) (morᶠ ab)

open Functor

idᶠ : {ℓ₁ ℓ₂ : Level} → (C : Category ℓ₁ ℓ₂) → Functor C C
objᶠ (idᶠ C) x = x
morᶠ (idᶠ C) ab = ab
mor-idᶠ (idᶠ C) a = refl
mor-compᶠ (idᶠ C) bc ab = refl

_∘ᶠ_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level} {A : Category ℓ₁ ℓ₂} {B : Category ℓ₃ ℓ₄} {C : Category ℓ₅ ℓ₆} → Functor B C → Functor A B → Functor A C
objᶠ (f ∘ᶠ g) = objᶠ f ∘ objᶠ g
morᶠ (f ∘ᶠ g) = morᶠ f ∘ morᶠ g
mor-idᶠ (_∘ᶠ_ {A = A} {B = B} {C = C} f g) a =
  morᶠ f (morᶠ g (idᶜ A a))
  ≡⟨ cong (morᶠ f) (mor-idᶠ g a) ⟩
  morᶠ f (idᶜ B (objᶠ g a))
  ≡⟨ mor-idᶠ f (objᶠ g a) ⟩
  idᶜ C (objᶠ f (objᶠ g a))
  ∎
mor-compᶠ (_∘ᶠ_ {A = A} {B = B} {C = C} f g) bc ab =
  morᶠ f (morᶠ g (compᶜ A bc ab))
  ≡⟨ cong (morᶠ f) (mor-compᶠ g bc ab) ⟩
  morᶠ f (compᶜ B (morᶠ g bc) (morᶠ g ab))
  ≡⟨ mor-compᶠ f _ _ ⟩
  compᶜ C (morᶠ f (morᶠ g bc)) (morᶠ f (morᶠ g ab))
  ∎


cat-cat : (ℓ₁ ℓ₂ : Level) → Category (lsuc (ℓ₁ ⊔ ℓ₂)) (ℓ₁ ⊔ ℓ₂)
elᶜ (cat-cat ℓ₁ ℓ₂) = Category ℓ₁ ℓ₂
morᶜ (cat-cat ℓ₁ ℓ₂) C D = Functor C D
idᶜ (cat-cat ℓ₁ ℓ₂) C = idᶠ C
compᶜ (cat-cat ℓ₁ ℓ₂) = _∘ᶠ_
id-compᶜ (cat-cat ℓ₁ ℓ₂) m = {!!}
comp-idᶜ (cat-cat ℓ₁ ℓ₂) m = {!!}
assocᶜ (cat-cat ℓ₁ ℓ₂) cd bc ab = {!!}

record NatTrans {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {C : Category ℓ₁ ℓ₂} {D : Category ℓ₃ ℓ₄} (F G : Functor C D) : Type (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    etaⁿ : (x : elᶜ C) → morᶜ D (objᶠ F x) (objᶠ G x)
    commuteⁿ : {x y : elᶜ C} → (f : morᶜ C x y) → compᶜ D (etaⁿ y) (morᶠ F f) ≡ compᶜ D (morᶠ G f) (etaⁿ x)

open NatTrans

idⁿ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {C : Category ℓ₁ ℓ₂} {D : Category ℓ₃ ℓ₄} → (F : Functor C D) → NatTrans F F
etaⁿ (idⁿ {D = D} F) x = idᶜ D (objᶠ F x)
commuteⁿ (idⁿ {D = D} F) f = id-compᶜ D (morᶠ F f) ∙ sym (comp-idᶜ D (morᶠ F f))

_∘ⁿ_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {C : Category ℓ₁ ℓ₂} {D : Category ℓ₃ ℓ₄} {F G H : Functor C D} → NatTrans G H → NatTrans F G → NatTrans F H
etaⁿ (_∘ⁿ_ {D = D} n m) x = compᶜ D (etaⁿ n x) (etaⁿ m x)
commuteⁿ (_∘ⁿ_ {D = D} {F = F} {G = G} {H = H} n m) {x = x} {y = y} f =
  compᶜ D (compᶜ D (etaⁿ n y) (etaⁿ m y)) (morᶠ F f)
  ≡⟨ sym (assocᶜ D _ _ _) ⟩
  compᶜ D (etaⁿ n y) (compᶜ D  (etaⁿ m y) (morᶠ F f))
  ≡⟨ cong (λ x → compᶜ D _ x) (commuteⁿ m f) ⟩
  compᶜ D (etaⁿ n y) (compᶜ D (morᶠ G f) (etaⁿ m x))
  ≡⟨ assocᶜ D _ _ _ ⟩
  compᶜ D (compᶜ D (etaⁿ n y) (morᶠ G f)) (etaⁿ m x)
  ≡⟨ cong (λ x → compᶜ D x _) (commuteⁿ n f) ⟩
  compᶜ D (compᶜ D (morᶠ H f) (etaⁿ n x)) (etaⁿ m x)
  ≡⟨ sym (assocᶜ D _ _ _) ⟩
  compᶜ D (morᶠ H f) (compᶜ D (etaⁿ n x) (etaⁿ m x))
  ∎


func-cat : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (C : Category ℓ₁ ℓ₂) (D : Category ℓ₃ ℓ₄) → Category (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
elᶜ (func-cat C D) = Functor C D
morᶜ (func-cat C D) = NatTrans
idᶜ (func-cat C D) = idⁿ
compᶜ (func-cat C D) = _∘ⁿ_

DepCat : {ℓ₁ ℓ₂ : Level} → (C : Category ℓ₁ ℓ₂) → Type (lsuc (ℓ₁ ⊔ ℓ₂))
DepCat {ℓ₁} {ℓ₂} C = Functor C (cat-cat ℓ₁ ℓ₂)

Σᶜ : {ℓ₁ ℓ₂ : Level} (C : Category ℓ₁ ℓ₂) → DepCat C → Category ℓ₁ ℓ₂
elᶜ (Σᶜ C D) = Σ (elᶜ C) (λ c → elᶜ (objᶠ D c))
morᶜ (Σᶜ C D) (a , a') (b , b') = Σ (morᶜ C a b) (λ m → morᶜ (objᶠ D b) (objᶠ (morᶠ D m) a') b')
idᶜ (Σᶜ C D) (a , a') = (idᶜ C a , {!!})
compᶜ (Σᶜ C D) (bc , bc') (ab , ab') = (compᶜ C bc ab , {!!})

Πᶜ : {ℓ₁ ℓ₂ : Level} (C : Category ℓ₁ ℓ₂) → DepCat C → Category ℓ₁ (ℓ₁ ⊔ ℓ₂)
elᶜ (Πᶜ C D) = (c : elᶜ C) → elᶜ (objᶠ D c)
morᶜ (Πᶜ C D) a b = (c : elᶜ C) → morᶜ (objᶠ D c) (a c) (b c)
idᶜ (Πᶜ C D) a c = idᶜ (objᶠ D c) (a c)
compᶜ (Πᶜ C D) bc ab x = compᶜ (objᶠ D x) (bc x) (ab x) 
id-compᶜ (Πᶜ C D) m = {!!}

record Poset ℓ₁ ℓ₂ : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    catᵖ : Category ℓ₁ ℓ₂
    leq-propᵖ : (x y : elᶜ catᵖ) → isProp (morᶜ catᵖ x y)

  elᵖ : Type ℓ₁
  elᵖ = elᶜ catᵖ

  leqᵖ : elᵖ → elᵖ → Type ℓ₂
  leqᵖ = morᶜ catᵖ

open Poset

PosetMor : {ℓ₁ ℓ₂ : Level} → Poset ℓ₁ ℓ₂ → Poset ℓ₁ ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
PosetMor P Q = Functor (catᵖ P) (catᵖ Q)

poset-cat : (ℓ₁ ℓ₂ : Level) → Category (lsuc (ℓ₁ ⊔ ℓ₂)) (ℓ₁ ⊔ ℓ₂)
elᶜ (poset-cat ℓ₁ ℓ₂) = Poset ℓ₁ ℓ₂
morᶜ (poset-cat ℓ₁ ℓ₂) = PosetMor
idᶜ (poset-cat ℓ₁ ℓ₂) P = idᶠ (catᵖ P)
compᶜ (poset-cat ℓ₁ ℓ₂) = _∘ᶠ_
id-compᶜ (poset-cat ℓ₁ ℓ₂) = id-compᶜ (cat-cat ℓ₁ ℓ₂)
comp-idᶜ (poset-cat ℓ₁ ℓ₂) = comp-idᶜ (cat-cat ℓ₁ ℓ₂)
assocᶜ (poset-cat ℓ₁ ℓ₂) = assocᶜ (cat-cat ℓ₁ ℓ₂)

forgetᵖ : (ℓ₁ ℓ₂ : Level) → Functor (poset-cat ℓ₁ ℓ₂) (cat-cat ℓ₁ ℓ₂)
objᶠ (forgetᵖ _ _) = catᵖ
morᶠ (forgetᵖ _ _) x = x
mor-idᶠ (forgetᵖ _ _) x = refl
mor-compᶠ (forgetᵖ _ _) bc ab = refl


DepPoset : {ℓ₁ ℓ₂ : Level} → (P : Poset ℓ₁ ℓ₂) → Type (lsuc (ℓ₁ ⊔ ℓ₂))
DepPoset {ℓ₁} {ℓ₂} P = Functor (catᵖ P) (poset-cat ℓ₁ ℓ₂)

Σᵖ : {ℓ₁ ℓ₂ : Level} (P : Poset ℓ₁ ℓ₂) → DepPoset P → Poset ℓ₁ ℓ₂
catᵖ (Σᵖ {ℓ₁} {ℓ₂} P D) = Σᶜ (catᵖ P) (forgetᵖ ℓ₁ ℓ₂ ∘ᶠ D)
leq-propᵖ (Σᵖ P D) (a , a') (b , b') (x , x') (y , y') = Σ-≡-intro (leq-propᵖ P a b x y , {!!})

-- Πᵖ : {ℓ : Level} (P : Poset ℓ) → DepPoset P → Poset ℓ
-- catᵖ (Πᵖ {ℓ} P D) = Πᶜ (catᵖ P) (forgetᵖ ℓ ∘ᶠ D)

record SemiLat ℓ₁ ℓ₂ : Type (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    posetˢ : Poset ℓ₁ ℓ₂
    joinˢ : elᵖ posetˢ → elᵖ posetˢ → elᵖ posetˢ
    bottomˢ : elᵖ posetˢ
    inlˢ : {x y : elᵖ posetˢ} → leqᵖ posetˢ x (joinˢ x y)
    inrˢ : {x y : elᵖ posetˢ} → leqᵖ posetˢ y (joinˢ x y)
    lubˢ : {x y z : elᵖ posetˢ} → leqᵖ posetˢ x z → leqᵖ posetˢ y z → leqᵖ posetˢ (joinˢ x y) z
    bottom-minˢ : {x : elᵖ posetˢ} → leqᵖ posetˢ bottomˢ x


  elˢ : Type ℓ₁
  elˢ = elᵖ posetˢ

  leqˢ : elˢ → elˢ → Type ℓ₂
  leqˢ = leqᵖ posetˢ

  catˢ : Category ℓ₁ ℓ₂
  catˢ = catᵖ posetˢ

open SemiLat

record SemiLatMor {ℓ₁ ℓ₂ : Level} (A B : SemiLat ℓ₁ ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    applyˢᵐ : Functor (catˢ A) (catˢ B)
    apply-joinˢᵐ : {x y : elˢ A} → objᶠ applyˢᵐ (joinˢ A x y) ≡ joinˢ B (objᶠ applyˢᵐ x) (objᶠ applyˢᵐ y)
    apply-bottomˢᵐ : {x y : elˢ A} → objᶠ applyˢᵐ (bottomˢ A) ≡ bottomˢ B

open SemiLatMor

idˢᵐ : {ℓ₁ ℓ₂ : Level} → (S : SemiLat ℓ₁ ℓ₂) → SemiLatMor S S
applyˢᵐ (idˢᵐ _) = idᶠ _
apply-joinˢᵐ (idˢᵐ S) = {!!}
apply-bottomˢᵐ (idˢᵐ S) = {!!}

_∘ˢᵐ_ : {ℓ₁ ℓ₂ : Level} {A B C : SemiLat ℓ₁ ℓ₂} → SemiLatMor B C → SemiLatMor A B → SemiLatMor A C
applyˢᵐ (bc ∘ˢᵐ ab) = applyˢᵐ bc ∘ᶠ applyˢᵐ ab
apply-joinˢᵐ (bc ∘ˢᵐ ab) = {!!}
apply-bottomˢᵐ (bc ∘ˢᵐ ab) = {!!}

semi-lat-cat : (ℓ₁ ℓ₂ : Level) → Category (lsuc (ℓ₁ ⊔ ℓ₂)) (ℓ₁ ⊔ ℓ₂)
elᶜ (semi-lat-cat ℓ₁ ℓ₂) = SemiLat ℓ₁ ℓ₂
morᶜ (semi-lat-cat  _ _) = SemiLatMor
idᶜ (semi-lat-cat _ _) = idˢᵐ
compᶜ (semi-lat-cat _ _) = _∘ˢᵐ_
id-compᶜ (semi-lat-cat _ _) m = {!!}
comp-idᶜ (semi-lat-cat _ _) m = {!!}
assocᶜ (semi-lat-cat _ _) cd bc ab = {!!}

forgetˢ : (ℓ₁ ℓ₂ : Level) → Functor (semi-lat-cat ℓ₁ ℓ₂) (poset-cat ℓ₁ ℓ₂)
objᶠ (forgetˢ _ _) = posetˢ
morᶠ (forgetˢ _ _) = applyˢᵐ
mor-idᶠ (forgetˢ _ _) _ = refl
mor-compᶠ (forgetˢ _ _) _ _ = refl



DepSemiLat : {ℓ₁ ℓ₂ : Level} → SemiLat ℓ₁ ℓ₂ → Type (lsuc (ℓ₁ ⊔ ℓ₂))
DepSemiLat {ℓ₁} {ℓ₂} S = Functor (catˢ S) (semi-lat-cat ℓ₁ ℓ₂)

-- Σᵖ : {ℓ : Level} {P : Poset ℓ} → DepPoset P → Poset ℓ
-- catᵖ (Σᵖ {ℓ} D) = Σᶜ (forgetᵖ ℓ ∘ᶠ D)
-- leq-propᵖ (Σᵖ {P = P} D) (a , a') (b , b') (x , x') (y , y') = Σ-≡-intro (leq-propᵖ P a b x y , {!!})

Σˢ : {ℓ₁ ℓ₂ : Level} → (S : SemiLat ℓ₁ ℓ₂) → DepSemiLat S → SemiLat ℓ₁ ℓ₂
posetˢ (Σˢ {ℓ₁} {ℓ₂} S D) = Σᵖ (posetˢ S) (forgetˢ ℓ₁ ℓ₂ ∘ᶠ D)
joinˢ (Σˢ S D) (a , a') (b , b') = (joinˢ S a b , {!!})


SemiLatEndo : (ℓ₁ ℓ₂ : Level) → Type (lsuc (ℓ₁ ⊔ ℓ₂))
SemiLatEndo ℓ₁ ℓ₂ = Functor (semi-lat-cat ℓ₁ ℓ₂) (semi-lat-cat ℓ₁ ℓ₂)

