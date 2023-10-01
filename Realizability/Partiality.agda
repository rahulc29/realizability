{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels

module Realizability.Partiality where

-- Mutual definition
-- We use the partiality monad by arXiv:1610.09254v2
-- This is done by constructing the free ω-cpo
-- over a type A using QIITs
data ♯_ {ℓ} (A : Type ℓ) : Type ℓ
data _⊑_ {ℓ} {A : Type ℓ} : ♯ A → ♯ A → Type ℓ
data ♯_ A where
  η : A → ♯ A
  ⊥ : ♯ A
  ⨆ : (s : ℕ → ♯ A)
      → (∀ n → (s n) ⊑ (s (suc n)))
      → ♯ A
  α : ∀ x y
      → x ⊑ y
      → y ⊑ x
      → x ≡ y
  setTrunc : isSet (♯ A)
data _⊑_ {ℓ} {A} where
  ⊑-refl : ∀ x → x ⊑ x
  ⊑-trans : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-bottom : ∀ x → ⊥ ⊑ x
  ⊑-ub : ∀ s p → (∀ n → s n ⊑ (⨆ s p))
  ⊑-lub : ∀ s p x → (∀ n → s n ⊑ x) → (⨆ s p) ⊑ x
  propTrunc : ∀ x y → isProp(x ⊑ y)

infix 20 _⊑_
infix 21 ♯_

-- We now define the type of 
-- partiality algebras over a type A
-- This is similar to, but slightly more complicated than
-- the kind of F-(co)algebras that naturally come up when studying
-- (co)induction.
-- For lower inductive types, initiality and the elimination rules
-- are rather trivial to establish. For higher inductive, or
-- as it is, in our case, quotient inductive inductive types,
-- the elimination rule is slightly more involved.
-- We show that ♯ A is exactly the initial object
-- in the category of partiality algebras over A
-- This gives us the induction principle for ♯ A
-- TODO : Complete construction
module _ {ℓ} (A : Type ℓ) where
  -- Also, side note, the universe levels start to get real ugly really quickly
  record PartialityAlgebra {ℓ' ℓ''} (X : Type ℓ') (_⊑X_ : X → X → Type ℓ'') : Type (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-max ℓ ℓ')) where
    field
      -- data structure
      isSetX : isSet X
      isProp⊑ : ∀ x y → isProp (x ⊑X y)
      ηX : A → X
      ⊥X : X
      ⨆X : (s : ℕ → X) → (∀ n → (s n) ⊑X (s (suc n))) → X
      -- logical structure
      -- Conjecture : being a partiality algebra is an hProp
      -- TODO : Separate logical structure into separate record
      αX : ∀ x y → x ⊑X y → y ⊑X x → x ≡ y
      ⊑X-refl : ∀ x → x ⊑X x
      ⊑X-trans : ∀ x y z → x ⊑X y → y ⊑X z → x ⊑X z
      ⊑X-bottom : ∀ x → ⊥X ⊑X x
      ⊑X-ub : (s : ℕ → X) → (p : (∀ n → (s n) ⊑X (s (suc n)))) → (n : ℕ) → (s n) ⊑X (⨆X s p)
      ⊑X-lub : ∀ x → (s : ℕ → X) → (p : (∀ n → (s n) ⊑X (s (suc n)))) → (∀ n → s n ⊑X x) → (⨆X s p) ⊑X x

  -- That's one ugly universe level
  record PartialityAlgebraHomomorphism {𝔁 𝔂 𝔁' 𝔂'} {X : Type 𝔁} {_⊑X_ : X → X → Type 𝔁'} {Y : Type 𝔂} {_⊑Y_ : Y → Y → Type 𝔂'} (XAlgebra : PartialityAlgebra X _⊑X_) (YAlgebra : PartialityAlgebra Y _⊑Y_) : Type (ℓ-max (ℓ-max (ℓ-max 𝔁 ℓ) 𝔂) (ℓ-max (ℓ-max ℓ 𝔁') 𝔂')) where
    open PartialityAlgebra XAlgebra
    open PartialityAlgebra YAlgebra renaming (⊥X to ⊥Y ; ηX to ηY ; ⨆X to ⨆Y)
    field
      map : X → Y
      monotone : ∀ x x' → x ⊑X x' → (map x) ⊑Y (map x')
      ⊥-preserve : map ⊥X ≡ ⊥Y
      η-preserve : ∀ a → map (ηX a) ≡ ηY a
      ⨆-preserve : (s : ℕ → X)
                 → (p : (∀ n → (s n) ⊑X (s (suc n))))
                 → map (⨆X s p) ≡ ⨆Y (λ n → map (s n)) (λ n → monotone (s n) (s (suc n)) (p n))

  open PartialityAlgebra
  ♯A-PartialityAlgebra : PartialityAlgebra (♯ A) (_⊑_ {A = A})
  ♯A-PartialityAlgebra .isSetX = setTrunc
  ♯A-PartialityAlgebra .isProp⊑ = propTrunc
  ♯A-PartialityAlgebra .ηX = η
  ♯A-PartialityAlgebra .⊥X = ⊥
  ♯A-PartialityAlgebra .⨆X = ⨆
  ♯A-PartialityAlgebra .αX = α
  ♯A-PartialityAlgebra .⊑X-refl = ⊑-refl
  ♯A-PartialityAlgebra .⊑X-trans = ⊑-trans
  ♯A-PartialityAlgebra .⊑X-bottom = ⊑-bottom
  ♯A-PartialityAlgebra .⊑X-ub = ⊑-ub
  ♯A-PartialityAlgebra .⊑X-lub x s p = ⊑-lub s p x

  -- Initiality of ♯A
  -- ♯A is the initial object in the category of
  -- partiality algebras
  -- Not only would it allow for much better and easier to read code
  -- it is conceptually easier to manage
  -- I'm sure both are equivalent formulations anyway

  record isInitial {𝔂 𝔂'} {Y : Type 𝔂} {_⊑Y_ : Y → Y → Type 𝔂'} (initial : PartialityAlgebra Y _⊑Y_) : Typeω where
    field
      morph : ∀ {𝔁 𝔁'} → (X : Type 𝔁) → (_⊑X_ : X → X → Type 𝔁') → (object : PartialityAlgebra X _⊑X_) → PartialityAlgebraHomomorphism initial object
      uniqueness : ∀ {𝔁 𝔁'} → (X : Type 𝔁) → (_⊑X_ : X → X → Type 𝔁') → (object : PartialityAlgebra X _⊑X_) → isContr (PartialityAlgebraHomomorphism initial object)

  -- Conjecture : being initial is an hProp
  open PartialityAlgebraHomomorphism

  module _ {𝔁 𝔁'} (X : Type 𝔁) (_⊑X_ : X → X → Type 𝔁') (object : PartialityAlgebra X _⊑X_) where
    {-# TERMINATING #-}
    ♯A-morphs : PartialityAlgebraHomomorphism ♯A-PartialityAlgebra object
    ♯A-morphs .map (η a) = object .ηX a
    ♯A-morphs .map ⊥ = object .⊥X
    ♯A-morphs .map (⨆ s p) = object .⨆X (λ n → ♯A-morphs .map (s n)) λ n → ♯A-morphs .monotone (s n) (s (suc n)) (p n)
    ♯A-morphs .map (α x y x⊑y y⊑x i) = object .αX (♯A-morphs .map x) (♯A-morphs .map y) (♯A-morphs .monotone x y x⊑y) (♯A-morphs .monotone y x y⊑x) i
    ♯A-morphs .map (setTrunc x y p q i j) = object .isSetX (♯A-morphs .map x) (♯A-morphs .map y) (cong (♯A-morphs .map) p) (cong (♯A-morphs .map) q) i j
    ♯A-morphs .monotone x x (⊑-refl x) = object .⊑X-refl (♯A-morphs .map x)
    ♯A-morphs .monotone x z (⊑-trans x y z x⊑y y⊑z) = object .⊑X-trans (♯A-morphs .map x) (♯A-morphs .map y) (♯A-morphs .map z) (♯A-morphs .monotone _ _ x⊑y) (♯A-morphs .monotone _ _ y⊑z)
    ♯A-morphs .monotone _ x (⊑-bottom x) = object .⊑X-bottom (♯A-morphs .map x)
    ♯A-morphs .monotone _ _ (⊑-ub s p index) = object .⊑X-ub (λ n → ♯A-morphs .map (s n)) (λ n → ♯A-morphs .monotone _ _ (p n)) index
    ♯A-morphs .monotone _ _ (⊑-lub s p x fam) = object .⊑X-lub (♯A-morphs .map x) (λ n → ♯A-morphs .map (s n)) (λ n → ♯A-morphs .monotone _ _ (p n)) (λ n → ♯A-morphs .monotone _ _ (fam n))
    ♯A-morphs .monotone _ _ (propTrunc x y p q i) = object .isProp⊑ (♯A-morphs .map x) (♯A-morphs .map y) (♯A-morphs .monotone _ _ p) (♯A-morphs .monotone _ _ q) i
    ♯A-morphs .⊥-preserve = refl
    ♯A-morphs .η-preserve a = refl
    ♯A-morphs .⨆-preserve s p = refl

  open isInitial
  ♯A-isInitial : isInitial ♯A-PartialityAlgebra
  ♯A-isInitial .morph = ♯A-morphs
  ♯A-isInitial .uniqueness X _⊑X_ object .fst = ♯A-isInitial .morph X _⊑X_ object
  ♯A-isInitial .uniqueness X _⊑X_ object .snd f = {!!}

  
_⇀_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ⇀ B = A → ♯ B

-- Monadic operations
return : ∀ {ℓ} → {A : Type ℓ} → A → ♯ A
return = η

-- Bind
_>>=_ : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'} → ♯ A → (A → ♯ B) → ♯ B
(η a) >>= f = (f a)
⊥ >>= f = ⊥
(⨆ s p) >>= f = ⨆ (λ n → (s n) >>= f) λ n → {!!}
(α x y x⊑y y⊑x i) >>= f = α (x >>= f) (y >>= f) {!!} {!!} i
(setTrunc x y p q i j) >>= f = setTrunc (x >>= f) (y >>= f) (cong (λ x → x >>= f) p) (cong (λ x → x >>= f) q) i j
