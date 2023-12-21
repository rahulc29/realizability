open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.HITs.SetQuotients

module Realizability.Tripos.PosetReflection where

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    _≤_ : A → A → Type ℓ'
    B : Type ℓ''

open IsPreorder renaming
  (is-set to isSetPreorder
  ;is-refl to isReflPreorder
  ;is-trans to isTransPreorder
  ;is-prop-valued to isPropValuedPreorder)
open IsPoset renaming
  (is-set to isSetPoset
  ;is-refl to isReflPoset
  ;is-antisym to isAntiSymPoset
  ;is-trans to isTransPoset
  ;is-prop-valued to isPropValuedPoset)

PosetReflection : {A : Type ℓ} (_≤_ : A → A → Type ℓ') → Type (ℓ-max ℓ ℓ')
PosetReflection {A = A} _≤_ = A / λ x y → x ≤ y × y ≤ x

module Properties {A : Type ℓ} (_≤_ : A → A → Type ℓ') (isPreorder : IsPreorder _≤_) where
  _≤ᴿ_ : PosetReflection _≤_ → PosetReflection _≤_ → hProp ℓ'
  a ≤ᴿ b =
    rec2
      isSetHProp
      (λ x y → (x ≤ y) , isPreorder .isPropValuedPreorder x y)
      (λ { x y z (x≤y , y≤x) →
        Σ≡Prop
          (λ A → isPropIsProp {A = A})
          (hPropExt
            (isPreorder .isPropValuedPreorder x z)
            (isPreorder .isPropValuedPreorder y z)
            (λ x≤z → isPreorder .isTransPreorder y x z y≤x x≤z)
            (λ y≤z → isPreorder .isTransPreorder x y z x≤y y≤z)) })
      (λ { x y z (y≤z , z≤y) →
        Σ≡Prop
          (λ A → isPropIsProp {A = A})
          (hPropExt
            (isPreorder .isPropValuedPreorder x y)
            (isPreorder .isPropValuedPreorder x z)
            (λ x≤y → isPreorder .isTransPreorder x y z x≤y y≤z)
            (λ x≤z → isPreorder .isTransPreorder x z y x≤z z≤y)) })
      a
      b

  isRefl≤ᴿ : ∀ x → ⟨ x ≤ᴿ x ⟩ 
  isRefl≤ᴿ x = elimProp (λ x → (x ≤ᴿ x) .snd) (λ x → isPreorder .isReflPreorder x) x

  isAntisym≤ᴿ : ∀ x y (p : ⟨ x ≤ᴿ y ⟩) (q : ⟨ y ≤ᴿ x ⟩) → x ≡ y
  isAntisym≤ᴿ x y =
    elimProp2
      {P = λ x y → ∀ (p : ⟨ x ≤ᴿ y ⟩) (q : ⟨ y ≤ᴿ x ⟩) → x ≡ y }
      (λ x y → isPropΠ λ x≤y → isPropΠ λ y≤x → squash/ x y)
      (λ x y x≤y y≤x → eq/ x y (x≤y , y≤x))
      x
      y

  isTrans≤ᴿ : ∀ x y z → ⟨ x ≤ᴿ y ⟩ → ⟨ y ≤ᴿ z ⟩ → ⟨ x ≤ᴿ z ⟩
  isTrans≤ᴿ x y z = elimProp3
                     {P = λ x y z → (p : ⟨ x ≤ᴿ y ⟩) (q : ⟨ y ≤ᴿ z ⟩) → ⟨ x ≤ᴿ z ⟩}
                     (λ x y z → isPropΠ2 λ x≤y y≤z → (x ≤ᴿ z) .snd)
                     (λ x y z x≤y y≤z → isPreorder .isTransPreorder x y z x≤y y≤z)
                     x
                     y
                     z

  _⊑_ : PosetReflection _≤_ → PosetReflection _≤_ → Type ℓ'
  x ⊑ y = ⟨ x ≤ᴿ y ⟩

  isPropValued⊑ : ∀ x y → isProp (x ⊑ y)
  isPropValued⊑ x y = (x ≤ᴿ y) .snd

  poset⊑ : Poset _ _
  poset⊑ = poset (PosetReflection _≤_) _⊑_ (isposet squash/ isPropValued⊑ isRefl≤ᴿ isTrans≤ᴿ isAntisym≤ᴿ)
