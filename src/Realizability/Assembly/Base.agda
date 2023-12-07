{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Base {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  record Assembly (X : Type ℓ) : Type (ℓ-suc ℓ) where
    infix 25 _⊩_
    field
      isSetX : isSet X
      _⊩_ : A → X → Type ℓ
      ⊩isPropValued : ∀ a x → isProp (a ⊩ x)
      ⊩surjective : ∀ x → ∃[ a ∈ A ] a ⊩ x

  open Assembly public
