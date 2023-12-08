{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Base {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  record Assembly (X : Type ℓ) : Type (ℓ-suc ℓ) where
    infix 25 _⊩_
    field
      isSetX : isSet X
      _⊩_ : A → X → Type ℓ
      ⊩isPropValued : ∀ a x → isProp (a ⊩ x)
      ⊩surjective : ∀ x → ∃[ a ∈ A ] a ⊩ x


  AssemblyΣ : Type ℓ → Type _
  AssemblyΣ X =
    Σ[ isSetX ∈ isSet X ]
    Σ[ _⊩_ ∈ (A → X → Type ℓ) ]
    Σ[ ⊩isPropValued ∈ (∀ a x → isProp (a ⊩ x)) ]
    (∀ x → ∃[ a ∈ A ] a ⊩ x)
  
  unquoteDecl AssemblyIsoΣ = declareRecordIsoΣ AssemblyIsoΣ (quote Assembly)

  open Assembly public

  
