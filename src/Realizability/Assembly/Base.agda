{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
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
    Σ[ _⊩_ ∈ (A → X → hProp ℓ) ]
    (∀ x → ∃[ a ∈ A ] ⟨ a ⊩ x ⟩)

  AssemblyΣX→isSetX : ∀ X → AssemblyΣ X → isSet X
  AssemblyΣX→isSetX X (isSetX , _ , _) = isSetX

  AssemblyΣX→⊩ : ∀ X → AssemblyΣ X → (A → X → hProp ℓ)
  AssemblyΣX→⊩ X (_ , ⊩ , _) = ⊩

  AssemblyΣX→⊩surjective : ∀ X → (asm : AssemblyΣ X) → (∀ x → ∃[ a ∈ A ] ⟨ AssemblyΣX→⊩ X asm a x ⟩)
  AssemblyΣX→⊩surjective X (_ , _ , ⊩surjective) = ⊩surjective

  isSetAssemblyΣ : ∀ X → isSet (AssemblyΣ X)
  isSetAssemblyΣ X = isSetΣ (isProp→isSet isPropIsSet) λ isSetX → isSetΣ (isSetΠ (λ a → isSetΠ λ x → isSetHProp)) λ _⊩_ → isSetΠ λ x → isProp→isSet isPropPropTrunc
  
  unquoteDecl AssemblyIsoΣ = declareRecordIsoΣ AssemblyIsoΣ (quote Assembly)

  open Assembly public

  
