{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Unit

module Realizability.PartialCombinatoryAlgebra {𝓢} where

open import Realizability.Partiality {𝓢}
open import Realizability.PartialApplicativeStructure {𝓢}
open ♯_
record PartialCombinatoryAlgebra {ℓ} (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
  field
    pas : PartialApplicativeStructure A
  open PartialApplicativeStructure pas public
  field
    fefermanStructure : Feferman pas
  open Feferman fefermanStructure public

module _ {ℓ} {A : Type ℓ} (pca : PartialCombinatoryAlgebra A) where
  open PartialCombinatoryAlgebra pca
  infix 11 _⊩_
  record Assembly : Type (ℓ-suc ℓ) where
    field
      X : Type ℓ
      isSetX : isSet X
      _⊩_ : A → X → Type ℓ
      ⊩-covers : ∀ x → Σ[ a ∈ A ] (a ⊩ x)

  record AssemblyMorphism (x y : Assembly) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
    open Assembly x renaming (_⊩_ to _⊩X_)
    open Assembly y renaming (X to Y ; _⊩_ to _⊩Y_)
    field
      mapping : X → Y
      realizer : A
      realizerSupports : ∀ x a → (a ⊩X x) → (realizer ⨾ a) .support
      realizerRealizes : ∀ x a → (a⊩x : a ⊩X x) → (realizer ⨾ a) .force (realizerSupports x a a⊩x) ⊩Y (mapping x)
  open Assembly
  open AssemblyMorphism
  idMorphism : ∀ X → AssemblyMorphism X X
  idMorphism X .mapping = λ x → x
  idMorphism X .realizer = {!!}
  idMorphism X .realizerSupports x a a⊩x = {!!}
  idMorphism X .realizerRealizes x a a⊩x = {!!}

  
      



