open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.HITs.SetQuotients
open import Tripoi.HeytingAlgebra
open import Tripoi.PosetReflection

module Tripoi.Tripos where

record TriposStructure {ℓ ℓ' ℓ''} : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where
  field
    𝓟⟅_⟆ : Type ℓ → Type ℓ'
    _⊢_ : ∀ {I : Type ℓ} → 𝓟⟅ I ⟆ → 𝓟⟅ I ⟆ → Type ℓ''
    𝓟⊤⟅_⟆ : (I : Type ℓ) → 𝓟⟅ I ⟆
    𝓟⊥⟅_⟆ : (I : Type ℓ) → 𝓟⟅ I ⟆
    ⊢isPreorder : ∀ {I : Type ℓ} → IsPreorder (_⊢_ {I})
  field
    ⊢isHeytingPrealgebra : ∀ {I : Type ℓ} → IsHeytingAlgebra {H = PosetReflection (_⊢_ {I})} [ 𝓟⊥⟅ I ⟆ ] [ 𝓟⊤⟅ I ⟆ ] {!!} {!!} {!!}
    𝓟⟪_⟫ : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ I ⟆ → 𝓟⟅ J ⟆
    `∀[_] : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ J ⟆ → 𝓟⟅ I ⟆
    `∃[_] : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ J ⟆ → 𝓟⟅ I ⟆
    
