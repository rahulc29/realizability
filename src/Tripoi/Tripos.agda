open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Sigma
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
  PredicateAlgebra : ∀ I → Type _
  PredicateAlgebra I = PosetReflection (_⊢_ {I})
  field
    _∨l_ : ∀ {I} → PredicateAlgebra I → PredicateAlgebra I → PredicateAlgebra I
    _∧l_ : ∀ {I} → PredicateAlgebra I → PredicateAlgebra I → PredicateAlgebra I
    _→l_ : ∀ {I} → PredicateAlgebra I → PredicateAlgebra I → PredicateAlgebra I
    ⊢isHeytingPrealgebra : ∀ {I : Type ℓ} → IsHeytingAlgebra {H = PosetReflection (_⊢_ {I})} [ 𝓟⊥⟅ I ⟆ ] [ 𝓟⊤⟅ I ⟆ ] _∨l_ _∧l_ _→l_
    𝓟⟪_⟫ : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ I ⟆ → 𝓟⟅ J ⟆
    `∀[_] : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ J ⟆ → 𝓟⟅ I ⟆
    `∃[_] : ∀ {I J : Type ℓ} → (f : J → I) → 𝓟⟅ J ⟆ → 𝓟⟅ I ⟆
    `∃isLeftAdjoint  : ∀ {I J : Type ℓ} → (f : I → J) → (ϕ : 𝓟⟅ I ⟆) → (ψ : 𝓟⟅ J ⟆) → `∃[ f ] ϕ ⊢ ψ ≡ ϕ ⊢ 𝓟⟪ f ⟫ ψ
    `∀isRightAdjoint : ∀ {I J : Type ℓ} → (f : I → J) → (ϕ : 𝓟⟅ I ⟆) → (ψ : 𝓟⟅ J ⟆) → `∀[ f ] ϕ ⊢ ψ ≡ ϕ ⊢ 𝓟⟪ f ⟫ ψ
    `∃BeckChevalley :
      ∀ {I J K : Type ℓ}
      → (f : J → I)
      → (g : K → I)
      → let 
          L = Σ[ k ∈ K ] Σ[ j ∈ J ] g k ≡ f j
        in
        𝓟⟪ g ⟫ ∘ `∃[ f ] ≡ `∃[ (λ (l : L) → fst l) ] ∘ 𝓟⟪ (λ l → fst (snd l)) ⟫
    `∀BeckChevalley :
      ∀ {I J K : Type ℓ}
      → (f : J → I)
      → (g : K → I)
      → let 
          L = Σ[ k ∈ K ] Σ[ j ∈ J ] g k ≡ f j
        in
        𝓟⟪ g ⟫ ∘ `∀[ f ] ≡ `∀[ (λ (l : L) → fst l) ] ∘ 𝓟⟪ (λ l → fst (snd l)) ⟫
        
