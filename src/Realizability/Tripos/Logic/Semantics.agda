open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary.Order.Preorder

module
  Realizability.Tripos.Logic.Semantics
  {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where
open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate')
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open import Realizability.Tripos.Prealgebra.Meets.Identity ca
open import Realizability.Tripos.Prealgebra.Joins.Identity ca
open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate'
open PredicateProperties
open Morphism {ℓ' = ℓ'} {ℓ'' = ℓ''}
Predicate = Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''}

module Interpretation (𝓛 : (s : Sort) → Predicate (⟦ s ⟧ˢ .fst)) (isNonTrivial : s ≡ k → ⊥) where

  ⟦_⟧ᶜ : Context → hSet ℓ'
  ⟦ [] ⟧ᶜ = Unit* , isSetUnit* 
  ⟦ c ′ x ⟧ᶜ = (⟦ c ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) , isSet× (⟦ c ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)

  ⟦_⟧ⁿ : ∀ {Γ s} → s ∈ Γ → ⟨ ⟦ Γ ⟧ᶜ ⟩ → ⟨ ⟦ s ⟧ˢ ⟩
  ⟦_⟧ⁿ {.(_ ′ s)} {s} _∈_.here (⟦Γ⟧ , ⟦s⟧) = ⟦s⟧
  ⟦_⟧ⁿ {.(_ ′ _)} {s} (_∈_.there s∈Γ) (⟦Γ⟧ , ⟦s⟧) = ⟦ s∈Γ ⟧ⁿ ⟦Γ⟧

  ⟦_⟧ᵗ : ∀ {Γ s} → Term Γ s → ⟨ ⟦ Γ ⟧ᶜ ⟩ → ⟨ ⟦ s ⟧ˢ ⟩
  ⟦_⟧ᵗ {Γ} {s} (var x) ⟦Γ⟧ = ⟦ x ⟧ⁿ ⟦Γ⟧
  ⟦_⟧ᵗ {Γ} {s} (t `, t₁) ⟦Γ⟧ = (⟦ t ⟧ᵗ ⟦Γ⟧) , (⟦ t₁ ⟧ᵗ ⟦Γ⟧)
  ⟦_⟧ᵗ {Γ} {s} (π₁ t) ⟦Γ⟧ = fst (⟦ t ⟧ᵗ ⟦Γ⟧)
  ⟦_⟧ᵗ {Γ} {s} (π₂ t) ⟦Γ⟧ = snd (⟦ t ⟧ᵗ ⟦Γ⟧)
  ⟦_⟧ᵗ {Γ} {s} (fun x t) ⟦Γ⟧ = x (⟦ t ⟧ᵗ ⟦Γ⟧)

  ⟦_⟧ᶠ : ∀ {Γ} → Formula Γ → Predicate ⟨ ⟦ Γ ⟧ᶜ ⟩
  ⟦_⟧ᶠ {[]} ⊤ᵗ = pre1 Unit* isSetUnit* isNonTrivial
  ⟦_⟧ᶠ {[]} ⊥ᵗ = pre0 Unit* isSetUnit* isNonTrivial
  ⟦_⟧ᶠ {[]} (f `∨ f₁) = _⊔_ Unit* ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {[]} (f `∧ f₁) = _⊓_ Unit* ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {[]} (f `→ f₁) = _⇒_ Unit* ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {[]} (`¬ f) = _⇒_ Unit* ⟦ f ⟧ᶠ ⟦ ⊥ᵗ ⟧ᶠ
  ⟦_⟧ᶠ {[]} (`∃ f) = {!!}
  ⟦_⟧ᶠ {[]} (`∀ f) = {!!}
  ⟦_⟧ᶠ {Γ ′ x} ⊤ᵗ = pre1 (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) isNonTrivial
  ⟦_⟧ᶠ {Γ ′ x} ⊥ᵗ = pre0 (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) isNonTrivial
  ⟦_⟧ᶠ {Γ ′ x} (f `∨ f₁) = _⊔_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (f `∧ f₁) = _⊓_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (f `→ f₁) = _⇒_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (`¬ f) = _⇒_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ ⊥ᵗ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (`∃ f) = {!!}
  ⟦_⟧ᶠ {Γ ′ x} (`∀ f) = {!!}
