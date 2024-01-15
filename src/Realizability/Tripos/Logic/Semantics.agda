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
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Fin
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

module Interpretation
  {n : ℕ}
  (relSym : Vec Sort n)
  (⟦_⟧ʳ : ∀ i → Predicate (⟦ lookup i relSym ⟧ˢ .fst)) (isNonTrivial : s ≡ k → ⊥) where
  open Relational relSym

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
  ⟦_⟧ᶠ {[]} (`¬ f) = _⇒_ Unit* ⟦ f ⟧ᶠ ⟦ ⊥ᵗ {Γ = []} ⟧ᶠ
  ⟦_⟧ᶠ {[]} (`∃ {B = B} f) =
    `∃[_]
    {X = Unit* × ⟦ B ⟧ˢ .fst}
    {Y = Unit*}
    (isSet× isSetUnit* (⟦ B ⟧ˢ .snd))
    isSetUnit*
    fst
    ⟦ f ⟧ᶠ
  ⟦_⟧ᶠ {[]} (`∀ {B = B} f) =
    `∀[_]
    {X = Unit* × ⟦ B ⟧ˢ .fst}
    {Y = Unit*}
    (isSet× isSetUnit* (⟦ B ⟧ˢ .snd))
    isSetUnit*
    fst
    ⟦ f ⟧ᶠ
  ⟦_⟧ᶠ {[]} (rel R t) = ⋆_ isSetUnit* (str ⟦ lookup R relSym ⟧ˢ) ⟦ t ⟧ᵗ ⟦ R ⟧ʳ
  ⟦_⟧ᶠ {Γ ′ x} ⊤ᵗ = pre1 (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) isNonTrivial
  ⟦_⟧ᶠ {Γ ′ x} ⊥ᵗ = pre0 (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) isNonTrivial
  ⟦_⟧ᶠ {Γ ′ x} (f `∨ f₁) = _⊔_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (f `∧ f₁) = _⊓_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (f `→ f₁) = _⇒_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (`¬ f) = _⇒_ (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) ⟦ f ⟧ᶠ ⟦ ⊥ᵗ {Γ = Γ ′ x} ⟧ᶠ
  ⟦_⟧ᶠ {Γ ′ x} (`∃ {B = B} f) =
    `∃[_]
    {X = (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) × ⟦ B ⟧ˢ .fst}
    {Y = ⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst}
    (isSet× (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) (⟦ B ⟧ˢ .snd))
    (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd))
    fst
    (⟦ f ⟧ᶠ)
  ⟦_⟧ᶠ {Γ ′ x} (`∀ {B = B} f) =
    `∀[_]
    {X = (⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst) × ⟦ B ⟧ˢ .fst}
    {Y = ⟦ Γ ⟧ᶜ .fst × ⟦ x ⟧ˢ .fst}
    (isSet× (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd)) (⟦ B ⟧ˢ .snd))
    (isSet× (⟦ Γ ⟧ᶜ .snd) (⟦ x ⟧ˢ .snd))
    fst
    (⟦ f ⟧ᶠ)
  ⟦_⟧ᶠ {Γ ′ x} (rel R t) = ⋆_ (str ⟦ Γ ′ x ⟧ᶜ) (str ⟦ lookup R relSym ⟧ˢ) ⟦ t ⟧ᵗ ⟦ R ⟧ʳ
