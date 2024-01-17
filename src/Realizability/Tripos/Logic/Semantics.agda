{-# OPTIONS --allow-unsolved-metas #-}
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
open PredicateProperties hiding (_≤_ ; isTrans≤)
open Morphism {ℓ' = ℓ'} {ℓ'' = ℓ''}
Predicate = Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''}
RelationInterpretation : ∀ {n : ℕ} → (Vec Sort n) → Type _
RelationInterpretation {n} relSym = (∀ i →  Predicate ⟨ ⟦ lookup i relSym ⟧ˢ ⟩)
module Interpretation
  {n : ℕ}
  (relSym : Vec Sort n)
  (⟦_⟧ʳ : RelationInterpretation relSym) (isNonTrivial : s ≡ k → ⊥) where
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

  -- R for renamings and r for relations
  ⟦_⟧ᴿ : ∀ {Γ Δ} → Renaming Γ Δ → ⟨ ⟦ Γ ⟧ᶜ ⟩ → ⟨ ⟦ Δ ⟧ᶜ ⟩
  ⟦ id ⟧ᴿ ctx = ctx
  ⟦ drop ren ⟧ᴿ (ctx , _) = ⟦ ren ⟧ᴿ ctx
  ⟦ keep ren ⟧ᴿ (ctx , s) = (⟦ ren ⟧ᴿ ctx) , s

  -- B for suBstitution and s for sorts
  ⟦_⟧ᴮ : ∀ {Γ Δ} → Substitution Γ Δ → ⟨ ⟦ Γ ⟧ᶜ ⟩ → ⟨ ⟦ Δ ⟧ᶜ ⟩
  ⟦ id ⟧ᴮ ctx = ctx
  ⟦ t , sub ⟧ᴮ ctx = (⟦ sub ⟧ᴮ ctx) , (⟦ t ⟧ᵗ ctx)
  ⟦ drop sub ⟧ᴮ (ctx , s) = ⟦ sub ⟧ᴮ ctx

  renamingVarSound : ∀ {Γ Δ s} → (ren : Renaming Γ Δ) → (v : s ∈ Δ) → ⟦ renamingVar ren v ⟧ⁿ ≡ ⟦ v ⟧ⁿ ∘ ⟦ ren ⟧ᴿ
  renamingVarSound {Γ} {.Γ} {s} id v = refl
  renamingVarSound {.(_ ′ _)} {Δ} {s} (drop ren) v = funExt λ { (⟦Γ⟧ , ⟦s⟧) i → renamingVarSound ren v i ⟦Γ⟧ }
  renamingVarSound {.(_ ′ s)} {.(_ ′ s)} {s} (keep ren) here = funExt λ { (⟦Γ⟧ , ⟦s⟧) i → ⟦s⟧ }
  renamingVarSound {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (there v) = funExt λ { (⟦Γ⟧ , ⟦s⟧) i → renamingVarSound ren v i ⟦Γ⟧ }

  renamingTermSound : ∀ {Γ Δ s} → (ren : Renaming Γ Δ) → (t : Term Δ s) → ⟦ renamingTerm ren t ⟧ᵗ ≡ ⟦ t ⟧ᵗ ∘ ⟦ ren ⟧ᴿ
  renamingTermSound {Γ} {.Γ} {s} id t = refl
  renamingTermSound {.(_ ′ _)} {Δ} {s} (drop ren) (var x) = funExt λ { (⟦Γ⟧ , ⟦s⟧) i → renamingVarSound ren x i ⟦Γ⟧ }
  renamingTermSound {.(_ ′ _)} {Δ} {.(_ `× _)} r@(drop ren) (t `, t₁) = funExt λ { (⟦Γ⟧ , ⟦s⟧) i → renamingTermSound r t i (⟦Γ⟧ , ⟦s⟧) , renamingTermSound r t₁ i (⟦Γ⟧ , ⟦s⟧) }
  renamingTermSound {.(_ ′ _)} {Δ} {s} r@(drop ren) (π₁ t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → renamingTermSound r t i x .fst }
  renamingTermSound {.(_ ′ _)} {Δ} {s} r@(drop ren) (π₂ t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → renamingTermSound r t i x .snd }
  renamingTermSound {.(_ ′ _)} {Δ} {s} r@(drop ren) (fun f t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → f (renamingTermSound r t i x) }
  renamingTermSound {.(_ ′ _)} {.(_ ′ _)} {s} r@(keep ren) (var v) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → renamingVarSound r v i x }
  renamingTermSound {.(_ ′ _)} {.(_ ′ _)} {.(_ `× _)} r@(keep ren) (t `, t₁) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → (renamingTermSound r t i x) , (renamingTermSound r t₁ i x) }
  renamingTermSound {.(_ ′ _)} {.(_ ′ _)} {s} r@(keep ren) (π₁ t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → renamingTermSound r t i x .fst }
  renamingTermSound {.(_ ′ _)} {.(_ ′ _)} {s} r@(keep ren) (π₂ t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → renamingTermSound r t i x .snd }
  renamingTermSound {.(_ ′ _)} {.(_ ′ _)} {s} r@(keep ren) (fun f t) = funExt λ { x@(⟦Γ⟧ , ⟦s⟧) i → f (renamingTermSound r t i x) }

  substitutionVarSound : ∀ {Γ Δ s} → (subs : Substitution Γ Δ) → (v : s ∈ Δ) → ⟦ substitutionVar subs v ⟧ᵗ ≡ ⟦ v ⟧ⁿ ∘ ⟦ subs ⟧ᴮ
  substitutionVarSound {Γ} {.Γ} {s} id t = refl
  substitutionVarSound {Γ} {.(_ ′ s)} {s} (t' , subs) here = funExt λ ⟦Γ⟧ → refl
  substitutionVarSound {Γ} {.(_ ′ _)} {s} (t' , subs) (there t) = funExt λ ⟦Γ⟧ i → substitutionVarSound subs t i ⟦Γ⟧
  substitutionVarSound {.(_ ′ _)} {Δ} {s} r@(drop subs) t =
    -- TODO : Fix unsolved constraints
    funExt
      λ { x@(⟦Γ⟧ , ⟦s⟧) →
        ⟦ substitutionVar (drop subs) t ⟧ᵗ (⟦Γ⟧ , ⟦s⟧)
          ≡[ i ]⟨  renamingTermSound (drop id) (substitutionVar subs t) i (⟦Γ⟧ , ⟦s⟧)  ⟩
        ⟦ substitutionVar subs t ⟧ᵗ (⟦ drop id ⟧ᴿ x)
          ≡⟨ refl ⟩
        ⟦ substitutionVar subs t ⟧ᵗ ⟦Γ⟧
          ≡[ i ]⟨ substitutionVarSound subs t i ⟦Γ⟧ ⟩
        ⟦ t ⟧ⁿ (⟦ subs ⟧ᴮ ⟦Γ⟧)
          ∎}

  substitutionTermSound : ∀ {Γ Δ s} → (subs : Substitution Γ Δ) → (t : Term Δ s) → ⟦ substitutionTerm subs t ⟧ᵗ ≡ ⟦ t ⟧ᵗ ∘ ⟦ subs ⟧ᴮ
  substitutionTermSound {Γ} {Δ} {s} subs (var x) = substitutionVarSound subs x
  substitutionTermSound {Γ} {Δ} {.(_ `× _)} subs (t `, t₁) = funExt λ x i → (substitutionTermSound subs t i x) , (substitutionTermSound subs t₁ i x)
  substitutionTermSound {Γ} {Δ} {s} subs (π₁ t) = funExt λ x i → substitutionTermSound subs t i x .fst
  substitutionTermSound {Γ} {Δ} {s} subs (π₂ t) = funExt λ x i → substitutionTermSound subs t i x .snd
  substitutionTermSound {Γ} {Δ} {s} subs (fun f t) = funExt λ x i → f (substitutionTermSound subs t i x)

module Soundness
  {n}
  {relSym : Vec Sort n}
  (isNonTrivial : s ≡ k → ⊥)
  (⟦_⟧ʳ : RelationInterpretation relSym) where
  open Relational relSym
  open Interpretation relSym ⟦_⟧ʳ isNonTrivial

  infix 24 _⊨_

  module _ {Γ : Context} where

    open PredicateProperties {ℓ'' = ℓ''} ⟨ ⟦ Γ ⟧ᶜ ⟩

    _⊨_ : Formula Γ → Formula Γ → Type _
    ϕ ⊨ ψ = ⟦ ϕ ⟧ᶠ ≤ ⟦ ψ ⟧ᶠ

    private
      variable
        ϕ ψ θ χ : Formula Γ

    cut : ∀ {ϕ ψ θ} → ϕ ⊨ ψ → ψ ⊨ θ → ϕ ⊨ θ
    cut {ϕ} {ψ} {θ} ϕ⊨ψ ψ⊨θ = isTrans≤ ⟦ ϕ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ θ ⟧ᶠ ϕ⊨ψ ψ⊨θ

    
