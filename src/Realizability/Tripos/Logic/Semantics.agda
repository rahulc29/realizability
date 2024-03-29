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
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec* to ⊥rec*)
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
  ⟦_⟧ᶠ {Γ} ⊤ᵗ = pre1 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial
  ⟦_⟧ᶠ {Γ} ⊥ᵗ = pre0 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial
  ⟦_⟧ᶠ {Γ} (form `∨ form₁) = _⊔_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ form ⟧ᶠ ⟦ form₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (form `∧ form₁) = _⊓_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ form ⟧ᶠ ⟦ form₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (form `→ form₁) = _⇒_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ form ⟧ᶠ ⟦ form₁ ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (`¬ form) = _⇒_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ form ⟧ᶠ ⟦ ⊥ᵗ {Γ = Γ} ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (`∃ {B = B} form) = `∃[_] (isSet× (str ⟦ Γ ⟧ᶜ) (str ⟦ B ⟧ˢ)) (str ⟦ Γ ⟧ᶜ) (λ { (⟦Γ⟧ , ⟦B⟧) → ⟦Γ⟧ }) ⟦ form ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (`∀ {B = B} form) = `∀[_] (isSet× (str ⟦ Γ ⟧ᶜ) (str ⟦ B ⟧ˢ)) (str ⟦ Γ ⟧ᶜ) (λ { (⟦Γ⟧ , ⟦B⟧) → ⟦Γ⟧ }) ⟦ form ⟧ᶠ
  ⟦_⟧ᶠ {Γ} (rel R t) = ⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ lookup R relSym ⟧ˢ) ⟦ t ⟧ᵗ ⟦ R ⟧ʳ

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

  substitutionFormulaSound : ∀ {Γ Δ} → (subs : Substitution Γ Δ) → (f : Formula Δ) → ⟦ substitutionFormula subs f ⟧ᶠ ≡ ⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ Δ ⟧ᶜ) ⟦ subs ⟧ᴮ ⟦ f ⟧ᶠ
  substitutionFormulaSound {Γ} {Δ} subs ⊤ᵗ =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (pre1 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial)
      (⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ Δ ⟧ᶜ) ⟦ subs ⟧ᴮ (pre1 ⟨ ⟦ Δ ⟧ᶜ ⟩ (str ⟦ Δ ⟧ᶜ) isNonTrivial))
      (λ ⟦Γ⟧ a tt* → tt*)
      λ ⟦Γ⟧ a tt* → tt*
  substitutionFormulaSound {Γ} {Δ} subs ⊥ᵗ =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (pre0 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial)
      (⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ Δ ⟧ᶜ) ⟦ subs ⟧ᴮ (pre0 ⟨ ⟦ Δ ⟧ᶜ ⟩ (str ⟦ Δ ⟧ᶜ) isNonTrivial))
      (λ ⟦Γ⟧ a bot → ⊥rec* bot)
      λ ⟦Γ⟧ a bot → bot
  substitutionFormulaSound {Γ} {Δ} subs (f `∨ f₁) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (_⊔_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ substitutionFormula subs f ⟧ᶠ ⟦ substitutionFormula subs f₁ ⟧ᶠ)
      (⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ Δ ⟧ᶜ) ⟦ subs ⟧ᴮ (_⊔_ ⟨ ⟦ Δ ⟧ᶜ ⟩ ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ))
      (λ ⟦Γ⟧ a a⊩f'⊔f₁' → {!!})
      {!!}
  substitutionFormulaSound {Γ} {Δ} subs (f `∧ f₁) = {!!}
  substitutionFormulaSound {Γ} {Δ} subs (f `→ f₁) = {!!}
  substitutionFormulaSound {Γ} {Δ} subs (`¬ f) = {!!}
  substitutionFormulaSound {Γ} {Δ} subs (`∃ f) = {!!}
  substitutionFormulaSound {Γ} {Δ} subs (`∀ f) = {!!}
  substitutionFormulaSound {Γ} {Δ} subs (rel k₁ x) = {!!}

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

    
