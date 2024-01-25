{-# OPTIONS --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
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
open CombinatoryAlgebra ca
private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate')
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open import Realizability.Tripos.Prealgebra.Meets.Identity ca
open import Realizability.Tripos.Prealgebra.Joins.Identity ca
open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
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
        ⟦ substitutionVar (drop subs) t ⟧ᵗ x
          ≡[ i ]⟨  renamingTermSound (drop id) (substitutionVar subs t) i x  ⟩
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

  semanticSubstitution : ∀ {Γ Δ} → (subs : Substitution Γ Δ) → Predicate ⟨ ⟦ Δ ⟧ᶜ ⟩ → Predicate ⟨ ⟦ Γ ⟧ᶜ ⟩
  semanticSubstitution {Γ} {Δ} subs = ⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ Δ ⟧ᶜ) ⟦ subs ⟧ᴮ

  -- Due to a shortcut in the soundness of negation termination checking fails
  -- TODO : Fix
  {-# TERMINATING #-}
  substitutionFormulaSound : ∀ {Γ Δ} → (subs : Substitution Γ Δ) → (f : Formula Δ) → ⟦ substitutionFormula subs f ⟧ᶠ ≡ semanticSubstitution subs ⟦ f ⟧ᶠ
  substitutionFormulaSound {Γ} {Δ} subs ⊤ᵗ =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (pre1 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial)
      (semanticSubstitution subs (pre1 ⟨ ⟦ Δ ⟧ᶜ ⟩ (str ⟦ Δ ⟧ᶜ) isNonTrivial))
      (λ γ a a⊩1γ → tt*)
      λ γ a a⊩1subsγ → tt*
  substitutionFormulaSound {Γ} {Δ} subs ⊥ᵗ =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (pre0 ⟨ ⟦ Γ ⟧ᶜ ⟩ (str ⟦ Γ ⟧ᶜ) isNonTrivial)
      (semanticSubstitution subs (pre0 ⟨ ⟦ Δ ⟧ᶜ ⟩ (str ⟦ Δ ⟧ᶜ) isNonTrivial))
      (λ _ _ bot → ⊥rec* bot)
      λ _ _ bot → bot
  substitutionFormulaSound {Γ} {Δ} subs (f `∨ f₁) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (_⊔_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ substitutionFormula subs f ⟧ᶠ ⟦ substitutionFormula subs f₁ ⟧ᶠ)
      (semanticSubstitution subs (_⊔_ ⟨ ⟦ Δ ⟧ᶜ ⟩ ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ))
      (λ γ a a⊩substFormFs →
        a⊩substFormFs >>=
          λ { (inl (pr₁a≡k , pr₂a⊩substFormF)) →
                   ∣ inl (pr₁a≡k , subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (substitutionFormulaSound subs f) pr₂a⊩substFormF) ∣₁
            ; (inr (pr₁a≡k' , pr₂a⊩substFormF₁)) →
                   ∣ inr (pr₁a≡k' , subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (substitutionFormulaSound subs f₁) pr₂a⊩substFormF₁) ∣₁ })
      λ γ a a⊩semanticSubsFs →
        a⊩semanticSubsFs >>=
          λ { (inl (pr₁a≡k , pr₂a⊩semanticSubsF)) →
                   ∣ inl (pr₁a≡k , (subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (sym (substitutionFormulaSound subs f)) pr₂a⊩semanticSubsF)) ∣₁
            ; (inr (pr₁a≡k' , pr₂a⊩semanticSubsF₁)) →
                   ∣ inr (pr₁a≡k' , (subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (sym (substitutionFormulaSound subs f₁)) pr₂a⊩semanticSubsF₁)) ∣₁ }
  substitutionFormulaSound {Γ} {Δ} subs (f `∧ f₁) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (_⊓_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ substitutionFormula subs f ⟧ᶠ ⟦ substitutionFormula subs f₁ ⟧ᶠ)
      (semanticSubstitution subs (_⊓_ ⟨ ⟦ Δ ⟧ᶜ ⟩ ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ))
      (λ γ a a⊩substFormulaFs →
        (subst (λ form → (pr₁ ⨾ a) ⊩ ∣ form ∣ γ) (substitutionFormulaSound subs f) (a⊩substFormulaFs .fst)) ,
        (subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (substitutionFormulaSound subs f₁) (a⊩substFormulaFs .snd)))
      λ γ a a⊩semanticSubstFs →
        (subst (λ form → (pr₁ ⨾ a) ⊩ ∣ form ∣ γ) (sym (substitutionFormulaSound subs f)) (a⊩semanticSubstFs .fst)) ,
        (subst (λ form → (pr₂ ⨾ a) ⊩ ∣ form ∣ γ) (sym (substitutionFormulaSound subs f₁)) (a⊩semanticSubstFs .snd))
  substitutionFormulaSound {Γ} {Δ} subs (f `→ f₁) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (_⇒_ ⟨ ⟦ Γ ⟧ᶜ ⟩ ⟦ substitutionFormula subs f ⟧ᶠ ⟦ substitutionFormula subs f₁ ⟧ᶠ)
      (semanticSubstitution subs (_⇒_ ⟨ ⟦ Δ ⟧ᶜ ⟩ ⟦ f ⟧ᶠ ⟦ f₁ ⟧ᶠ))
      (λ γ a a⊩substFormulaFs →
        λ b b⊩semanticSubstFs →
          subst
            (λ form → (a ⨾ b) ⊩ ∣ form ∣ γ)
            (substitutionFormulaSound subs f₁)
            (a⊩substFormulaFs
              b
              (subst
                (λ form → b ⊩ ∣ form ∣ γ)
                (sym (substitutionFormulaSound subs f))
                b⊩semanticSubstFs)))
      λ γ a a⊩semanticSubstFs →
        λ b b⊩substFormulaFs →
          subst
            (λ form → (a ⨾ b) ⊩ ∣ form ∣ γ)
            (sym (substitutionFormulaSound subs f₁))
            (a⊩semanticSubstFs
              b
              (subst
                (λ form → b ⊩ ∣ form ∣ γ)
                (substitutionFormulaSound subs f)
                b⊩substFormulaFs))
  substitutionFormulaSound {Γ} {Δ} subs (`¬ f) =
    substitutionFormulaSound subs (f `→ ⊥ᵗ)
  substitutionFormulaSound {Γ} {Δ} subs (`∃ {B = B} f) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (`∃[ isSet× (str ⟦ Γ ⟧ᶜ) (str ⟦ B ⟧ˢ) ] (str ⟦ Γ ⟧ᶜ) (λ { (f , s) → f }) ⟦ substitutionFormula (var here , drop subs) f ⟧ᶠ)
      (semanticSubstitution subs (`∃[ isSet× (str ⟦ Δ ⟧ᶜ) (str ⟦ B ⟧ˢ) ] (str ⟦ Δ ⟧ᶜ) (λ { (γ , b) → γ }) ⟦ f ⟧ᶠ))
      (λ γ a a⊩πSubstFormulaF →
        a⊩πSubstFormulaF >>=
          λ { ((γ' , b) , γ'≡γ , a⊩substFormFγ') →
            ∣ ((⟦ subs ⟧ᴮ γ') , b) ,
              ((cong ⟦ subs ⟧ᴮ γ'≡γ) ,
                (subst
                  (λ form → a ⊩ ∣ form ∣ (γ' , b))
                  (substitutionFormulaSound (var here , drop subs) f)
                  a⊩substFormFγ' )) ∣₁ })
      λ γ a a⊩semanticSubstF →
        a⊩semanticSubstF >>=
          λ (x@(δ , b) , δ≡subsγ , a⊩fx) →
            ∣ (γ , b) ,
              (refl ,
                (subst
                  (λ form → a ⊩ ∣ form ∣ (γ , b))
                  (sym (substitutionFormulaSound (var here , drop subs) f))
                  (subst (λ x → a ⊩ ∣ ⟦ f ⟧ᶠ ∣ (x , b)) δ≡subsγ a⊩fx))) ∣₁
  substitutionFormulaSound {Γ} {Δ} subs (`∀ {B = B} f) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (`∀[ isSet× (str ⟦ Γ ⟧ᶜ) (str ⟦ B ⟧ˢ) ] (str ⟦ Γ ⟧ᶜ) (λ { (f , s) → f }) ⟦ substitutionFormula (var here , drop subs) f ⟧ᶠ)
      (semanticSubstitution subs (`∀[ isSet× (str ⟦ Δ ⟧ᶜ) (str ⟦ B ⟧ˢ) ] (str ⟦ Δ ⟧ᶜ) (λ { (f , s) → f }) ⟦ f ⟧ᶠ))
      (λ γ a a⊩substFormF →
        λ { r x@(δ , b) δ≡subsγ →
          subst
            (λ g → (a ⨾ r) ⊩ ∣ ⟦ f ⟧ᶠ ∣ (g , b))
            (sym δ≡subsγ)
            (subst
              (λ form → (a ⨾ r) ⊩ ∣ form ∣ (γ , b))
              (substitutionFormulaSound (var here , drop subs) f)
              (a⊩substFormF r (γ , b) refl)) })
      λ γ a a⊩semanticSubsF →
        λ { r x@(γ' , b) γ'≡γ →
          subst
            (λ form → (a ⨾ r) ⊩ ∣ form ∣ (γ' , b))
            (sym (substitutionFormulaSound (var here , drop subs) f))
            (subst
              (λ g → (a ⨾ r) ⊩ ∣ ⟦ f ⟧ᶠ ∣ (g , b))
              (cong ⟦ subs ⟧ᴮ (sym γ'≡γ))
              (a⊩semanticSubsF r (⟦ subs ⟧ᴮ γ , b) refl)) }
  substitutionFormulaSound {Γ} {Δ} subs (rel R t) =
    Predicate≡
      ⟨ ⟦ Γ ⟧ᶜ ⟩
      (⋆_ (str ⟦ Γ ⟧ᶜ) (str ⟦ lookup R relSym ⟧ˢ) ⟦ substitutionTerm subs t ⟧ᵗ ⟦ R ⟧ʳ)
      (semanticSubstitution subs (⋆_ (str ⟦ Δ ⟧ᶜ) (str ⟦ lookup R relSym ⟧ˢ) ⟦ t ⟧ᵗ ⟦ R ⟧ʳ))
      (λ γ a a⊩substTR →
        subst (λ transform → a ⊩ ∣ ⟦ R ⟧ʳ ∣ (transform γ)) (substitutionTermSound subs t) a⊩substTR)
      λ γ a a⊩semSubst →
        subst (λ transform → a ⊩ ∣ ⟦ R ⟧ʳ ∣ (transform γ)) (sym (substitutionTermSound subs t)) a⊩semSubst

module Soundness
  {n}
  {relSym : Vec Sort n}
  (isNonTrivial : s ≡ k → ⊥)
  (⟦_⟧ʳ : RelationInterpretation relSym) where
  open Relational relSym
  open Interpretation relSym ⟦_⟧ʳ isNonTrivial
  -- Acknowledgements : 1lab's "the internal logic of a regular hyperdoctrine"
  infix 35 _⊨_
  
  module PredProps = PredicateProperties
  
  _⊨_ : ∀ {Γ} → Formula Γ → Formula Γ → Type (ℓ-max (ℓ-max ℓ ℓ'') ℓ')
  _⊨_ {Γ} ϕ ψ = ⟦ ϕ ⟧ᶠ ≤ ⟦ ψ ⟧ᶠ where open PredProps ⟨ ⟦ Γ ⟧ᶜ ⟩

  entails = _⊨_

  private
    variable
      Γ Δ : Context
      ϕ ψ θ : Formula Γ
      χ μ ν : Formula Δ

  cut : ∀ {Γ} {ϕ ψ θ : Formula Γ} → ϕ ⊨ ψ → ψ ⊨ θ → ϕ ⊨ θ
  cut {Γ} {ϕ} {ψ} {θ} ϕ⊨ψ ψ⊨θ = isTrans≤ ⟦ ϕ ⟧ᶠ ⟦ ψ ⟧ᶠ ⟦ θ ⟧ᶠ ϕ⊨ψ ψ⊨θ where open PredProps ⟨ ⟦ Γ ⟧ᶜ ⟩

  substitutionEntailment : ∀ {Γ Δ} (subs : Substitution Γ Δ) → {ϕ ψ : Formula Δ} → ϕ ⊨ ψ → substitutionFormula subs ϕ ⊨ substitutionFormula subs ψ
  substitutionEntailment {Γ} {Δ} subs {ϕ} {ψ} ϕ⊨ψ =
    subst2
      (λ ϕ' ψ' → ϕ' ≤Γ ψ')
      (sym (substitutionFormulaSound subs ϕ))
      (sym (substitutionFormulaSound subs ψ))
      (ϕ⊨ψ >>=
        λ { (a , a⊩ϕ≤ψ) →
          ∣ a , (λ γ b b⊩ϕsubsγ → a⊩ϕ≤ψ (⟦ subs ⟧ᴮ γ) b b⊩ϕsubsγ) ∣₁ }) where
      open PredProps {ℓ'' = ℓ''} ⟨ ⟦ Γ ⟧ᶜ ⟩ renaming (_≤_ to _≤Γ_)
      open PredProps {ℓ'' = ℓ''} ⟨ ⟦ Δ ⟧ᶜ ⟩ renaming (_≤_ to _≤Δ_)

  `∧intro : ∀ {Γ} {ϕ ψ θ : Formula Γ} → ϕ ⊨ ψ → entails ϕ θ → entails ϕ (ψ `∧ θ)
  `∧intro {Γ} {ϕ} {ψ} {θ} ϕ⊨ψ ϕ⊨θ =
    do
      (a , a⊩ϕ⊨ψ) ← ϕ⊨ψ
      (b , b⊩ϕ⊨θ) ← ϕ⊨θ
      let
        prover : ApplStrTerm as 1
        prover = ` pair ̇ (` a ̇ # fzero) ̇ (` b ̇ # fzero)
      return
        (λ* prover ,
          λ γ r r⊩ϕγ →
            let
              proofEq : λ* prover ⨾ r ≡ pair ⨾ (a ⨾ r) ⨾ (b ⨾ r)
              proofEq = λ*ComputationRule prover (r ∷ [])

              pr₁proofEq : pr₁ ⨾ (λ* prover ⨾ r) ≡ a ⨾ r
              pr₁proofEq =
                pr₁ ⨾ (λ* prover ⨾ r)
                  ≡⟨ cong (λ x → pr₁ ⨾ x) proofEq ⟩
                pr₁ ⨾ (pair ⨾ (a ⨾ r) ⨾ (b ⨾ r))
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                a ⨾ r
                  ∎

              pr₂proofEq : pr₂ ⨾ (λ* prover ⨾ r) ≡ b ⨾ r
              pr₂proofEq =
                pr₂ ⨾ (λ* prover ⨾ r)
                  ≡⟨ cong (λ x → pr₂ ⨾ x) proofEq ⟩
                pr₂ ⨾ (pair ⨾ (a ⨾ r) ⨾ (b ⨾ r))
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                b ⨾ r
                  ∎
            in
            subst (λ r → r ⊩ ∣ ⟦ ψ ⟧ᶠ ∣ γ) (sym pr₁proofEq) (a⊩ϕ⊨ψ γ r r⊩ϕγ) ,
            subst (λ r → r ⊩ ∣ ⟦ θ ⟧ᶠ ∣ γ) (sym pr₂proofEq) (b⊩ϕ⊨θ γ r r⊩ϕγ))


    
