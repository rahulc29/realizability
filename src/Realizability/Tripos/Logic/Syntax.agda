module Realizability.Tripos.Logic.Syntax {ℓ} where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

-- Inspired by the 1lab definitions
data Sort : Type (ℓ-suc ℓ) where
  ↑ : hSet ℓ → Sort
  _`×_ : Sort → Sort → Sort


⟦_⟧ˢ : Sort → hSet ℓ
⟦ ↑ a ⟧ˢ = a
⟦ a `× b ⟧ˢ = ⟦ a ⟧ˢ .fst × ⟦ b ⟧ˢ .fst , isSet× (⟦ a ⟧ˢ .snd) (⟦ b ⟧ˢ .snd)

data Context : Type (ℓ-suc ℓ) where
  [] : Context
  _′_ : Context → Sort → Context

data _∈_ : Sort → Context → Type (ℓ-suc ℓ) where
  here : ∀ {Γ A} → A ∈ (Γ ′ A)
  there : ∀ {Γ A B} → A ∈ Γ → A ∈ (Γ ′ B)

data Term : Context → Sort → Type (ℓ-suc ℓ) where
  var : ∀ {Γ A} → A ∈ Γ → Term Γ A
  _`,_ : ∀ {Γ A B} → Term Γ A → Term Γ B → Term Γ (A `× B)
  π₁ : ∀ {Γ A B} → Term Γ (A `× B) → Term Γ A
  π₂ : ∀ {Γ A B} → Term Γ (A `× B) → Term Γ B
  fun : ∀ {Γ A B} → (⟦ A ⟧ˢ .fst → ⟦ B ⟧ˢ .fst) → Term Γ A → Term Γ B

data Renaming : Context → Context → Type (ℓ-suc ℓ) where
  id : ∀ {Γ} → Renaming Γ Γ
  drop : ∀ {Γ Δ s} → Renaming Γ Δ → Renaming (Γ ′ s) Δ
  keep : ∀ {Γ Δ s} → Renaming Γ Δ → Renaming (Γ ′ s) (Δ ′ s)

data Substitution : Context → Context → Type (ℓ-suc ℓ) where
  id : ∀ {Γ} → Substitution Γ Γ
  _,_ : ∀ {Γ Δ s} → (t : Term Γ s) → Substitution Γ Δ → Substitution Γ (Δ ′ s)
  drop : ∀ {Γ Δ s} → Substitution Γ Δ → Substitution (Γ ′ s) Δ

terminatingSubstitution : ∀ {Γ} → Substitution Γ []
terminatingSubstitution {[]} = id
terminatingSubstitution {Γ ′ x} = drop terminatingSubstitution

renamingCompose : ∀ {Γ Δ Θ} → Renaming Γ Δ → Renaming Δ Θ → Renaming Γ Θ
renamingCompose {Γ} {.Γ} {Θ} id Δ→Θ = Δ→Θ
renamingCompose {.(_ ′ _)} {Δ} {Θ} (drop Γ→Δ) Δ→Θ = drop (renamingCompose Γ→Δ Δ→Θ)
renamingCompose {.(_ ′ _)} {.(_ ′ _)} {.(_ ′ _)} (keep Γ→Δ) id = keep Γ→Δ
renamingCompose {.(_ ′ _)} {.(_ ′ _)} {Θ} (keep Γ→Δ) (drop Δ→Θ) = drop (renamingCompose Γ→Δ Δ→Θ)
renamingCompose {.(_ ′ _)} {.(_ ′ _)} {.(_ ′ _)} (keep Γ→Δ) (keep Δ→Θ) = keep (renamingCompose Γ→Δ Δ→Θ)

renamingVar : ∀ {Γ Δ s} → Renaming Γ Δ → s ∈ Δ → s ∈ Γ
renamingVar {Γ} {.Γ} {s} id s∈Δ = s∈Δ
renamingVar {.(_ ′ _)} {Δ} {s} (drop ren) s∈Δ = there (renamingVar ren s∈Δ)
renamingVar {.(_ ′ s)} {.(_ ′ s)} {s} (keep ren) here = here
renamingVar {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (there s∈Δ) = there (renamingVar ren s∈Δ)

renamingTerm : ∀ {Γ Δ s} → Renaming Γ Δ → Term Δ s → Term Γ s
renamingTerm {Γ} {.Γ} {s} id term = term
renamingTerm {.(_ ′ _)} {Δ} {s} (drop ren) (var x) = var (renamingVar (drop ren) x)
renamingTerm {.(_ ′ _)} {Δ} {.(_ `× _)} (drop ren) (term `, term₁) = renamingTerm (drop ren) term `, renamingTerm (drop ren) term₁
renamingTerm {.(_ ′ _)} {Δ} {s} (drop ren) (π₁ term) = π₁ (renamingTerm (drop ren) term)
renamingTerm {.(_ ′ _)} {Δ} {s} (drop ren) (π₂ term) = π₂ (renamingTerm (drop ren) term)
renamingTerm {.(_ ′ _)} {Δ} {s} (drop ren) (fun f term) = fun f (renamingTerm (drop ren) term)
renamingTerm {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (var x) = var (renamingVar (keep ren) x)
renamingTerm {.(_ ′ _)} {.(_ ′ _)} {.(_ `× _)} (keep ren) (term `, term₁) = renamingTerm (keep ren) term `, renamingTerm (keep ren) term₁
renamingTerm {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (π₁ term) = π₁ (renamingTerm (keep ren) term)
renamingTerm {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (π₂ term) = π₂ (renamingTerm (keep ren) term)
renamingTerm {.(_ ′ _)} {.(_ ′ _)} {s} (keep ren) (fun f term) = fun f (renamingTerm (keep ren) term)

substitutionVar : ∀ {Γ Δ s} → Substitution Γ Δ → s ∈ Δ → Term Γ s
substitutionVar {Γ} {.Γ} {s} id s∈Δ = var s∈Δ
substitutionVar {Γ} {.(_ ′ s)} {s} (t , subs) here = t
substitutionVar {Γ} {.(_ ′ _)} {s} (t , subs) (there s∈Δ) = substitutionVar subs s∈Δ
substitutionVar {.(_ ′ _)} {Δ} {s} (drop subs) s∈Δ = renamingTerm (drop id) (substitutionVar subs s∈Δ)

substitutionTerm : ∀ {Γ Δ s} → Substitution Γ Δ → Term Δ s → Term Γ s
substitutionTerm {Γ} {Δ} {s} subs (var x) = substitutionVar subs x
substitutionTerm {Γ} {Δ} {.(_ `× _)} subs (t `, t₁) = substitutionTerm subs t `, substitutionTerm subs t₁
substitutionTerm {Γ} {Δ} {s} subs (π₁ t) = π₁ (substitutionTerm subs t)
substitutionTerm {Γ} {Δ} {s} subs (π₂ t) = π₂ (substitutionTerm subs t)
substitutionTerm {Γ} {Δ} {s} subs (fun x t) = fun x (substitutionTerm subs t)

module Relational {n} (relSym : Vec Sort n) where

 data Formula : Context → Type (ℓ-suc ℓ) where
   ⊤ᵗ : ∀ {Γ} → Formula Γ
   ⊥ᵗ : ∀ {Γ} → Formula Γ
   _`∨_ : ∀ {Γ} → Formula Γ → Formula Γ → Formula Γ 
   _`∧_ : ∀ {Γ} → Formula Γ → Formula Γ → Formula Γ 
   _`→_ : ∀ {Γ} → Formula Γ → Formula Γ → Formula Γ 
   `¬_ : ∀ {Γ} → Formula Γ → Formula Γ
   `∃ : ∀ {Γ B} → Formula (Γ ′ B) → Formula Γ
   `∀ : ∀ {Γ B} → Formula (Γ ′ B) → Formula Γ
   rel : ∀ {Γ} (k : Fin n) → Term Γ (lookup k relSym) → Formula Γ
   
