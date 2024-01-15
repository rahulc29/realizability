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
