open import Cubical.Foundations.Prelude

module Realizability.PERs.SystemF where

module Syntax where
  -- Only one kind for now
  -- System Fω has a simply typed lambda calculus at the type level
  -- Inspired heavily by
  -- "System F in Agda for Fun and Profit"
  data Kind : Type where
    tp : Kind

  data TypeCtxt : Type where
    [] : TypeCtxt
    _,_ : TypeCtxt → Kind → TypeCtxt

  data _∈*_ : Kind → TypeCtxt → Type where
    here : ∀ {k Γ} → k ∈* (Γ , k)
    there : ∀ {k Γ k'} → k ∈* Γ → k ∈* (Γ , k')

  data Tp : TypeCtxt → Kind → Type where
    var : ∀ {Γ k} → k ∈* Γ → Tp Γ k
    funcTp : ∀ {Γ k} → Tp Γ k → Tp Γ k → Tp Γ k
    prodTp : ∀ {Γ k} → Tp Γ k → Tp Γ k → Tp Γ k
    forallTp : ∀ {Γ k} → Tp (Γ , k) tp → Tp Γ tp

  data TermCtxt : TypeCtxt → Type where
    [] : TermCtxt []
    _,*_ : ∀ {Γ k} → TermCtxt Γ → k ∈* Γ → TermCtxt (Γ , k)
    _,_ : ∀ {Γ} → TermCtxt Γ → Tp Γ tp → TermCtxt Γ

  -- This is a better notion of renaming than as an inductive type?
  Ren* : TypeCtxt → TypeCtxt → Type
  Ren* Γ Δ = ∀ {K} → K ∈* Γ → K ∈* Δ

  lift* : ∀ {Γ Δ k} → Ren* Γ Δ → Ren* (Γ , k) (Δ , k)
  lift* {Γ} {Δ} {k} ρ {.k} here = here
  lift* {Γ} {Δ} {k} ρ {K} (there inm) = there (ρ inm)

  ren* : ∀ {Γ Δ} → 

  data _∈_ : ∀ {Γ} → Tp Γ tp → TermCtxt Γ → Type where
    here : ∀ {Γ} {A : Tp Γ tp} {Θ : TermCtxt Γ} → A ∈ (Θ , A)
    thereType : ∀ {Γ} {A B : Tp Γ tp} {Θ : TermCtxt Γ} → A ∈ Θ → A ∈ (Θ , B)
    
    
