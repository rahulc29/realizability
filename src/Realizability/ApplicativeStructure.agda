open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Tactics.NatSolver

module Realizability.ApplicativeStructure where

private module _ {ℓ} {A : Type ℓ} where
  -- Taken from Data.Vec.Base from agda-stdlib
  foldlOp : ∀ {ℓ'} (B : ℕ → Type ℓ') → Type _
  foldlOp B = ∀ {n} → B n → A → B (suc n)

  opaque
    foldl : ∀ {ℓ'} {n : ℕ} (B : ℕ → Type ℓ') → foldlOp B → B zero → Vec A n → B n
    foldl {ℓ'} {.zero} B op acc emptyVec = acc
    foldl {ℓ'} {.(suc _)} B op acc (x ∷vec vec) = foldl (λ n → B (suc n)) op (op acc x) vec

  opaque
    reverse : ∀ {n} → Vec A n → Vec A n
    reverse vec = foldl (λ n → Vec A n) (λ acc curr → curr ∷ acc) [] vec

  opaque
    chain : ∀ {n} → Vec A (suc n) → (A → A → A) → A
    chain {n} (x ∷vec vec) op = foldl (λ _ → A) (λ acc curr → op acc curr) x vec

record ApplicativeStructure {ℓ} (A : Type ℓ) : Type ℓ where
  infixl 20 _⨾_
  field
    isSetA : isSet A
    _⨾_ : A → A → A

module _ {ℓ} {A : Type ℓ} (as : ApplicativeStructure A) where
  open ApplicativeStructure as
  infix 23 `_
  infixl 22 _̇_
  data Term (n : ℕ) : Type ℓ where
    # : Fin n → Term n
    `_ : A → Term n
    _̇_ : Term n → Term n → Term n

  ⟦_⟧ : ∀ {n} → Term n → Vec A n → A
  ⟦_⟧ (` a) _ = a
  ⟦_⟧ {n} (# k) subs = lookup k subs
  ⟦_⟧ (a ̇ b) subs = (⟦ a ⟧ subs) ⨾ (⟦ b ⟧ subs)

  applicationChain : ∀ {n m} → Vec (Term m) (suc n) → Term m
  applicationChain {n} {m} vec = chain vec (λ x y → x ̇ y)

  apply : ∀ {n} → A → Vec A n → A
  apply {n} a vec = chain (a ∷ vec) (λ x y → x ⨾ y)
  
  private
    opaque
      unfolding reverse
      unfolding foldl
      unfolding chain
      applyWorks : ∀ K a b → apply K (a ∷ b ∷ []) ≡ K ⨾ a ⨾ b
      applyWorks K a b = refl

  record Feferman : Type ℓ where
    field
      s : A
      k : A
      kab≡a : ∀ a b → k ⨾ a ⨾ b ≡ a
      sabc≡ac_bc : ∀ a b c → s ⨾ a ⨾ b ⨾ c ≡ (a ⨾ c) ⨾ (b ⨾ c)
      
  module ComputationRules (feferman : Feferman) where
    open Feferman feferman

    opaque
      λ*abst : ∀ {n} → (e : Term (suc n)) → Term n
      λ*abst {n} (# zero) = ` s ̇ ` k ̇ ` k
      λ*abst {n} (# (suc x)) = ` k ̇ # x
      λ*abst {n} (` x) = ` k ̇ ` x
      λ*abst {n} (e ̇ e₁) = ` s ̇ λ*abst e ̇ λ*abst e₁

    -- Some shortcuts

    λ* : Term one → A
    λ* t = ⟦ λ*abst t ⟧ []

    λ*2 : Term two → A
    λ*2 t = ⟦ λ*abst (λ*abst t) ⟧ []

    λ*3 : Term three → A
    λ*3 t = ⟦ λ*abst (λ*abst (λ*abst t)) ⟧ []

    λ*4 : Term four → A
    λ*4 t = ⟦ λ*abst (λ*abst (λ*abst (λ*abst t))) ⟧ []

    opaque
      unfolding λ*abst
      βreduction : ∀ {n} → (body : Term (suc n)) → (prim : A) → (subs : Vec A n) → ⟦ λ*abst body ̇ ` prim ⟧ subs ≡ ⟦ body ⟧ (prim ∷ subs)
      βreduction {n} (# zero) prim subs =
        s ⨾ k ⨾ k ⨾ prim
          ≡⟨ sabc≡ac_bc _ _ _ ⟩
        k ⨾ prim ⨾ (k ⨾ prim)
          ≡⟨ kab≡a _ _ ⟩
        prim
          ∎
      βreduction {n} (# (suc x)) prim subs = kab≡a _ _
      βreduction {n} (` x) prim subs = kab≡a _ _
      βreduction {n} (rator ̇ rand) prim subs =
        s ⨾ ⟦ λ*abst rator ⟧ subs ⨾ ⟦ λ*abst rand ⟧ subs ⨾ prim
          ≡⟨ sabc≡ac_bc _ _ _ ⟩
        ⟦ λ*abst rator ⟧ subs ⨾ prim ⨾ (⟦ λ*abst rand ⟧ subs ⨾ prim)
          ≡⟨ cong₂ (λ x y → x ⨾ y) (βreduction rator prim subs) (βreduction rand prim subs) ⟩
        ⟦ rator ⟧ (prim ∷ subs) ⨾ ⟦ rand ⟧ (prim ∷ subs)
          ∎

    λ*chainTerm : ∀ n → Term n → Term zero
    λ*chainTerm zero t = t
    λ*chainTerm (suc n) t = λ*chainTerm n (λ*abst t)

    λ*chain : ∀ {n} → Term n → A
    λ*chain {n} t = ⟦ λ*chainTerm n t ⟧ []

    opaque
      unfolding reverse
      unfolding foldl
      unfolding chain

      λ*ComputationRule : ∀ (t : Term 1) (a : A) → λ* t ⨾ a ≡ ⟦ t ⟧ (a ∷ [])
      λ*ComputationRule t a =
        ⟦ λ*abst t ⟧ [] ⨾ a
          ≡⟨ βreduction t a [] ⟩
        ⟦ t ⟧ (a ∷ [])
          ∎

      λ*2ComputationRule : ∀ (t : Term 2) (a b : A) → λ*2 t ⨾ a ⨾ b ≡ ⟦ t ⟧ (b ∷ a ∷ [])
      λ*2ComputationRule t a b =
        ⟦ λ*abst (λ*abst t) ⟧ [] ⨾ a ⨾ b
          ≡⟨ refl ⟩
        ⟦ λ*abst (λ*abst t) ⟧ [] ⨾ ⟦ ` a ⟧ [] ⨾ ⟦ ` b ⟧ []
          ≡⟨ refl ⟩
        ⟦ λ*abst (λ*abst t) ̇ ` a ⟧ [] ⨾ ⟦ ` b ⟧ []
          ≡⟨ cong (λ x → x ⨾ b) (βreduction (λ*abst t) a []) ⟩
        ⟦ λ*abst t ⟧ (a ∷ []) ⨾ b
          ≡⟨ βreduction t b (a ∷ []) ⟩
        ⟦ t ⟧ (b ∷ a ∷ [])
          ∎
          
      λ*3ComputationRule : ∀ (t : Term 3) (a b c : A) → λ*3 t ⨾ a ⨾ b ⨾ c ≡ ⟦ t ⟧ (c ∷ b ∷ a ∷ [])
      λ*3ComputationRule t a b c =
        ⟦ λ*abst (λ*abst (λ*abst t)) ⟧ [] ⨾ ⟦ ` a ⟧ [] ⨾ ⟦ ` b ⟧ [] ⨾ ⟦ ` c ⟧ []
          ≡⟨ cong (λ x → x ⨾ b ⨾ c) (βreduction (λ*abst (λ*abst t)) a []) ⟩
        ⟦ λ*abst (λ*abst t) ⟧ (a ∷ []) ⨾ ⟦ ` b ⟧ (a ∷ []) ⨾ ⟦ ` c ⟧ (a ∷ [])
          ≡⟨ cong (λ x → x ⨾ c) (βreduction (λ*abst t) b (a ∷ [])) ⟩
        ⟦ λ*abst t ⟧ (b ∷ a ∷ []) ⨾ ⟦ ` c ⟧ (b ∷ a ∷ [])
          ≡⟨ βreduction t c (b ∷ a ∷ []) ⟩
        ⟦ t ⟧ (c ∷ b ∷ a ∷ [])
          ∎

      λ*4ComputationRule : ∀ (t : Term 4) (a b c d : A) → λ*4 t ⨾ a ⨾ b ⨾ c ⨾ d ≡ ⟦ t ⟧ (d ∷ c ∷ b ∷ a ∷ [])
      λ*4ComputationRule t a b c d =
        ⟦ λ*abst (λ*abst (λ*abst (λ*abst t))) ⟧ [] ⨾ ⟦ ` a ⟧ [] ⨾ ⟦ ` b ⟧ [] ⨾ ⟦ ` c ⟧ [] ⨾ ⟦ ` d ⟧ []
          ≡⟨ cong (λ x → x ⨾ b ⨾ c ⨾ d) (βreduction (λ*abst (λ*abst (λ*abst t))) a []) ⟩
        ⟦ λ*abst (λ*abst (λ*abst t)) ⟧ (a ∷ []) ⨾ ⟦ ` b ⟧ (a ∷ []) ⨾ ⟦ ` c ⟧ (a ∷ []) ⨾ ⟦ ` d ⟧ (a ∷ [])
          ≡⟨ cong (λ x → x ⨾ c ⨾ d) (βreduction (λ*abst (λ*abst t)) b (a ∷ [])) ⟩
        ⟦ λ*abst (λ*abst t) ⟧ (b ∷ a ∷ []) ⨾ ⟦ ` c ⟧ (b ∷ a ∷ []) ⨾ ⟦ ` d ⟧ (b ∷ a ∷ [])
          ≡⟨ cong (λ x → x ⨾ d) (βreduction (λ*abst t) c (b ∷ a ∷ [])) ⟩
        ⟦ λ*abst t ⟧ (c ∷ b ∷ a ∷ []) ⨾ ⟦ ` d ⟧ (c ∷ b ∷ a ∷ [])
          ≡⟨ βreduction t d (c ∷ b ∷ a ∷ []) ⟩
        ⟦ t ⟧ (d ∷ c ∷ b ∷ a ∷ [])
          ∎
