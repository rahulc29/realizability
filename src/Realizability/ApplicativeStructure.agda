{-# OPTIONS --cubical --without-K --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Empty renaming (elim to ⊥elim)

module Realizability.ApplicativeStructure where

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

  upgrade : ∀ {n m} → n < m → Term n → Term m
  upgrade _ (` a) = ` a
  upgrade {n} {m} n<m (# k) = # (k .fst , <-trans (k .snd) n<m)
  upgrade {n} {m} n<m (a ̇ b) = upgrade n<m a ̇ upgrade n<m b

  substitute : ∀ {n} → Term n → Vec A n → A
  substitute (` a) _ = a
  substitute {n} (# k) subs = lookup (Fin→FinData n k) subs
  substitute (a ̇ b) subs = (substitute a subs) ⨾ (substitute b subs)

  apply : ∀ {n} → A → Vec A n → A
  apply a [] = a
  apply a (x ∷ xs) = apply' (x ∷ xs) a where
                            apply' : ∀ {n} → Vec A n → A → A
                            apply' [] acc = acc
                            apply' (x ∷ xs) acc = apply' xs (acc ⨾ x)

  applyWorks : ∀ K a b → apply K (a ∷ b ∷ []) ≡ K ⨾ a ⨾ b
  applyWorks K a b = refl

  record isInterpreted {n} (t : Term n) : Type ℓ where
    field
      interpretation : A
      naturality : ∀ (subs : Vec A n) → apply interpretation subs ≡ substitute t subs

  isCombinatoriallyComplete : Type ℓ
  isCombinatoriallyComplete = ∀ {n} (t : Term n) → isInterpreted t

  record Feferman : Type ℓ where
    field
      s : A
      k : A
      kab≡a : ∀ a b → k ⨾ a ⨾ b ≡ a
      sabc≡ac_bc : ∀ a b c → s ⨾ a ⨾ b ⨾ c ≡ (a ⨾ c) ⨾ (b ⨾ c)

  module _ (completeness : isCombinatoriallyComplete) where
    open isInterpreted

    preS : Term 3
    preS = ((# 0) ̇ (# 2)) ̇ ((# 1) ̇ (# 2))

    S : A
    S = (completeness preS) .interpretation

    preK : Term 2
    preK = # 0

    K : A
    K = (completeness preK) .interpretation

    Kab≡a : ∀ a b → K ⨾ a ⨾ b ≡ a
    Kab≡a a b = (completeness preK) .naturality (a ∷ b ∷ [])

    Sabc≡ac_bc : ∀ a b c → S ⨾ a ⨾ b ⨾ c ≡ (a ⨾ c) ⨾ (b ⨾ c)
    Sabc≡ac_bc a b c = (completeness preS) .naturality (a ∷ b ∷ c ∷ [])
    open Feferman
    completeness→feferman : Feferman
    completeness→feferman .s = S
    completeness→feferman .k = K
    completeness→feferman .kab≡a = Kab≡a
    completeness→feferman .sabc≡ac_bc = Sabc≡ac_bc

  module _ (feferman : Feferman) where
    open Feferman feferman
    {-
    This goofy definition is there to ensure that λ* computes.
    For some reason the last branch of pattern-matching cannot definitionally equate y .fst and suc m
    So we must postulate it.
    But since we already know that y .fst = suc m we can use discreteℕ to get an actual proof and extract
    it using fromYes. fromYes then gets a dummy proof
    -}
    λ* : ∀ {n} (e : Term (suc n)) → Term n
    λ* (` a) = ` k ̇ ` a
    λ* (a ̇ b) = ` s ̇ (λ* a) ̇ (λ* b)
    λ* {n} (# y) with (discreteℕ (y .fst) zero)
    ... | yes _ = ` s ̇ ` k ̇ ` k
    ... | no ¬y≡zero with (y .fst)
    ...     | zero = ⊥elim (¬y≡zero refl)
    ...     | (suc m) = ` k ̇ # (m , pred-≤-pred (subst (λ y' → suc y' ≤ suc n) (fromYes fsty≡sucm (discreteℕ (y .fst) (suc m))) (y .snd))) where postulate fsty≡sucm : fst y ≡ suc m

    λ*-chainTerm : ∀ n → Term n → Term zero
    λ*-chainTerm zero t = t
    λ*-chainTerm (suc n) t = λ*-chainTerm n (λ* t)

    λ*-chain : ∀ {n} → Term n → A
    λ*-chain {n} t = substitute (λ*-chainTerm n t) []

    ⟦_⟧ : Term zero → A
    ⟦ ` a ⟧ = a
    ⟦ a ̇ b ⟧ = ⟦ a ⟧ ⨾ ⟦ b ⟧
    ⟦ # x ⟧ = ⊥elim {A = λ _ → A} (¬Fin0 x)

    λ*Computation : ∀ (T : Term 1) (e : Term zero) → ⟦ λ* T ⟧ ⨾ ⟦ e ⟧ ≡ substitute T (⟦ e ⟧ ∷ [])
    λ*Computation (# x) e = {!subst (λ x≡zero → ⟦ λ* (# x) ⟧ ⨾ ⟦ e ⟧ ≡ lookup (Fin→FinData 1 x) (⟦ e ⟧ ∷ [])) ? ?!}
    λ*Computation (` x) e = kab≡a x ⟦ e ⟧
    λ*Computation (U ̇ V) e =
      s ⨾ ⟦ λ* U ⟧ ⨾ ⟦ λ* V ⟧ ⨾ ⟦ e ⟧
        ≡⟨ sabc≡ac_bc _ _ _ ⟩
       (⟦ λ* U ⟧ ⨾ ⟦ e ⟧) ⨾ (⟦ λ* V ⟧ ⨾ ⟦ e ⟧)
        ≡⟨ cong (λ x → x ⨾ _) (λ*Computation U e) ⟩
        (substitute U (⟦ e ⟧ ∷ [])) ⨾ (⟦ λ* V ⟧ ⨾ ⟦ e ⟧)
        ≡⟨ cong (λ x → _ ⨾ x) (λ*Computation V e) ⟩
        (substitute U (⟦ e ⟧ ∷ [])) ⨾ (substitute V (⟦ e ⟧ ∷ []))
        ∎
    

    open isInterpreted

    postulate λ*-naturality : ∀ {n} (t : Term n) (subs : Vec A n) → apply (λ*-chain t) subs ≡ substitute t subs
    
    feferman→completeness : isCombinatoriallyComplete
    feferman→completeness t .interpretation = λ*-chain t
    feferman→completeness t .naturality subs = λ*-naturality t subs
    

