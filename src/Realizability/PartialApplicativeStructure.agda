{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin

module Realizability.PartialApplicativeStructure {𝓢} where

open import Realizability.Partiality {𝓢}
open ♯_

record PartialApplicativeStructure {ℓ} (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
  infixl 20 _⨾_
  field
    isSetA : isSet A
    _⨾_ : A → A → ♯ A

module _ {ℓ} {A : Type ℓ} (pas : PartialApplicativeStructure A) where
  open PartialApplicativeStructure pas
  infix 22 `_
  infixl 23 _̇_
  data Term (n : ℕ) : Type ℓ where
    # : Fin n → Term n
    `_ : A → Term n
    _̇_ : Term n → Term n → Term n

  upgrade : ∀ {n m} → n < m → Term n → Term m
  upgrade _ (` a) = ` a
  upgrade {n} {m} n<m (# k) = # (k .fst , <-trans (k .snd) n<m)
  upgrade {n} {m} n<m (a ̇ b) = upgrade n<m a ̇ upgrade n<m b

  foo : ∀ a → Term 0
  foo a = ` a

  bar : Term 1
  bar = # fzero

  baz : Term 2
  baz = (# fzero) ̇ (# fone)

  baz' : Term 1
  baz' = (# fzero) ̇ (# fzero)

  isClosed : ∀ {n} → Term n → Type
  isClosed {n} _ = n ≡ zero

  isClosed-foo : ∀ a → isClosed (foo a)
  isClosed-foo a = refl

  ClosedTerm : Type ℓ
  ClosedTerm = Term zero

  infix 23 _↓_
  data _↓_ : ClosedTerm → ClosedTerm → Type ℓ where
    ↓-refl : ∀ a → (` a) ↓ (` a)
    ↓-appl : ∀ {a b c s t} → s ↓ (` b) → t ↓ (` c) → (s ̇ t) ↓ a
             
  infix 23 _denotes
  _denotes : ClosedTerm → Type ℓ
  t denotes = Σ[ a ∈ _ ] t ↓ a

  denotationOf : ∀ {t} → t denotes → ClosedTerm
  denotationOf {t} (a , _) = a

  record _＝_ (a b : ClosedTerm) : Type ℓ where
    field
      a-denotes : a denotes
      b-denotes : b denotes
      denote-≡ : denotationOf a-denotes ≡ denotationOf b-denotes

  substitute : ∀ {n} → Term n → Vec (♯ A) n → ♯ A
  substitute (` a) _ = return a
  substitute {n} (# k) subs = lookup (Fin→FinData n k) subs
  substitute (a ̇ b) subs = do
                            a ← substitute a subs
                            b ← substitute b subs
                            a ⨾ b

  -- Given an element a and a vector of elements (a₁ .. aₙ)
  -- produces the application (a a₁ .. aₙ)
  -- Note that application associates to the left
  applicationChain : ∀ {n} → A → Vec A n → ♯ A
  applicationChain a [] = return a
  applicationChain a (x ∷ xs) = applicationChain' a (x ∷ xs) (return a) where
                                 applicationChain' : ∀ {n} → A → Vec A n → ♯ A → ♯ A
                                 applicationChain' _ [] acc = acc
                                 applicationChain' a (x ∷ xs) acc = applicationChain' x xs (acc >>= λ x → x ⨾ a)
  
  record isInterpreted {n} (t : Term n) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
    field
      interpretation : A
      applicationChainSupported : ∀ {m} (subs : Vec A m) → applicationChain interpretation subs .support
      naturality : ∀ (subs : Vec A n) → applicationChain interpretation subs ≈ substitute t (map return subs)

  isCombinatoriallyComplete : Type (ℓ-max ℓ (ℓ-suc 𝓢))
  isCombinatoriallyComplete = ∀ {n} (t : Term n) → isInterpreted t

  -- Applying combinatorial completeness on this term will create the K combinator
  -- Essentially this is
  -- t(x₁ , x₂) = x₁ 
  preK : Term 2
  preK = # 0

  -- As always, Agda is unable to solve constraints
  -- So we must put {3} to tell Agda we are constructing
  -- terms of order 3
  -- Essentially this is
  -- t(x₁ , x₂ , x₃) = (x₁ x₃) (x₂ x₃)
  preS : Term 3
  preS = ((# {3} 0) ̇ (# {3} 2)) ̇ ((# {3} 1) ̇ (# {3} 2))

  record Feferman : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
   field
      s : A
      k : A
      sab-supported : ∀ a b → applicationChain s (a ∷ b ∷ []) .support
      kab≈a : ∀ a b → applicationChain k (a ∷ b ∷ []) ≈ return a
      sabc≈ac_bc : ∀ a b c → applicationChain s (a ∷ b ∷ c ∷ []) ≈ (substitute preS (map return (a ∷ b ∷ c ∷ [])))
  -- A few elementary developments assuming combinatorial completeness
  -- In particular, we can finally prove one side of Feferman's theorem
  module _ (completeness : isCombinatoriallyComplete) where
    open isInterpreted
    K : A
    K = completeness preK .interpretation

    S : A
    S = completeness preS .interpretation

    Sab-supported : ∀ a b → applicationChain S (a ∷ b ∷ []) .support
    Sab-supported a b = completeness preS .applicationChainSupported (a ∷ b ∷ [])

    Kab≈a : ∀ a b → applicationChain K (a ∷ b ∷ []) ≈ return a
    Kab≈a a b = completeness preK .naturality (a ∷ b ∷ [])

    Sabc≈ac_bc : ∀ a b c → applicationChain S (a ∷ b ∷ c ∷ []) ≈ (substitute preS (map return (a ∷ b ∷ c ∷ [])))
    Sabc≈ac_bc a b c = completeness preS .naturality (a ∷ b ∷ c ∷ [])

    open Feferman
    
    feferman : Feferman
    feferman .s = S
    feferman .k = K
    feferman .sab-supported = Sab-supported
    feferman .kab≈a = Kab≈a
    feferman .sabc≈ac_bc = Sabc≈ac_bc

  module _ (feferman : Feferman) where
    open Feferman feferman
    ƛ : ∀ {n} (e : Term (suc n)) → Term n
    ƛ (` a) = (` k) ̇ (` a)
    ƛ {n} (# y) with (discreteℕ n (y .fst))
    ... | yes _ = (` s) ̇ (` k) ̇ (` k)
    ... | no ¬y≡n with (y .fst)
    ...   | zero = (` k) ̇ (# (zero , {!!}))
    ...   | (suc m) = (` k) ̇ # (m , {!!})
    ƛ (a ̇ b) = (` s) ̇ (ƛ a) ̇ (ƛ b)

    ƛ-chainSyntax : ∀ n → Term n → Term zero
    ƛ-chainSyntax zero t = t
    ƛ-chainSyntax (suc n) t = ƛ-chainSyntax n (ƛ t)

    ƛ-chain : ∀ n → Term n → ♯ A
    ƛ-chain n t = substitute (ƛ-chainSyntax n t) []

    ƛ-chainSupport : ∀ n → (t : Term n) → ƛ-chain n t .support
    ƛ-chainSupport n (` a) = {!!}
    ƛ-chainSupport n (# y) = {!!}
    ƛ-chainSupport n (a ̇ b) = {!!}

    freeVariables : ∀ {n} → Term n → ℕ
    freeVariables {n} _ = n
    
    open isInterpreted
    feferman→isCombinatoriallyComplete : isCombinatoriallyComplete
    feferman→isCombinatoriallyComplete t .interpretation = (ƛ-chain (freeVariables t) t) .force (ƛ-chainSupport (freeVariables t) t)
    feferman→isCombinatoriallyComplete t .applicationChainSupported subs = {!!}
    feferman→isCombinatoriallyComplete t .naturality subs = {!!}

    

    

  
    
  
