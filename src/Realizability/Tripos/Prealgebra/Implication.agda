open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.Fin
open import Cubical.Data.Vec

module Realizability.Tripos.Prealgebra.Implication {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Tripos.Prealgebra.Predicate ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

λ*ComputationRule = `λ*ComputationRule as fefermanStructure
λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  -- ⇒ is Heyting implication
  a⊓b≤c→a≤b⇒c : ∀ a b c → (a ⊓ b ≤ c) → a ≤ (b ⇒ c)
  a⊓b≤c→a≤b⇒c a b c a⊓b≤c =
    do
      (a~ , a~proves) ← a⊓b≤c
      let prover = (` a~ ̇ (` pair ̇ (# fzero)  ̇ (# fone)))
      return
        (λ* prover ,
          λ x aₓ aₓ⊩ax bₓ bₓ⊩bx →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (aₓ ∷ bₓ ∷ [])))
              (a~proves
                x
                (pair ⨾ aₓ ⨾ bₓ)
                ((subst (λ r → r ⊩ ∣ a ∣ x) (sym (pr₁pxy≡x _ _)) aₓ⊩ax) ,
                 (subst (λ r → r ⊩ ∣ b ∣ x) (sym (pr₂pxy≡y _ _)) bₓ⊩bx))))

  a≤b⇒c→a⊓b≤c : ∀ a b c → a ≤ (b ⇒ c) → (a ⊓ b ≤ c)
  a≤b⇒c→a⊓b≤c a b c a≤b⇒c =
    do
      (a~ , a~proves) ← a≤b⇒c
      let prover = ` a~ ̇ (` pr₁ ̇ (# fzero)) ̇ (` pr₂ ̇ (# fzero))
      return
        (λ* prover ,
          λ { x abₓ (pr₁abₓ⊩ax , pr₂abₓ⊩bx) →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (abₓ ∷ [])))
              (a~proves x (pr₁ ⨾ abₓ) pr₁abₓ⊩ax (pr₂ ⨾ abₓ) pr₂abₓ⊩bx) })

  ⇒isRightAdjointOf⊓ : ∀ a b c → (a ⊓ b ≤ c) ≡ (a ≤ b ⇒ c)
  ⇒isRightAdjointOf⊓ a b c = hPropExt (isProp≤ (a ⊓ b) c) (isProp≤ a (b ⇒ c)) (a⊓b≤c→a≤b⇒c a b c) (a≤b⇒c→a⊓b≤c a b c)

  antiSym→a⇒c≤b⇒c : ∀ a b c → a ≤ b → b ≤ a → (a ⇒ c) ≤ (b ⇒ c)
  antiSym→a⇒c≤b⇒c a b c a≤b b≤a =
    do
      (α , αProves) ← a≤b
      (β , βProves) ← b≤a
      let
        prover : Term as 2
        prover = (# fzero) ̇ (` β ̇ # fone)
      return
        (λ* prover ,
          (λ x r r⊩a⇒c r' r'⊩b →
            subst
              (λ witness → witness ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (r ∷ r' ∷ [])))
              (r⊩a⇒c (β ⨾ r') (βProves x r' r'⊩b))))

  antiSym→a⇒b≤a⇒c : ∀ a b c → b ≤ c → c ≤ b → (a ⇒ b) ≤ (a ⇒ c)
  antiSym→a⇒b≤a⇒c a b c b≤c c≤b =
    do
      (β , βProves) ← b≤c
      (γ , γProves) ← c≤b
      let
        prover : Term as 2
        prover = ` β ̇ ((# fzero) ̇ (# fone))
      return
        (λ* prover ,
          (λ x α α⊩a⇒b a' a'⊩a →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (α ∷ a' ∷ [])))
              (βProves x (α ⨾ a') (α⊩a⇒b a' a'⊩a))))
