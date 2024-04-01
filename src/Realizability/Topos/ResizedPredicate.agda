-- Before we can talk about power objects in RT
-- we need to use propositional resizing to get
-- a copy of A-valued predicates in Type ℓ'

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Realizability.PropResizing
open import Realizability.CombinatoryAlgebra

module Realizability.Topos.ResizedPredicate
  {ℓ}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  (resizing : hPropResizing ℓ)
  where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ} {ℓ'' = ℓ} ca

open CombinatoryAlgebra ca
open Predicate renaming (isSetX to isSetPredicateBase)

smallHProp = resizing .fst
smallHProp≃hProp = resizing .snd

ResizedPredicate : Type ℓ → Type ℓ
ResizedPredicate X = Σ[ rel ∈ (X → A → smallHProp) ] isSet X

PredicateΣ≃ResizedPredicate : ∀ X → PredicateΣ X ≃ ResizedPredicate X
PredicateΣ≃ResizedPredicate X =
  Σ-cong-equiv-prop
    (equivΠ
      (idEquiv X)
      (λ x →
        equivΠ
          (idEquiv A)
          λ a →
            smallHProp≃hProp))
    (λ _ → isPropIsSet)
    (λ _ → isPropIsSet)
    (λ _ answer → answer)
    (λ _ answer → answer)

Predicate≃ResizedPredicate : ∀ X → Predicate X ≃ ResizedPredicate X
Predicate≃ResizedPredicate X = compEquiv (Predicate≃PredicateΣ X) (PredicateΣ≃ResizedPredicate X)

isSetResizedPredicate : ∀ {X} → isSet (ResizedPredicate X)
isSetResizedPredicate {X} = isOfHLevelRespectEquiv 2 (Predicate≃ResizedPredicate X) (isSetPredicate X)

ResizedPredicate≃Predicate : ∀ X → ResizedPredicate X ≃ Predicate X
ResizedPredicate≃Predicate X = invEquiv (Predicate≃ResizedPredicate X)

toPredicate : ∀ {X} → ResizedPredicate X → Predicate X
toPredicate {X} ϕ = equivFun (ResizedPredicate≃Predicate X) ϕ

fromPredicate : ∀ {X} → Predicate X → ResizedPredicate X
fromPredicate {X} ϕ = equivFun (Predicate≃ResizedPredicate X) ϕ

compIsIdEquiv : ∀ X → compEquiv (Predicate≃ResizedPredicate X) (ResizedPredicate≃Predicate X) ≡ idEquiv (Predicate X)
compIsIdEquiv X = invEquiv-is-rinv (Predicate≃ResizedPredicate X)

compIsIdFunc : ∀ {X} → (p : Predicate X) → toPredicate (fromPredicate p) ≡ p
compIsIdFunc {X} p i = equivFun (compIsIdEquiv X i) p

module _ {X} where
  entailmentResizedPredicate : ∀ (ϕ ψ : ResizedPredicate X) → A → Type ℓ
  entailmentResizedPredicate ϕ ψ r = ∀ (x : X) (a : A) (⊩ϕx : a ⊩ ∣ toPredicate ϕ ∣ x) → (r ⨾ a) ⊩ ∣ toPredicate ψ ∣ x

  isPropEntailmentResizedPredicate : ∀ ϕ ψ a → isProp (entailmentResizedPredicate ϕ ψ a)
  isPropEntailmentResizedPredicate ϕ ψ a =
    isPropΠ λ x → isPropΠ λ b → isPropΠ λ _ → (toPredicate ψ) .isPropValued _ _
