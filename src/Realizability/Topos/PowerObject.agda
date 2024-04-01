open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*; λ* to `λ*abst)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Category
open import Realizability.PropResizing
open import Realizability.CombinatoryAlgebra

module Realizability.Topos.PowerObject
  {ℓ}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  (resizing : hPropResizing ℓ)
  where
  
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Topos.Object {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.Equalizer {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.BinProducts {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.MonicReprFuncRel {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.ResizedPredicate ca isNonTrivial resizing

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open Morphism
open PartialEquivalenceRelation
open FunctionalRelation
open Category RT


private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure
  λ*abst = `λ*abst as fefermanStructure

-- Power object of X

module _ (X : Type ℓ) (perX : PartialEquivalenceRelation X) where
  𝓟 : PartialEquivalenceRelation (ResizedPredicate X)
  Predicate.isSetX (equality 𝓟) = isSet× isSetResizedPredicate isSetResizedPredicate
  Predicate.∣ equality 𝓟 ∣ (ϕ , ψ) r =
    (pr₁ ⨾ (pr₁ ⨾ r)) ⊩ isStrictResizedPredicate ϕ ×
    (pr₂ ⨾ (pr₁ ⨾ r)) ⊩ isRelationalResizedPredicate ϕ ×
    (pr₁ ⨾ (pr₂ ⨾ r)) ⊩ entailmentResizedPredicate ϕ ψ ×
    (pr₂ ⨾ (pr₂ ⨾ r)) ⊩ entailmentResizedPredicate ψ ϕ
  Predicate.isPropValued (equality 𝓟) (ϕ , ψ) r =
    isProp× (isPropIsStrictResizedPredicate ϕ (pr₁ ⨾ (pr₁ ⨾ r)))
      (isProp× (isPropIsRelationalResizedPredicate ϕ (pr₂ ⨾ (pr₁ ⨾ r)))
        (isProp×
          (isPropEntailmentResizedPredicate ϕ ψ (pr₁ ⨾ (pr₂ ⨾ r)))
          (isPropEntailmentResizedPredicate ψ ϕ (pr₂ ⨾ (pr₂ ⨾ r)))))
  isPartialEquivalenceRelation.isSetX (isPerEquality 𝓟) = isSetResizedPredicate
  isPartialEquivalenceRelation.isSymmetric (isPerEquality 𝓟) =
    do
      let
        strictness : ApplStrTerm as 2
        strictness = ` pr₁ ̇ (` pr₁ ̇ # fone) ̇ (` pr₂ ̇ (` pr₂ ̇ # fone) ̇ # fzero)

        proj : ApplStrTerm as 3
        proj = # (fsuc fone)

        proj' : ApplStrTerm as 2
        proj' = ` pr₂ ̇ (` pr₂ ̇ # fzero) ̇ # fone

        proj'' : ApplStrTerm as 2
        proj'' = ` pr₁ ̇ (` pr₂ ̇ # fzero) ̇ # fone

        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (` pair ̇ λ*abst strictness ̇ λ*abst (λ*abst proj)) ̇ (` pair ̇ λ*abst proj' ̇ λ*abst proj'')
      return
        (λ* realizer ,
        (λ { ϕ ψ r (⊩isStrictϕ , ⊩isRelationalϕ , ⊩ϕ≤ψ , ⊩ψ≤ϕ) →
          (λ x b ⊩ψx →
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym {!!}) (⊩isStrictϕ x _ (⊩ψ≤ϕ x b ⊩ψx))) ,
          (λ x x' b c ⊩x~x' ⊩ψx →
            subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x) (sym {!!}) ⊩ψx) ,
          (λ x a ⊩ψx →
            subst (λ r' → r' ⊩ ∣ toPredicate ϕ ∣ x) (sym {!!}) (⊩ψ≤ϕ x _ ⊩ψx)) ,
          λ x a ⊩ϕx →
            subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x) (sym {!!}) (⊩ϕ≤ψ x _ ⊩ϕx) }))
  isPartialEquivalenceRelation.isTransitive (isPerEquality 𝓟) = {!!}
