open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Literals
open import Cubical.Data.Vec
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

module Realizability.Topos.TerminalObject
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥) where

open CombinatoryAlgebra ca
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Topos.Object {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial

open Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open PartialEquivalenceRelation
open Predicate renaming (isSetX to isSetPredicateBase)
private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure

opaque
  terminalPer : PartialEquivalenceRelation Unit*
  isSetPredicateBase (equality terminalPer) = isSet× isSetUnit* isSetUnit*
  ∣ equality terminalPer ∣ (tt* , tt*) _ = Unit*
  isPropValued (equality terminalPer) _ _ = isPropUnit*
  isPartialEquivalenceRelation.isSetX (isPerEquality terminalPer) = isSetUnit*
  isPartialEquivalenceRelation.isSymmetric (isPerEquality terminalPer) =
    return (k , (λ { tt* tt* r tt* → tt* }))
  isPartialEquivalenceRelation.isTransitive (isPerEquality terminalPer) =
    return (k , (λ { tt* tt* tt* _ _ tt* tt* → tt* }))

open FunctionalRelation

opaque
  unfolding terminalPer
  terminalFuncRel : ∀ {Y : Type ℓ'} → (perY : PartialEquivalenceRelation Y) → FunctionalRelation perY terminalPer
  terminalFuncRel {Y} perY =
    record
      { relation =
        record
          { isSetX = isSet× (perY .isSetX) isSetUnit*
          ; ∣_∣ = λ { (y , tt*) r → r ⊩ ∣ perY .equality ∣ (y , y) }
          ; isPropValued = λ { (y , tt*) r → perY .equality .isPropValued _ _ } }
      ; isFuncRel =
        record
          { isStrictDomain = return (Id , (λ { y tt* r r⊩y~y → subst (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y)) (sym (Ida≡a _)) r⊩y~y }))
          ; isStrictCodomain = return (k , (λ { y tt* r r⊩y~y → tt* }))
          ; isRelational =
            (do
            (t , t⊩isTransitive) ← perY .isTransitive
            (s , s⊩isSymmetric) ← perY .isSymmetric
            let
              prover : ApplStrTerm as 3
              prover = ` t ̇ (` s ̇ # fzero) ̇ # fzero
            return
              (λ* prover ,
              (λ { y y' tt* tt* a b c a⊩y~y' b⊩y~y tt* →
                subst
                  (λ r' → r' ⊩ ∣ perY .equality ∣ (y' , y'))
                  (sym (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])))
                  (t⊩isTransitive y' y y' (s ⨾ a) a (s⊩isSymmetric y y' a a⊩y~y') a⊩y~y') })))
          ; isSingleValued = (return (k , (λ { y tt* tt* r₁ r₂ r₁⊩y~y r₂⊩y~y → tt* })))
          ; isTotal = return
                      (Id ,
                      (λ y r r⊩y~y →
                        return (tt* , (subst (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y)) (sym (Ida≡a _)) r⊩y~y))))
                                    } }
opaque
  unfolding terminalPer
  isTerminalTerminalPer : ∀ {Y : Type ℓ'} → (perY : PartialEquivalenceRelation Y) → isContr (RTMorphism perY terminalPer)
  isTerminalTerminalPer {Y} perY =
    inhProp→isContr
      [ terminalFuncRel perY ]
      λ f g →
        SQ.elimProp2
          (λ f g → squash/ f g)
          (λ F G →
            let
              answer : pointwiseEntailment perY terminalPer F G
              answer =
                do
                  (tlG , tlG⊩isTotalG) ← G .isTotal
                  (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
                  let
                    prover : ApplStrTerm as 1
                    prover = ` tlG ̇ (` stFD ̇ # fzero)
                  return
                    (λ* prover ,
                    (λ { y tt* r r⊩Fy →
                      transport
                        (propTruncIdempotent (G .relation .isPropValued _ _))
                        (do
                          (tt* , tlGstFD⊩Gy) ← tlG⊩isTotalG y (stFD ⨾ r) (stFD⊩isStrictDomainF y tt* r r⊩Fy)
                          return (subst (λ r' → r' ⊩ ∣ G .relation ∣ (y , tt*)) (sym (λ*ComputationRule prover (r ∷ []))) tlGstFD⊩Gy)) }))
            in
            eq/ _ _ (answer , F≤G→G≤F perY terminalPer F G answer))
          f g

TerminalRT : Terminal RT
TerminalRT =
  (Unit* , terminalPer) , (λ { (Y , perY) → isTerminalTerminalPer perY})
