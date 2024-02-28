open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients renaming (elimProp to setQuotElimProp; elimProp2 to setQuotElimProp2)
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal

module Realizability.Topos.TerminalObject
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥) where

open CombinatoryAlgebra ca
open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate')
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open import Realizability.Topos.Object {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial

open Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open PartialEquivalenceRelation
open Predicate' renaming (isSetX to isSetPredicateBase)
private
  Predicate = Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''}
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure

terminalPartialEquivalenceRelation : PartialEquivalenceRelation Unit*
isSetX terminalPartialEquivalenceRelation = isSetUnit*
isSetPredicateBase (equality terminalPartialEquivalenceRelation) = isSet× isSetUnit* isSetUnit*
∣ equality terminalPartialEquivalenceRelation ∣ (tt* , tt*) r = Unit*
isPropValued (equality terminalPartialEquivalenceRelation) (tt* , tt*) r = isPropUnit*
isSymmetric terminalPartialEquivalenceRelation = return (k , (λ { tt* tt* _ tt* → tt* }))
isTransitive terminalPartialEquivalenceRelation = return (k , (λ { tt* tt* tt* _ _ tt* tt* → tt* }))

open FunctionalRelation
-- I have officially taken the inlining too far
-- TODO : Refactor
isTerminalTerminalPartialEquivalenceRelation : ∀ {Y : Type ℓ'} → (perY : PartialEquivalenceRelation Y) → isContr (RTMorphism perY terminalPartialEquivalenceRelation)
isTerminalTerminalPartialEquivalenceRelation {Y} perY =
  inhProp→isContr
    [ record
       { relation =
         record
           { isSetX = isSet× (perY .isSetX) isSetUnit*
           ; ∣_∣ = λ { (y , tt*) r → r ⊩ ∣ perY .equality ∣ (y , y) }
           ; isPropValued = λ { (y , tt*) r → perY .equality .isPropValued _ _ } }
       ; isStrict =
         let
           prover : ApplStrTerm as 1
           prover = ` pair ̇ # fzero ̇ # fzero
         in
         return
           ((λ* prover) ,
            (λ { y tt* r r⊩y~y →
              subst
                (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y))
                (sym
                  (pr₁ ⨾ (λ* prover ⨾ r)
                    ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ⟩
                  pr₁ ⨾ (pair ⨾ r ⨾ r)
                    ≡⟨ pr₁pxy≡x _ _ ⟩
                  r
                    ∎))
                r⊩y~y ,
              tt* }))
       ; isRelational =
         do
         (trY , trY⊩isTransitiveY) ← perY .isTransitive
         (smY , smY⊩isSymmetricY) ← perY .isSymmetric
         let
           prover : ApplStrTerm as 1
           prover = ` trY ̇ (` pair ̇ (` smY ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₁ ̇ # fzero))
         return
           (λ* prover ,
            (λ { y y' tt* tt* a b c a⊩y~y' b⊩y~y tt* →
              let
                proofEq : λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)) ≡ trY ⨾ (pair ⨾ (smY ⨾ a) ⨾ a)
                proofEq =
                  λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))
                    ≡⟨ λ*ComputationRule prover ((pair ⨾ a ⨾ (pair ⨾ b ⨾ c)) ∷ []) ⟩
                  (trY ⨾ (pair ⨾ (smY ⨾ (pr₁ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))) ⨾ (pr₁ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))))
                    ≡⟨ cong₂ (λ x y → trY ⨾ (pair ⨾ (smY ⨾ x) ⨾ y)) (pr₁pxy≡x _ _) (pr₁pxy≡x _ _) ⟩
                  trY ⨾ (pair ⨾ (smY ⨾ a) ⨾ a)
                    ∎
              in
              subst
                (λ r → r ⊩ ∣ perY .equality ∣ (y' , y'))
                (sym proofEq)
                (trY⊩isTransitiveY y' y y' (smY ⨾ a) a (smY⊩isSymmetricY y y' a a⊩y~y') a⊩y~y') }))
       ; isSingleValued = return (k , (λ { _ tt* tt* _ _ _ _ → tt* })) -- nice
       ; isTotal = return (Id , (λ y r r⊩y~y → return (tt* , subst (λ r → r ⊩ ∣ perY .equality ∣ (y , y)) (sym (Ida≡a _)) r⊩y~y)))
       } ]
    λ f g →
      setQuotElimProp2
        (λ f g → squash/ f g)
        (λ F G →
          eq/
          F G
          let
            F≤G : pointwiseEntailment perY terminalPartialEquivalenceRelation F G
            F≤G =
              (do
                (tlG , tlG⊩isTotalG) ← G .isTotal
                (stF , stF⊩isStrictF) ← F .isStrict
                let
                  prover : ApplStrTerm as 1
                  prover = ` tlG ̇ (` pr₁ ̇ (` stF ̇ # fzero))
                return
                  (λ* prover ,
                  (λ { y tt* r r⊩Fx →
                    transport
                      (propTruncIdempotent (G .relation .isPropValued _ _))
                      (tlG⊩isTotalG y (pr₁ ⨾ (stF ⨾ r)) (stF⊩isStrictF y tt* r r⊩Fx .fst)
                        >>= λ { (tt* , ⊩Gy) → return (subst (λ r' → r' ⊩ ∣ G .relation ∣ (y , tt*)) (sym (λ*ComputationRule prover (r ∷ []))) ⊩Gy) }) })))
          in F≤G , (F≤G→G≤F perY terminalPartialEquivalenceRelation F G F≤G))
        f g

TerminalRT : Terminal RT
TerminalRT =
  (Unit* , terminalPartialEquivalenceRelation) , (λ { (Y , perY) → isTerminalTerminalPartialEquivalenceRelation perY})
