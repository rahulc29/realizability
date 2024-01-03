open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec* to ⊥*rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary.Order.Preorder
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)

module Realizability.Tripos.Prealgebra.Meets.Identity {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate ca
open import Realizability.Tripos.Prealgebra.Meets.Commutativity ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  private PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  open PreorderReasoning preorder≤

  pre1 : PredicateX
  Predicate.isSetX pre1 = isSetX'
  Predicate.∣ pre1 ∣ = λ x a → Unit*
  Predicate.isPropValued pre1 = λ x a → isPropUnit*

  x⊓1≤x : ∀ x → x ⊓ pre1 ≤ x
  x⊓1≤x x = ∣ pr₁ , (λ x' a a⊩x⊓1 → a⊩x⊓1 .fst) ∣₁

  x≤x⊓1 : ∀ x → x ≤ x ⊓ pre1
  x≤x⊓1 x =
    do
      let
        proof : Term as 1
        proof = ` pair ̇ # fzero ̇ ` true
      return ((λ* proof) , (λ x' a a⊩x → subst (λ r → ∣ x ⊓ pre1 ∣ x' r) (sym (λ*ComputationRule proof (a ∷ []))) (subst (λ r → r ⊩ ∣ x ∣ x') (sym (pr₁pxy≡x _ _)) a⊩x , tt*)))
