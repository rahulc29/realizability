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

module Realizability.Tripos.Prealgebra.Meets.Idempotency {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate ca
open import Realizability.Tripos.Prealgebra.Joins.Commutativity ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  open PreorderReasoning preorder≤

  x⊓x≤x : ∀ x → x ⊓ x ≤ x
  x⊓x≤x x = return (pr₁ , (λ x' a a⊩x⊓x → a⊩x⊓x .fst))

  x≤x⊓x : ∀ x → x ≤ x ⊓ x
  x≤x⊓x x =
    let
      proof : Term as 1
      proof = ` pair ̇ # fzero ̇ # fzero
    in
      return
        ((λ* proof) ,
          (λ x' a a⊩x →
            let λ*eq = λ*ComputationRule proof (a ∷ []) in
            (subst (λ r → r ⊩ ∣ x ∣ x') (sym (cong (λ x → pr₁ ⨾ x) λ*eq ∙ pr₁pxy≡x _ _)) a⊩x) ,
             subst (λ r → r ⊩ ∣ x ∣ x') (sym (cong (λ x → pr₂ ⨾ x) λ*eq ∙ pr₂pxy≡y _ _)) a⊩x))
