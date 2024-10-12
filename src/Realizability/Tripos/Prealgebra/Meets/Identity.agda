open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec* to ⊥*rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary.Order.Preorder
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure 

module Realizability.Tripos.Prealgebra.Meets.Identity {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Meets.Commutativity {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _ (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  private PredicateX = Predicate X
  open Predicate
  open PredicateProperties X
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
        proof = ` pair ̇ # zero ̇ ` true
      return
        ((λ* proof) ,
          (λ x' a a⊩x →
            subst
              (λ r → ∣ x ⊓ pre1 ∣ x' r)
              (sym (λ*ComputationRule proof a))
              (subst
                (λ r → r ⊩ ∣ x ∣ x')
                (sym (pr₁pxy≡x _ _))
                a⊩x , tt*)))

  1⊓x≤x : ∀ x → pre1 ⊓ x ≤ x
  1⊓x≤x x = ∣ pr₂ , (λ x' a a⊩1⊓x → a⊩1⊓x .snd) ∣₁

  x≤1⊓x : ∀ x → x ≤ pre1 ⊓ x
  x≤1⊓x x =
    do
      let
        proof : Term as 1
        proof = ` pair ̇ ` false ̇ # zero
      return
        ((λ* proof) ,
          (λ x' a a⊩x →
            subst
              (λ r → r ⊩ ∣ pre1 ⊓ x ∣ x')
              (sym (λ*ComputationRule proof a))
              (tt* ,
              (subst
                (λ r → r ⊩ ∣ x ∣ x')
                (sym (pr₂pxy≡y _ _))
                a⊩x))))
