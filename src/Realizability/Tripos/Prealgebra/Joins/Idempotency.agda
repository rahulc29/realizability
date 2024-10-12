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

module Realizability.Tripos.Prealgebra.Joins.Idempotency {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Joins.Commutativity ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _ (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  private PredicateX = Predicate X
  open Predicate
  open PredicateProperties X

  x⊔x≤x : ∀ x → x ⊔ x ≤ x
  x⊔x≤x x =
      return
        (pr₂ ,
          (λ x' a a⊩x⊔x →
            transport
              (propTruncIdempotent (x .isPropValued x' (pr₂ ⨾ a)))
              (do
                a⊩x⊔x ← a⊩x⊔x
                let
                  goal : ((pr₁ ⨾ a ≡ k) × (pr₂ ⨾ a) ⊩ ∣ x ∣ x') ⊎ ((pr₁ ⨾ a ≡ k') × (pr₂ ⨾ a) ⊩ ∣ x ∣ x') → (pr₂ ⨾ a) ⊩ ∣ x ∣ x'
                  goal = λ { (inl (_ , pr₂a⊩x)) → pr₂a⊩x ; (inr (_ , pr₂a⊩x)) → pr₂a⊩x }
                return (goal a⊩x⊔x))))

  x≤x⊔x : ∀ x → x ≤ x ⊔ x
  x≤x⊔x x =
    let prover = ` pair ̇ ` true ̇ # zero in
    ∣ λ* prover ,
      (λ x' a a⊩x →
        subst
          (λ r → r ⊩ ∣ x ⊔ x ∣ x')
          (sym (λ*ComputationRule prover a))
          ∣ inl (pr₁pxy≡x _ _ , subst (λ r → r ⊩ ∣ x ∣ x') (sym (pr₂pxy≡y _ _)) a⊩x) ∣₁) ∣₁
