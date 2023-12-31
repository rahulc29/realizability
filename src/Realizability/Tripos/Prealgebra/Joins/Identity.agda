{-# OPTIONS --allow-unsolved-metas #-}
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

module Realizability.Tripos.Prealgebra.Joins.Identity {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate ca
open import Realizability.Tripos.Prealgebra.Joins.Commutativity ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  private PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  open PreorderReasoning preorder≤


  pre0 : PredicateX
  Predicate.isSetX pre0 = isSetX'
  ∣ pre0 ∣ = λ x a → ⊥*
  Predicate.isPropValued pre0 = λ x a → isProp⊥*

  x⊔0≤x : ∀ x → x ⊔ pre0 ≤ x
  x⊔0≤x x =
    do
      return
        (pr₂ ,
          (λ x' a a⊩x⊔0 →
            transport
              (propTruncIdempotent (x .isPropValued x' (pr₂ ⨾ a)))
              (do
                a⊩x⊔0 ← a⊩x⊔0
                let
                  goal : ((pr₁ ⨾ a ≡ k) × (pr₂ ⨾ a) ⊩ ∣ x ∣ x') ⊎ ((pr₁ ⨾ a ≡ k') × ⊥*) → (pr₂ ⨾ a) ⊩ ∣ x ∣ x'
                  goal = λ { (inl (pr₁a≡k , pr₂a⊩x)) → pr₂a⊩x ; (inr (_ , bottom)) → ⊥*rec bottom }
                return (goal a⊩x⊔0))))

  x≤0⊔x : ∀ x → x ≤ (pre0 ⊔ x)
  x≤0⊔x x =
    let
      proof : Term as 1
      proof = ` pair ̇ ` false ̇ # fzero
    in
      return
        ((λ* proof) ,
          (λ x' a a⊩x →
            let
              pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ false
              pr₁proofEq =
                pr₁ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
                pr₁ ⨾ (pair ⨾ false ⨾ a)
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                false
                  ∎

              pr₂proofEq : pr₂ ⨾ (λ* proof ⨾ a) ≡ a
              pr₂proofEq =
                pr₂ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
                pr₂ ⨾ (pair ⨾ false ⨾ a)
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                a
                  ∎
            in
            ∣ inr (pr₁proofEq , subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₂proofEq) a⊩x) ∣₁))

  x≤x⊔0 : ∀ x → x ≤ x ⊔ pre0
  x≤x⊔0 x =
    let
      proof : Term as 1
      proof = ` pair ̇ ` true ̇ # fzero
    in return
      ((λ* proof) ,
        (λ x' a a⊩x →
          let
            pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ true
            pr₁proofEq =
              pr₁ ⨾ (λ* proof ⨾ a)
                ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
              pr₁ ⨾ (pair ⨾ true ⨾ a)
                ≡⟨ pr₁pxy≡x _ _ ⟩
              true
                ∎

            pr₂proofEq : pr₂ ⨾ (λ* proof ⨾ a) ≡ a
            pr₂proofEq =
              pr₂ ⨾ (λ* proof ⨾ a)
                ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
              pr₂ ⨾ (pair ⨾ true ⨾ a)
                ≡⟨ pr₂pxy≡y _ _ ⟩
              a
                ∎
          in
          ∣ inl (pr₁proofEq , subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₂proofEq) a⊩x) ∣₁))
  0⊔x≤x : ∀ x → pre0 ⊔ x ≤ x
  0⊔x≤x x =
    pre0 ⊔ x
      ≲⟨ a⊔b→b⊔a X isSetX' pre0 x ⟩
    x ⊔ pre0
      ≲⟨ x⊔0≤x x ⟩
    x
      ◾

  
  

