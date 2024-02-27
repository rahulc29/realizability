open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Sum renaming (rec to sumRec)
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad

module Realizability.Tripos.Prealgebra.Joins.Commutativity {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) where
  open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
  private PredicateX = Predicate X
  open Predicate
  open PredicateProperties  X
  open PreorderReasoning preorder≤

  -- ⊔ is commutative upto anti-symmetry
  a⊔b→b⊔a : ∀ a b → a ⊔ b ≤ b ⊔ a
  a⊔b→b⊔a a b =
    do
      let prover = ` Id ̇ (` pr₁ ̇ (# fzero)) ̇ (` pair ̇ ` k' ̇ (` pr₂ ̇ (# fzero))) ̇ (` pair ̇ ` k ̇ (` pr₂ ̇ (# fzero)))
      let λ*eq = λ (r : A) → λ*ComputationRule prover (r ∷ [])
      return
        (λ* prover ,
          λ x r r⊩a⊔b →
            r⊩a⊔b >>=
              λ { (inl (pr₁r≡k  , pr₂r⊩a)) →
                  ∣ inr ((pr₁ ⨾ (λ* prover ⨾ r)
                           ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*eq r) ⟩
                          pr₁ ⨾ (Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                           ≡⟨ cong (λ x → pr₁ ⨾ (Id ⨾ x ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))) (pr₁r≡k) ⟩
                          pr₁ ⨾ (Id ⨾ k ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                           ≡⟨ cong (λ x → pr₁ ⨾ x) (ifTrueThen _ _) ⟩
                          pr₁ ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r))
                           ≡⟨ pr₁pxy≡x _ _ ⟩
                          k'
                           ∎) ,
                        subst
                          (λ r → r ⊩ ∣ a ∣ x)
                          (sym
                            ((pr₂ ⨾ (λ* prover ⨾ r)
                                ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*eq r) ⟩
                              pr₂ ⨾ (Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                                ≡⟨ cong (λ x → pr₂ ⨾ (Id ⨾ x ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))) (pr₁r≡k) ⟩
                              pr₂ ⨾ (Id ⨾ k ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                                ≡⟨ cong (λ x → pr₂ ⨾ x) (ifTrueThen _ _) ⟩
                              pr₂ ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r))
                                ≡⟨ pr₂pxy≡y _ _ ⟩
                              pr₂ ⨾ r
                                ∎)))
                          pr₂r⊩a) ∣₁
                ; (inr (pr₁r≡k' , pr₂r⊩b)) →
                  ∣ inl (((pr₁ ⨾ (λ* prover ⨾ r)
                           ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*eq r) ⟩
                          pr₁ ⨾ (Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                           ≡⟨ cong (λ x → pr₁ ⨾ (Id ⨾ x ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))) pr₁r≡k' ⟩
                          pr₁ ⨾ (Id ⨾ k' ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                           ≡⟨ cong (λ x → pr₁ ⨾ x) (ifFalseElse _ _) ⟩
                          pr₁ ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r))
                           ≡⟨ pr₁pxy≡x _ _ ⟩
                          k
                           ∎) ,
                        subst
                          (λ r → r ⊩ ∣ b ∣ x)
                          (sym
                            ((pr₂ ⨾ (λ* prover ⨾ r)
                                ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*eq r) ⟩
                              pr₂ ⨾ (Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                                ≡⟨ cong (λ x → pr₂ ⨾ (Id ⨾ x ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))) pr₁r≡k' ⟩
                              pr₂ ⨾ (Id ⨾ k' ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r)))
                                ≡⟨ cong (λ x → pr₂ ⨾ x) (ifFalseElse _ _) ⟩
                              pr₂ ⨾ (pair ⨾ k ⨾ (pr₂ ⨾ r))
                                ≡⟨ pr₂pxy≡y _ _ ⟩
                              pr₂ ⨾ r
                                ∎)))
                          pr₂r⊩b)) ∣₁ })

  antiSym→x⊔z≤y⊔z : ∀ x y z → x ≤ y → y ≤ x → (x ⊔ z) ≤ (y ⊔ z)
  antiSym→x⊔z≤y⊔z x y z x≤y y≤x =
    do
      (x⊨y , x⊨yProves) ← x≤y
      let prover = ` Id ̇ (` pr₁ ̇ (# fzero)) ̇ (` pair ̇ ` k ̇ (` x⊨y ̇ (` pr₂ ̇ (# fzero)))) ̇ (` pair ̇ ` k' ̇ (` pr₂ ̇ (# fzero)))
      return
        (λ* prover ,
          λ x' a a⊩x⊔zx' →
            equivFun
              (propTruncIdempotent≃
                ((y ⊔ z) .isPropValued x' (λ* prover ⨾ a)))
                (do
                  a⊩x⊔z ← a⊩x⊔zx'
                  return
                    ∣ sumRec
                      (λ { (pr₁⨾a≡k , pr₂⨾a⊩xx') →
                        inl
                          (((pr₁ ⨾ (λ* prover ⨾ a))
                             ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ [])) ⟩
                            (pr₁ ⨾ (Id ⨾ (pr₁ ⨾ a) ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))
                             ≡⟨ cong (λ x → (pr₁ ⨾ (Id ⨾ x ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))) pr₁⨾a≡k ⟩
                            (pr₁ ⨾ (Id ⨾ k ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))
                             ≡⟨ cong (λ x → pr₁ ⨾ x) (ifTrueThen _ _) ⟩
                            (pr₁ ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))))
                             ≡⟨ pr₁pxy≡x _ _ ⟩
                            (k)
                             ∎) ,
                             subst
                               (λ r → r ⊩ ∣ y ∣ x')
                               (sym
                                 (pr₂ ⨾ (λ* prover ⨾ a)
                                   ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ [])) ⟩
                                  pr₂ ⨾ (Id ⨾ (pr₁ ⨾ a) ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a)))
                                   ≡⟨ cong (λ x → (pr₂ ⨾ (Id ⨾ x ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))) pr₁⨾a≡k ⟩
                                  pr₂ ⨾ (Id ⨾ k ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a)))
                                   ≡⟨ cong (λ x → pr₂ ⨾ x) (ifTrueThen _ _) ⟩
                                  pr₂ ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a)))
                                   ≡⟨ pr₂pxy≡y _ _ ⟩
                                  x⊨y ⨾ (pr₂ ⨾ a)
                                   ∎))
                               (x⊨yProves x' (pr₂ ⨾ a) pr₂⨾a⊩xx')) })
                      (λ { (pr₁⨾a≡k' , pr₂a⊩zx') →
                        inr
                         ((((pr₁ ⨾ (λ* prover ⨾ a))
                             ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ [])) ⟩
                            (pr₁ ⨾ (Id ⨾ (pr₁ ⨾ a) ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))
                             ≡⟨ cong (λ x → (pr₁ ⨾ (Id ⨾ x ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))) pr₁⨾a≡k' ⟩
                            (pr₁ ⨾ (Id ⨾ k' ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))
                             ≡⟨ cong (λ x → pr₁ ⨾ x) (ifFalseElse _ _) ⟩
                            (pr₁ ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a)))
                             ≡⟨ pr₁pxy≡x _ _ ⟩
                            (k')
                             ∎)) ,
                               subst
                                 (λ r → r ⊩ ∣ z ∣ x')
                                 (sym
                                  ((pr₂ ⨾ (λ* prover ⨾ a)
                                   ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ [])) ⟩
                                  pr₂ ⨾ (Id ⨾ (pr₁ ⨾ a) ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a)))
                                   ≡⟨ cong (λ x → (pr₂ ⨾ (Id ⨾ x ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))))) pr₁⨾a≡k' ⟩
                                  pr₂ ⨾ (Id ⨾ k' ⨾ (pair ⨾ k ⨾ (x⊨y ⨾ (pr₂ ⨾ a))) ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a)))
                                   ≡⟨ cong (λ x → pr₂ ⨾ x) (ifFalseElse _ _) ⟩
                                  pr₂ ⨾ (pair ⨾ k' ⨾ (pr₂ ⨾ a))
                                   ≡⟨ pr₂pxy≡y _ _ ⟩
                                  pr₂ ⨾ a
                                    ∎)))
                                 pr₂a⊩zx') })
                      a⊩x⊔z ∣₁))
