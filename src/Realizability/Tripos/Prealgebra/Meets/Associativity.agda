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

module Realizability.Tripos.Prealgebra.Meets.Associativity {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Joins.Commutativity ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _  (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  open Predicate
  open PredicateProperties X
  open PreorderReasoning preorder≤

  x⊓_y⊓z≤x⊓y_⊓z : ∀ x y z → x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
  x⊓_y⊓z≤x⊓y_⊓z x y z =
    let
      proof : Term as 1
      proof = ` pair ̇ (` pair ̇ (` pr₁ ̇ # zero) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))) ̇ (` pr₂ ̇ (` pr₂ ̇ # zero))
    in
      return
        (λ* proof ,
          λ x' a a⊩x⊓_y⊓z →
            let
              λ*eq = λ*ComputationRule proof a
              
              pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a))
              pr₁proofEq =
                pr₁ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₁ ⨾ x) λ*eq ⟩
                pr₁ ⨾ (pair ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a))) ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a))
                  ∎

              pr₁pr₁proofEq : pr₁ ⨾ (pr₁ ⨾ (λ* proof ⨾ a)) ≡ pr₁ ⨾ a
              pr₁pr₁proofEq =
                pr₁ ⨾ (pr₁ ⨾ (λ* proof ⨾ a))
                  ≡⟨ cong (λ x → pr₁ ⨾ x) pr₁proofEq ⟩
                pr₁ ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                pr₁ ⨾ a
                  ∎

              pr₂pr₁proofEq : pr₂ ⨾ (pr₁ ⨾ (λ* proof ⨾ a)) ≡ pr₁ ⨾ (pr₂ ⨾ a)
              pr₂pr₁proofEq =
                pr₂ ⨾ (pr₁ ⨾ (λ* proof ⨾ a))
                  ≡⟨ cong (λ x → pr₂ ⨾ x) pr₁proofEq ⟩
                pr₂ ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                pr₁ ⨾ (pr₂ ⨾ a)
                  ∎

              pr₂proofEq : pr₂ ⨾ (λ* proof ⨾ a) ≡ pr₂ ⨾ (pr₂ ⨾ a)
              pr₂proofEq =
                pr₂ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₂ ⨾ x) λ*eq ⟩
                pr₂ ⨾ (pair ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ (pr₁ ⨾ (pr₂ ⨾ a))) ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                pr₂ ⨾ (pr₂ ⨾ a)
                  ∎
            in
              (subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₁pr₁proofEq) (a⊩x⊓_y⊓z .fst) ,
               subst (λ r → r ⊩ ∣ y ∣ x') (sym pr₂pr₁proofEq) (a⊩x⊓_y⊓z .snd .fst)) ,
               subst (λ r → r ⊩ ∣ z ∣ x') (sym pr₂proofEq) (a⊩x⊓_y⊓z .snd .snd))

  x⊓y_⊓z≤x⊓_y⊓z : ∀ x y z → (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
  x⊓y_⊓z≤x⊓_y⊓z x y z =
    let
      proof : Term as 1
      proof = ` pair ̇ (` pr₁ ̇ (` pr₁ ̇ # zero)) ̇ (` pair ̇ (` pr₂ ̇ (` pr₁ ̇ # zero)) ̇ (` pr₂ ̇ # zero))
    in
      return
        (λ* proof ,
          λ { x' a ((pr₁pr₁a⊩x , pr₂pr₁a⊩y) , pr₂a⊩z) →
            let
              λ*eq = λ*ComputationRule proof a

              pr₂proofEq : pr₂ ⨾ (λ* proof ⨾ a) ≡ pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a)
              pr₂proofEq =
                pr₂ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₂ ⨾ x) λ*eq ⟩
                pr₂ ⨾ (pair ⨾ (pr₁ ⨾ (pr₁ ⨾ a)) ⨾ (pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a)
                  ∎

              pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ pr₁ ⨾ (pr₁ ⨾ a)
              pr₁proofEq =
                pr₁ ⨾ (λ* proof ⨾ a)
                  ≡⟨ cong (λ x → pr₁ ⨾ x) λ*eq ⟩
                pr₁ ⨾ (pair ⨾ (pr₁ ⨾ (pr₁ ⨾ a)) ⨾ (pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a)))
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                pr₁ ⨾ (pr₁ ⨾ a)
                  ∎

              pr₁pr₂proofEq : pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ pr₂ ⨾ (pr₁ ⨾ a)
              pr₁pr₂proofEq =
                pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                  ≡⟨ cong (λ x → pr₁ ⨾ x) pr₂proofEq ⟩
                pr₁ ⨾ (pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a))
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                pr₂ ⨾ (pr₁ ⨾ a)
                  ∎

              pr₂pr₂proofEq : pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ pr₂ ⨾ a
              pr₂pr₂proofEq =
                pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                  ≡⟨ cong (λ x → pr₂ ⨾ x) pr₂proofEq ⟩
                pr₂ ⨾ (pair ⨾ (pr₂ ⨾ (pr₁ ⨾ a)) ⨾ (pr₂ ⨾ a))
                  ≡⟨ pr₂pxy≡y _ _ ⟩
                pr₂ ⨾ a
                  ∎
                  
            in
              subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₁proofEq) pr₁pr₁a⊩x ,
              subst (λ r → r ⊩ ∣ y ∣ x') (sym pr₁pr₂proofEq) pr₂pr₁a⊩y ,
              subst (λ r → r ⊩ ∣ z ∣ x') (sym pr₂pr₂proofEq) pr₂a⊩z })

  
