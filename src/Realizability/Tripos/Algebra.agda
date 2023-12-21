{-# OPTIONS --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Realizability.Tripos.PosetReflection
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Fin
open import Cubical.Data.Sum renaming (rec to sumRec)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients renaming (rec to quotRec; rec2 to quotRec2)
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.Poset

module Realizability.Tripos.Algebra {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where
open import Realizability.Tripos.Predicate ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

λ*ComputationRule = `λ*ComputationRule as fefermanStructure
λ* = `λ* as fefermanStructure

module AlgebraicProperties {ℓ' ℓ''} (X : Type ℓ') where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  -- ⇒ is Heyting implication
  a⊓b≤c→a≤b⇒c : ∀ a b c → (a ⊓ b ≤ c) → a ≤ (b ⇒ c)
  a⊓b≤c→a≤b⇒c a b c a⊓b≤c =
    do
      (a~ , a~proves) ← a⊓b≤c
      let prover = (` a~ ̇ (` pair ̇ (# fzero)  ̇ (# fone)))
      return
        (λ* prover ,
          λ x aₓ aₓ⊩ax bₓ bₓ⊩bx →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (aₓ ∷ bₓ ∷ [])))
              (a~proves
                x
                (pair ⨾ aₓ ⨾ bₓ)
                ((subst (λ r → r ⊩ ∣ a ∣ x) (sym (pr₁pxy≡x _ _)) aₓ⊩ax) ,
                 (subst (λ r → r ⊩ ∣ b ∣ x) (sym (pr₂pxy≡y _ _)) bₓ⊩bx))))

  a≤b⇒c→a⊓b≤c : ∀ a b c → a ≤ (b ⇒ c) → (a ⊓ b ≤ c)
  a≤b⇒c→a⊓b≤c a b c a≤b⇒c =
    do
      (a~ , a~proves) ← a≤b⇒c
      let prover = ` a~ ̇ (` pr₁ ̇ (# fzero)) ̇ (` pr₂ ̇ (# fzero))
      return
        (λ* prover ,
          λ { x abₓ (pr₁abₓ⊩ax , pr₂abₓ⊩bx) →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (abₓ ∷ [])))
              (a~proves x (pr₁ ⨾ abₓ) pr₁abₓ⊩ax (pr₂ ⨾ abₓ) pr₂abₓ⊩bx) })

  ⇒isRightAdjointOf⊓ : ∀ a b c → (a ⊓ b ≤ c) ≡ (a ≤ b ⇒ c)
  ⇒isRightAdjointOf⊓ a b c = hPropExt (isProp≤ (a ⊓ b) c) (isProp≤ a (b ⇒ c)) (a⊓b≤c→a≤b⇒c a b c) (a≤b⇒c→a⊓b≤c a b c)

  open Iso
  open PreorderStr
  open Realizability.Tripos.PosetReflection.Properties _≤_ (preorder≤ .snd .isPreorder)

  PredicateAlgebra = PosetReflection _≤_

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

  _l∨_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a l∨ b =
    quotRec2
      squash/
      (λ x y → [ x ⊔ y ])
      (λ x y z (x≤y , y≤x) → eq/ (x ⊔ z) (y ⊔ z) (antiSym→x⊔z≤y⊔z x y z x≤y y≤x , antiSym→x⊔z≤y⊔z y x z y≤x x≤y))
      (λ x y z (y≤z , z≤y) →
        eq/ (x ⊔ y) (x ⊔ z)
          ((x ⊔ y
              ≲⟨ a⊔b→b⊔a x y ⟩
             y ⊔ x
              ≲⟨ antiSym→x⊔z≤y⊔z y z x y≤z z≤y ⟩
             z ⊔ x
              ≲⟨ a⊔b→b⊔a z x ⟩ (
             x ⊔ z ◾)) ,
          (x ⊔ z
            ≲⟨ a⊔b→b⊔a x z ⟩
           z ⊔ x
            ≲⟨ antiSym→x⊔z≤y⊔z z y x z≤y y≤z ⟩
           y ⊔ x
            ≲⟨ a⊔b→b⊔a y x ⟩
           x ⊔ y
            ◾)))
      a b
