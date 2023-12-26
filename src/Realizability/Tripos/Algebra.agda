{-# OPTIONS --allow-unsolved-metas --lossy-unification #-}
open import Realizability.CombinatoryAlgebra
open import Realizability.Tripos.PosetReflection
open import Realizability.Tripos.HeytingAlgebra
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
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients renaming (rec to quotRec; rec2 to quotRec2)
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

module Realizability.Tripos.Algebra {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where
open import Realizability.Tripos.Predicate ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

λ*ComputationRule = `λ*ComputationRule as fefermanStructure
λ* = `λ* as fefermanStructure

module AlgebraicProperties {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) where
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

  _∨l_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a ∨l b =
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

  x⊓y≤x : ∀ x y → x ⊓ y ≤ x
  x⊓y≤x x y = return (pr₁ , (λ x a a⊩x⊓y → a⊩x⊓y .fst))

  x⊓y≤y : ∀ x y → x ⊓ y ≤ y
  x⊓y≤y x y = return (pr₂ , (λ x a a⊩x⊓y → a⊩x⊓y .snd))

  isLowerbound⊓ : ∀ x y → ((x ⊓ y) ≤ x) × ((x ⊓ y) ≤ y)
  isLowerbound⊓ x y = x⊓y≤x x y , x⊓y≤y x y

  isGreatestLowerbound⊓ : ∀ x y z → (z ≤ x) → (z ≤ y) → (z ≤ (x ⊓ y))
  isGreatestLowerbound⊓ x y z z≤x z≤y =
    do
      (z≤x~ , z≤x~proves) ← z≤x
      (z≤y~ , z≤y~proves) ← z≤y
      let
        prover : Term as 1
        prover = ` pair ̇ (` z≤x~ ̇ # fzero) ̇ (` z≤y~ ̇ # fzero)
      return
        (λ* prover ,
          λ x' a a⊩zx →
            subst
              (λ witness → witness ⊩ ∣ x ⊓ y ∣ x')
              (sym (λ*ComputationRule prover (a ∷ [])))
              ((subst (λ witness → witness ⊩ ∣ x ∣ x') (sym (pr₁pxy≡x _ _)) (z≤x~proves x' a a⊩zx)) ,
                subst (λ witness → witness ⊩ ∣ y ∣ x') (sym (pr₂pxy≡y _ _)) (z≤y~proves x' a a⊩zx)))

  _∧l_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a ∧l b =
    quotRec2
      squash/
      (λ x y → [ x ⊓ y ])
      (λ x y z (x≤y , y≤x) →
        eq/
          (x ⊓ z)
          (y ⊓ z)
          (isGreatestLowerbound⊓ y z (x ⊓ z) (x ⊓ z ≲⟨ x⊓y≤x x z ⟩ x ≲⟨ x≤y ⟩ y ◾) (x⊓y≤y x z) ,
           isGreatestLowerbound⊓ x z (y ⊓ z) (y ⊓ z ≲⟨ x⊓y≤x y z ⟩ y ≲⟨ y≤x ⟩ x ◾) (x⊓y≤y y z)))
      (λ x y z (y≤z , z≤y) →
        eq/
          (x ⊓ y)
          (x ⊓ z)
          ((isGreatestLowerbound⊓ x z (x ⊓ y) (x⊓y≤x x y) (x ⊓ y ≲⟨ x⊓y≤y x y ⟩ y ≲⟨ y≤z ⟩ z ◾)) ,
            isGreatestLowerbound⊓ x y (x ⊓ z) (x⊓y≤x x z) (x ⊓ z ≲⟨ x⊓y≤y x z ⟩ z ≲⟨ z≤y ⟩ y ◾)))
      a b

  antiSym→a⇒c≤b⇒c : ∀ a b c → a ≤ b → b ≤ a → (a ⇒ c) ≤ (b ⇒ c)
  antiSym→a⇒c≤b⇒c a b c a≤b b≤a =
    do
      (α , αProves) ← a≤b
      (β , βProves) ← b≤a
      let
        prover : Term as 2
        prover = (# fzero) ̇ (` β ̇ # fone)
      return
        (λ* prover ,
          (λ x r r⊩a⇒c r' r'⊩b →
            subst
              (λ witness → witness ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (r ∷ r' ∷ [])))
              (r⊩a⇒c (β ⨾ r') (βProves x r' r'⊩b))))

  antiSym→a⇒b≤a⇒c : ∀ a b c → b ≤ c → c ≤ b → (a ⇒ b) ≤ (a ⇒ c)
  antiSym→a⇒b≤a⇒c a b c b≤c c≤b =
    do
      (β , βProves) ← b≤c
      (γ , γProves) ← c≤b
      let
        prover : Term as 2
        prover = ` β ̇ ((# fzero) ̇ (# fone))
      return
        (λ* prover ,
          (λ x α α⊩a⇒b a' a'⊩a →
            subst
              (λ r → r ⊩ ∣ c ∣ x)
              (sym (λ*ComputationRule prover (α ∷ a' ∷ [])))
              (βProves x (α ⨾ a') (α⊩a⇒b a' a'⊩a))))

  _→l_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a →l b =
    quotRec2
      squash/
      (λ a b → [ a ⇒ b ])
      (λ a b c (a≤b , b≤a) → eq/ (a ⇒ c) (b ⇒ c) (antiSym→a⇒c≤b⇒c a b c a≤b b≤a , antiSym→a⇒c≤b⇒c b a c b≤a a≤b))
      (λ a b c (b≤c , c≤b) → eq/ (a ⇒ b) (a ⇒ c) (antiSym→a⇒b≤a⇒c a b c b≤c c≤b , antiSym→a⇒b≤a⇒c a c b c≤b b≤c))
      a b

  module ⊔Assoc (x y z : Predicate {ℓ'' = ℓ''} X) where
    →proverTerm : Term as 1
    →proverTerm =
            ` Id ̇
            (` pr₁ ̇ (# fzero)) ̇
            (` pair ̇ ` true ̇ (` pair ̇ ` true ̇ (` pr₂ ̇ (# fzero)))) ̇
            (` Id ̇
              (` pr₁ ̇ (` pr₂ ̇ (# fzero))) ̇
              (` pair ̇ ` true ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ ` pr₂ ̇ # fzero))) ̇
              (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))))

    →prover = λ* →proverTerm

    module _
      (a : A)
      (pr₁a≡true : pr₁ ⨾ a ≡ true) where

      proof = →prover ⨾ a

      proof≡pair⨾true⨾pair⨾true⨾pr₂a : proof ≡ pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))
      proof≡pair⨾true⨾pair⨾true⨾pr₂a =
        proof
          ≡⟨ λ*ComputationRule →proverTerm (a ∷ []) ⟩
        (Id ⨾
         (pr₁ ⨾ a) ⨾
         (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
         (Id ⨾
           (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
           (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ pr₂ ⨾ a))) ⨾
           (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
           ≡⟨  cong (λ x →
                     (Id ⨾
                       x ⨾
                       (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
                       (Id ⨾
                         (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
                         (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ pr₂ ⨾ a))) ⨾
                         (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))))
                pr₁a≡true ⟩
         (Id ⨾
           k ⨾
           (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
           (Id ⨾
             (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
             (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ pr₂ ⨾ a))) ⨾
             (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
            ≡⟨ ifTrueThen _ _ ⟩
          pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))
            ∎

      pr₁⨾proof≡true : pr₁ ⨾ (→prover ⨾ a) ≡ true
      pr₁⨾proof≡true =
                     (pr₁ ⨾ (→prover ⨾ a))
                       ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair⨾true⨾pair⨾true⨾pr₂a ⟩
                     pr₁ ⨾ (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a)))
                       ≡⟨ pr₁pxy≡x _ _ ⟩
                     true
                        ∎

      pr₁pr₂proof≡true : pr₁ ⨾ (pr₂ ⨾ (→prover ⨾ a)) ≡ true
      pr₁pr₂proof≡true =
        pr₁ ⨾ (pr₂ ⨾ proof)
          ≡⟨ cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) proof≡pair⨾true⨾pair⨾true⨾pr₂a ⟩
        pr₁ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))))
          ≡⟨ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ⟩
        pr₁ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))
          ≡⟨ pr₁pxy≡x _ _ ⟩
        true
           ∎

  x⊔_y⊔z≤x⊔y_⊔z : ∀ x y z → (x ⊔ (y ⊔ z)) ≤ ((x ⊔ y) ⊔ z)
  x⊔_y⊔z≤x⊔y_⊔z x y z =
    do
      let
        {-
        if pr₁ a then
          ⟨ true , ⟨ true , pr₂ a ⟩⟩
        else
          if pr₁ (pr₂ a) then
            ⟨ true , ⟨ false , pr₂ (pr₂ a) ⟩⟩
          else
            ⟨ false , pr₂ (pr₂ a) ⟩
        -}
        prover : Term as 1
        prover =
          ` Id ̇
            (` pr₁ ̇ (# fzero)) ̇
            (` pair ̇ ` true ̇ (` pair ̇ ` true ̇ (` pr₂ ̇ (# fzero)))) ̇
            (` Id ̇
              (` pr₁ ̇ (` pr₂ ̇ (# fzero))) ̇
              (` pair ̇ ` true ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ ` pr₂ ̇ # fzero))) ̇
              (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))))
      return
        (λ* prover ,
          λ x' a a⊩x⊔_y⊔z →
            transport
              (propTruncIdempotent (((x ⊔ y) ⊔ z) .isPropValued x' (λ* prover ⨾ a)))
              (a⊩x⊔_y⊔z >>= (λ { (inl (pr₁a≡true , pr₁a⊩x))
                                 → ∣ ∣ inl ( ⊔Assoc.pr₁⨾proof≡true x y z a pr₁a≡true ,
                                       transport
                                         (propTruncIdempotent isPropPropTrunc)
                                         ∣ a⊩x⊔_y⊔z
                                           >>= (λ { (inl (pr₁a≡k , pr₂a⊩x)) → ∣ inl (⊔Assoc.pr₁pr₂proof≡true x y z a pr₁a≡true , {!!}) ∣₁ ; (inr (pr₁a≡k , pr₂a⊩y⊔z)) → {!!} }) ∣₁) ∣₁ ∣₁
                               ; (inr (pr₁a≡false , pr₂a⊩y⊔z)) → {!!}
                                })))

  ∨lAssoc : ∀ x y z → x ∨l (y ∨l z) ≡ ((x ∨l y) ∨l z)
  ∨lAssoc x y z =
    elimProp3
      (λ x y z → squash/ (x ∨l (y ∨l z)) ((x ∨l y) ∨l z))
      (λ x y z → eq/ _ _ ({!!} , {!!}))
      x y z

  0predicate : PredicateAlgebra
  0predicate = [ record { isSetX = isSetX' ; ∣_∣ = λ x a → ⊥* ; isPropValued = λ _ _ → isProp⊥* } ]

  1predicate : PredicateAlgebra
  1predicate = [ record { isSetX = isSetX' ; ∣_∣ = λ x a → Unit* ; isPropValued = λ _ _ → isPropUnit* } ]

  isHeytingAlgebraPredicateAlgebra : IsHeytingAlgebra 0predicate 1predicate _∨l_ _∧l_ _→l_
  isHeytingAlgebraPredicateAlgebra =
    isHeytingAlgebra
      squash/
      (islattice
        (issemilattice
          (iscommmonoid
            (ismonoid
              (issemigroup squash/ {!!}) {!!} {!!}) {!!}) {!!})
        (issemilattice
          (iscommmonoid
            (ismonoid
              (issemigroup squash/ {!!}) {!!} {!!}) {!!}) {!!})
        {!!})
      {!!}
