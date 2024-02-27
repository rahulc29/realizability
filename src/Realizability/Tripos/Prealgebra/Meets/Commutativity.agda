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

module Realizability.Tripos.Prealgebra.Meets.Commutativity {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

module _ (X : Type ℓ') (isSetX' : isSet X) where
  
  private PredicateX = Predicate  X
  open Predicate
  open PredicateProperties  X
  open PreorderReasoning preorder≤

  x⊓y≤y⊓x : ∀ x y → x ⊓ y ≤ y ⊓ x
  x⊓y≤y⊓x x y =
    do
      let
        proof : Term as 1
        proof = ` pair ̇ (` pr₂ ̇ # fzero) ̇ (` pr₁ ̇ # fzero)
      return
        (λ* proof ,
          (λ x' a a⊩x⊓y →
            subst
              (λ r → r ⊩ ∣ y ⊓ x ∣ x')
              (sym (λ*ComputationRule proof (a ∷ []) ))
              ((subst (λ r → r ⊩ ∣ y ∣ x') (sym (pr₁pxy≡x _ _)) (a⊩x⊓y .snd)) ,
               (subst (λ r → r ⊩ ∣ x ∣ x') (sym (pr₂pxy≡y _ _)) (a⊩x⊓y .fst)))))

  antiSym→x⊓z≤y⊓z : ∀ x y z → x ≤ y → y ≤ x → x ⊓ z ≤ y ⊓ z
  antiSym→x⊓z≤y⊓z x y z x≤y y≤x =
    do
      (f , f⊩x≤y) ← x≤y
      (g , g⊩y≤x) ← y≤x
      let
        proof : Term as 1
        proof = ` pair ̇ (` f ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₂ ̇ # fzero)
      return
        ((λ* proof) ,
          (λ x' a a⊩x⊓z →
            subst
              (λ r → r ⊩ ∣ y ⊓ z ∣ x')
              (sym (λ*ComputationRule proof (a ∷ [])))
              ((subst (λ r → r ⊩ ∣ y ∣ x') (sym (pr₁pxy≡x _ _)) (f⊩x≤y x' (pr₁ ⨾ a) (a⊩x⊓z .fst))) ,
               (subst (λ r → r ⊩ ∣ z ∣ x') (sym (pr₂pxy≡y _ _)) (a⊩x⊓z .snd)))))


  antiSym→x⊓y≤x⊓z : ∀ x y z → y ≤ z → z ≤ y → x ⊓ y ≤ x ⊓ z
  antiSym→x⊓y≤x⊓z x y z y≤z z≤y =
    do
      (f , f⊩y≤z) ← y≤z
      (g , g⊩z≤y) ← z≤y
      let
        proof : Term as 1
        proof = ` pair ̇ (`  pr₁ ̇ # fzero) ̇ (` f ̇ (` pr₂ ̇ # fzero))
      return
        ((λ* proof) ,
          (λ { x' a (pr₁a⊩x , pr₂a⊩y) →
            subst
              (λ r → r ⊩ ∣ x ⊓ z ∣ x')
              (sym (λ*ComputationRule proof (a ∷ [])))
              ((subst (λ r → r ⊩ ∣ x ∣ x') (sym (pr₁pxy≡x _ _)) pr₁a⊩x) ,
               (subst (λ r → r ⊩ ∣ z ∣ x') (sym (pr₂pxy≡y _ _)) (f⊩y≤z x' (pr₂ ⨾ a) pr₂a⊩y))) }))
