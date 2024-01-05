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

module Realizability.Tripos.Prealgebra.Absorbtion {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
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

  `if_then_else_ : ∀ {n} → Term as n → Term as n → Term as n → Term as n
  `if c then t else e = ` Id ̇ c ̇ t ̇ e

  absorb⊔ : PredicateX → PredicateX → PredicateX
  absorb⊔ x y = x ⊔ (x ⊓ y)

  absorb⊓ : PredicateX → PredicateX → PredicateX
  absorb⊓ x y = x ⊓ (x ⊔ y)

  absorb⊔≤x : ∀ x y → absorb⊔ x y ≤ x
  absorb⊔≤x x y =
    do
      let
        proof : Term as 1
        proof = `if ` pr₁ ̇ # fzero then ` pr₂ ̇ # fzero else (` pr₁ ̇ (` pr₂ ̇ # fzero))
      return
        ((λ* proof) ,
          λ x' a a⊩x⊔x⊓y →
            transport
            (propTruncIdempotent (x .isPropValued x' (λ* proof ⨾ a)))
            (a⊩x⊔x⊓y >>=
              λ { (inl (pr₁a≡k , pr₂a⊩x)) →
                       let
                         proof≡pr₂a : λ* proof ⨾ a ≡ pr₂ ⨾ a
                         proof≡pr₂a =
                           λ* proof ⨾ a
                             ≡⟨ λ*ComputationRule proof (a ∷ []) ⟩
                           if (pr₁ ⨾ a) then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))
                             ≡⟨ cong (λ x → if x then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))) pr₁a≡k ⟩
                           if true then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))
                             ≡⟨ ifTrueThen _ _ ⟩
                           pr₂ ⨾ a
                             ∎
                       in ∣ subst (λ r → r ⊩ ∣ x ∣ x') (sym proof≡pr₂a) pr₂a⊩x ∣₁
                ; (inr (pr₁a≡k' , pr₂a⊩x⊓y)) →
                       let
                         proof≡pr₁pr₂a : λ* proof ⨾ a ≡ pr₁ ⨾ (pr₂ ⨾ a)
                         proof≡pr₁pr₂a =
                           λ* proof ⨾ a
                             ≡⟨ λ*ComputationRule proof (a ∷ []) ⟩
                           if (pr₁ ⨾ a) then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))
                             ≡⟨ cong (λ x → if x then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))) pr₁a≡k' ⟩
                           if false then (pr₂ ⨾ a) else (pr₁ ⨾ (pr₂ ⨾ a))
                             ≡⟨ ifFalseElse _ _ ⟩
                           pr₁ ⨾ (pr₂ ⨾ a)
                             ∎
                       in ∣ subst (λ r → r ⊩ ∣ x ∣ x') (sym proof≡pr₁pr₂a) (pr₂a⊩x⊓y .fst) ∣₁ }))

  x≤absorb⊔ : ∀ x y → x ≤ absorb⊔ x y
  x≤absorb⊔ x y = ∣ pair ⨾ true , (λ x' a a⊩x → ∣ inl ((pr₁pxy≡x _ _) , (subst (λ r → r ⊩ ∣ x ∣ x') (sym (pr₂pxy≡y _ _)) a⊩x)) ∣₁) ∣₁

  absorb⊓≤x : ∀ x y → absorb⊓ x y ≤ x
  absorb⊓≤x x y = ∣ pr₁ , (λ x' a a⊩x⊓x⊔y → a⊩x⊓x⊔y .fst) ∣₁

  x≤absorb⊓ : ∀ x y → x ≤ absorb⊓ x y
  x≤absorb⊓ x y =
    let
      proof : Term as 1
      proof = ` pair ̇ # fzero ̇ (` pair ̇ ` true ̇ # fzero)
    in
    return
      ((λ* proof) ,
      (λ x' a a⊩x →
        let
          pr₁proof≡a : pr₁ ⨾ (λ* proof ⨾ a) ≡ a
          pr₁proof≡a =
            pr₁ ⨾ (λ* proof ⨾ a)
              ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
            pr₁ ⨾ (pair ⨾ a ⨾ (pair ⨾ true ⨾ a))
              ≡⟨ pr₁pxy≡x _ _ ⟩
            a
              ∎

          pr₂proof≡pair⨾true⨾a : pr₂ ⨾ (λ* proof ⨾ a) ≡ pair ⨾ true ⨾ a
          pr₂proof≡pair⨾true⨾a =
            pr₂ ⨾ (λ* proof ⨾ a)
              ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule proof (a ∷ [])) ⟩
            pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ true ⨾ a))
              ≡⟨ pr₂pxy≡y _ _ ⟩
            pair ⨾ true ⨾ a
              ∎

          pr₁pr₂proof≡true : pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ true
          pr₁pr₂proof≡true =
            pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
              ≡⟨ cong (λ x → pr₁ ⨾ x) pr₂proof≡pair⨾true⨾a ⟩
            pr₁ ⨾ (pair ⨾ true ⨾ a)
              ≡⟨ pr₁pxy≡x _ _ ⟩
            true
              ∎

          pr₂pr₂proof≡a : pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ a
          pr₂pr₂proof≡a =
            pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
              ≡⟨ cong (λ x → pr₂ ⨾ x) pr₂proof≡pair⨾true⨾a ⟩
            pr₂ ⨾ (pair ⨾ true ⨾ a)
              ≡⟨ pr₂pxy≡y _ _ ⟩
            a
              ∎
          
        in
        subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₁proof≡a) a⊩x ,
        ∣ inl (pr₁pr₂proof≡true , subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₂pr₂proof≡a) a⊩x) ∣₁))
