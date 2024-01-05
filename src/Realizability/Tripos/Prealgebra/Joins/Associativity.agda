{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)

module Realizability.Tripos.Prealgebra.Joins.Associativity {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open import Realizability.Tripos.Prealgebra.Predicate ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure

module _ {ℓ' ℓ''} (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  private PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X

  module →⊔Assoc (x y z : Predicate {ℓ'' = ℓ''} X) where
    →proverTerm : Term as 1
    →proverTerm =
            ` Id ̇
            (` pr₁ ̇ (# fzero)) ̇
            (` pair ̇ ` true ̇ (` pair ̇ ` true ̇ (` pr₂ ̇ (# fzero)))) ̇
            (` Id ̇
              (` pr₁ ̇ (` pr₂ ̇ (# fzero))) ̇
              (` pair ̇ ` true ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero)))) ̇
              (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))))

    →prover = λ* →proverTerm

    module Pr₁a≡true
      (a : A)
      (pr₁a≡true : pr₁ ⨾ a ≡ true) where

      private proof = →prover ⨾ a

      proof≡pair⨾true⨾pair⨾true⨾pr₂a : proof ≡ pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))
      proof≡pair⨾true⨾pair⨾true⨾pr₂a =
        proof
          ≡⟨ λ*ComputationRule →proverTerm (a ∷ []) ⟩
        (Id ⨾
         (pr₁ ⨾ a) ⨾
         (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
         (Id ⨾
           (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
           (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
           (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
           ≡⟨  cong (λ x →
                     (Id ⨾
                       x ⨾
                       (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
                       (Id ⨾
                         (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
                         (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
                         (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))))
                pr₁a≡true ⟩
         (Id ⨾
           k ⨾
           (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
           (Id ⨾
             (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
             (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
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

      pr₂pr₂proof≡pr₂a : pr₂ ⨾ (pr₂ ⨾ proof) ≡ pr₂ ⨾ a
      pr₂pr₂proof≡pr₂a = 
        pr₂ ⨾ (pr₂ ⨾ proof)
          ≡⟨ cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) proof≡pair⨾true⨾pair⨾true⨾pr₂a ⟩
        pr₂ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))))
          ≡⟨ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ⟩
        pr₂ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))
          ≡⟨ pr₂pxy≡y _ _ ⟩
        pr₂ ⨾ a
          ∎

    module Pr₁a≡false
      (a : A)
      (pr₁a≡false : pr₁ ⨾ a ≡ false) where
      private proof = →prover ⨾ a
      proof≡y⊔z : proof ≡ (Id ⨾
                    (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
                    (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
                    (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
      proof≡y⊔z =
        proof
          ≡⟨ λ*ComputationRule →proverTerm (a ∷ []) ⟩
        (Id ⨾
         (pr₁ ⨾ a) ⨾
         (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
         (Id ⨾
           (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
           (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
           (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
           ≡⟨  cong (λ x →
                     (Id ⨾
                       x ⨾
                       (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
                       (Id ⨾
                         (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
                         (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
                         (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))))
                pr₁a≡false ⟩
         (Id ⨾
           k' ⨾
           (pair ⨾ true ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ a))) ⨾
           (Id ⨾
             (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
             (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
             (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
            ≡⟨ ifFalseElse _ _ ⟩
         (Id ⨾
             (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
             (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
             (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
            ∎

      module _ (pr₁pr₂a≡true : pr₁ ⨾ (pr₂ ⨾ a) ≡ true) where
        proof≡pair⨾true⨾pair⨾false⨾pr₂⨾pr₂⨾a : proof ≡ pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
        proof≡pair⨾true⨾pair⨾false⨾pr₂⨾pr₂⨾a =
          proof
            ≡⟨ proof≡y⊔z ⟩
          Id ⨾
              (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
              (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
              (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ cong
               (λ x → (Id ⨾
                        x ⨾
                        (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
                        (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
               pr₁pr₂a≡true ⟩
          Id ⨾ true ⨾ (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
            (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ ifTrueThen _ _ ⟩
          (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
            ∎
        
        pr₁proof≡true : pr₁ ⨾ proof ≡ true
        pr₁proof≡true =
          pr₁ ⨾ proof
            ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair⨾true⨾pair⨾false⨾pr₂⨾pr₂⨾a ⟩
         pr₁ ⨾ (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
            ≡⟨ pr₁pxy≡x _ _ ⟩
         true
            ∎

        pr₁pr₂proof≡k' : pr₁ ⨾ (pr₂ ⨾ proof) ≡ k'
        pr₁pr₂proof≡k' =
          pr₁ ⨾ (pr₂ ⨾ proof)
            ≡⟨ cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) proof≡pair⨾true⨾pair⨾false⨾pr₂⨾pr₂⨾a ⟩
          pr₁ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
            ≡⟨ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ⟩
          pr₁ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ pr₁pxy≡x _ _ ⟩
          false
            ∎

        
        pr₂pr₂proof≡pr₂pr₂a : pr₂ ⨾ (pr₂ ⨾ proof) ≡ pr₂ ⨾ (pr₂ ⨾ a)
        pr₂pr₂proof≡pr₂pr₂a =
          pr₂ ⨾ (pr₂ ⨾ proof)
            ≡⟨ cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) proof≡pair⨾true⨾pair⨾false⨾pr₂⨾pr₂⨾a ⟩
          pr₂ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
            ≡⟨ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ⟩
          pr₂ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ pr₂pxy≡y _ _ ⟩
          pr₂ ⨾ (pr₂ ⨾ a)
            ∎

      module _ (pr₁pr₂a≡false : pr₁ ⨾ (pr₂ ⨾ a) ≡ false) where

        proof≡pair⨾false⨾pr₂pr₂a : proof ≡ pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))
        proof≡pair⨾false⨾pr₂pr₂a =
          proof
            ≡⟨ proof≡y⊔z ⟩
          Id ⨾
            (pr₁ ⨾ (pr₂ ⨾ a)) ⨾
            (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
            (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ cong
               (λ x →
                 Id ⨾
                 x ⨾
                 (pair ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))) ⨾
                 (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                 pr₁pr₂a≡false ⟩
          ifFalseElse _ _

        pr₁proof≡false : pr₁ ⨾ proof ≡ false
        pr₁proof≡false =
          pr₁ ⨾ proof
            ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair⨾false⨾pr₂pr₂a ⟩
          pr₁ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ pr₁pxy≡x _ _ ⟩
          false
            ∎

        pr₂proof≡pr₂pr₂a : pr₂ ⨾ proof ≡ pr₂ ⨾ (pr₂ ⨾ a)
        pr₂proof≡pr₂pr₂a =
          pr₂ ⨾ proof
            ≡⟨ cong (λ x → pr₂ ⨾ x) proof≡pair⨾false⨾pr₂pr₂a ⟩
          pr₂ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
            ≡⟨ pr₂pxy≡y _ _ ⟩
          pr₂ ⨾ (pr₂ ⨾ a)
            ∎
            

  x⊔_y⊔z≤x⊔y_⊔z : ∀ x y z → (x ⊔ (y ⊔ z)) ≤ ((x ⊔ y) ⊔ z)
  x⊔_y⊔z≤x⊔y_⊔z x y z =
    (do
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
              (` pair ̇ ` true ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero)))) ̇
              (` pair ̇ ` false ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))))
      return
        (λ* prover ,
          λ x' a a⊩x⊔_y⊔z →
            transport
              (propTruncIdempotent (((x ⊔ y) ⊔ z) .isPropValued x' (λ* prover ⨾ a)))
              (a⊩x⊔_y⊔z
                >>= (λ { (inl (pr₁a≡true , pr₁a⊩x))
                     → ∣ ∣ inl
                           (Pr₁a≡true.pr₁⨾proof≡true a pr₁a≡true ,
                           transport
                             (propTruncIdempotent isPropPropTrunc)
                             ∣ a⊩x⊔_y⊔z
                               >>= (λ { (inl (pr₁a≡k , pr₂a⊩x)) →
                                         ∣ inl
                                           (Pr₁a≡true.pr₁pr₂proof≡true a pr₁a≡true ,
                                            subst
                                              (λ r → r ⊩ ∣ x ∣ x')
                                              (sym (Pr₁a≡true.pr₂pr₂proof≡pr₂a a pr₁a≡true))
                                              pr₂a⊩x) ∣₁
                                      ; (inr (pr₁a≡k' , pr₂a⊩y⊔z)) → ⊥rec (Trivial.k≠k' ca isNonTrivial (k ≡⟨ sym pr₁a≡true ⟩ pr₁ ⨾ a ≡⟨ pr₁a≡k' ⟩ k' ∎)) }) ∣₁) ∣₁ ∣₁
                       ; (inr (pr₁a≡false , pr₂a⊩y⊔z))
                     → ∣ pr₂a⊩y⊔z >>=
                       (λ { (inl (pr₁pr₂a≡k  , pr₂pr₂a⊩y)) →
                            ∣ inl (Pr₁a≡false.pr₁proof≡true a pr₁a≡false pr₁pr₂a≡k ,
                              ∣ inr
                              (Pr₁a≡false.pr₁pr₂proof≡k' a pr₁a≡false pr₁pr₂a≡k ,
                              subst
                                (λ r → r ⊩ ∣ y ∣ x')
                                (sym (Pr₁a≡false.pr₂pr₂proof≡pr₂pr₂a a pr₁a≡false pr₁pr₂a≡k))
                                pr₂pr₂a⊩y) ∣₁) ∣₁
                          ; (inr (pr₁pr₂a≡k' , pr₂pr₂a⊩z)) →
                            ∣ inr (
                              Pr₁a≡false.pr₁proof≡false a pr₁a≡false pr₁pr₂a≡k' ,
                              subst
                                (λ r → r ⊩ ∣ z ∣ x')
                                (sym (Pr₁a≡false.pr₂proof≡pr₂pr₂a a pr₁a≡false pr₁pr₂a≡k'))
                                pr₂pr₂a⊩z) ∣₁ }) ∣₁
                                })))) where open →⊔Assoc x y z

  `if_then_else_ : ∀ {n} → Term as n → Term as n → Term as n → Term as n
  `if c then t else e = ` Id ̇ c ̇ t ̇ e

  x⊔y_⊔z≤x⊔_y⊔z : ∀ x y z → (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
  x⊔y_⊔z≤x⊔_y⊔z x y z =
    do
      let
        proof : Term as 1
        proof =
          `if ` pr₁ ̇ # fzero then
            `if ` pr₁ ̇ (` pr₂ ̇ (# fzero)) then
              ` pair ̇ ` true  ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))
            else
              (` pair ̇ ` false ̇ (` pair ̇ ` true ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero))))
          else
            (` pair ̇ ` false ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ # fzero)))
      return
        (λ* proof ,
          (λ x' a a⊩x⊔y_⊔z →
            a⊩x⊔y_⊔z >>=
              let
                mainThen =
                  if (pr₁ ⨾ (pr₂ ⨾ a)) then
                    (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                  else
                    (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))

                mainElse =
                  (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
              in
              λ { (inl (pr₁a≡k , pr₂a⊩x⊔y)) →
                           
                           let
                             proofEq :
                               (λ* proof ⨾ a) ≡ if (pr₁ ⨾ (pr₂ ⨾ a)) then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                             proofEq =
                               λ* proof ⨾ a
                                 ≡⟨ λ*ComputationRule proof (a ∷ []) ⟩
                               if (pr₁ ⨾ a) then
                                 if (pr₁ ⨾ (pr₂ ⨾ a)) then
                                   (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                 else
                                   (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                               else
                                 (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ≡⟨ cong (λ x → if x then mainThen else mainElse) pr₁a≡k ⟩
                               if true then
                                 if (pr₁ ⨾ (pr₂ ⨾ a)) then
                                   (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                 else
                                   (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                               else
                                 (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ≡⟨ ifTrueThen _ _ ⟩
                               refl
                           in
                           pr₂a⊩x⊔y >>=
                             λ { (inl (pr₁pr₂a≡k , pr₂pr₂a⊩x)) →
                               let
                                 proof≡pair : λ* proof ⨾ a ≡ pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))
                                 proof≡pair =
                                   λ* proof ⨾ a
                                     ≡⟨ proofEq ⟩
                                   (if (pr₁ ⨾ (pr₂ ⨾ a)) then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ cong (λ x → if x then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))) pr₁pr₂a≡k ⟩
                                   (if true then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ ifTrueThen _ _ ⟩
                                   pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))
                                     ∎
                                 
                                 pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ k
                                 pr₁proofEq =
                                   pr₁ ⨾ (λ* proof ⨾ a)
                                     ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair ⟩
                                   pr₁ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                     ≡⟨ pr₁pxy≡x _ _ ⟩
                                   true
                                     ∎

                                 pr₂proofEq : pr₂ ⨾ (λ* proof ⨾ a) ≡ pr₂ ⨾ (pr₂ ⨾ a)
                                 pr₂proofEq =
                                   pr₂ ⨾ (λ* proof ⨾ a)
                                     ≡⟨ cong (λ x → pr₂ ⨾ x) proof≡pair ⟩
                                   pr₂ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                     ≡⟨ pr₂pxy≡y _ _ ⟩
                                   pr₂ ⨾ (pr₂ ⨾ a)
                                     ∎
                               in ∣ inl (pr₁proofEq , subst (λ r → r ⊩ ∣ x ∣ x') (sym pr₂proofEq) pr₂pr₂a⊩x) ∣₁
                               ; (inr (pr₁pr₂a≡k' , pr₂pr₂a⊩y)) →
                               let
                                 proof≡pair : λ* proof ⨾ a ≡ pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                 proof≡pair =
                                   λ* proof ⨾ a
                                     ≡⟨ proofEq ⟩
                                   (if (pr₁ ⨾ (pr₂ ⨾ a)) then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ cong (λ x → if x then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))) pr₁pr₂a≡k' ⟩
                                   (if false then (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))) else (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ ifFalseElse _ _ ⟩
                                   pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                     ∎

                                 pr₁proofEq : pr₁ ⨾ (λ* proof ⨾ a) ≡ k'
                                 pr₁proofEq =
                                   pr₁ ⨾ (λ* proof ⨾ a)
                                     ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair ⟩
                                   pr₁ ⨾ (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                                     ≡⟨ pr₁pxy≡x _ _ ⟩
                                   false
                                     ∎

                                 pr₁pr₂proofEq : pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ true
                                 pr₁pr₂proofEq =
                                   pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                                     ≡⟨ cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) proof≡pair ⟩
                                   pr₁ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ⟩
                                   pr₁ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                     ≡⟨ pr₁pxy≡x _ _ ⟩
                                   true
                                     ∎

                                 pr₂pr₂proofEq : pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ pr₂ ⨾ (pr₂ ⨾ a)
                                 pr₂pr₂proofEq =
                                   pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                                     ≡⟨ cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) proof≡pair ⟩
                                   pr₂ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))))
                                     ≡⟨ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ⟩
                                   pr₂ ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                     ≡⟨ pr₂pxy≡y _ _ ⟩
                                   pr₂ ⨾ (pr₂ ⨾ a)
                                     ∎
                               in ∣ inr (pr₁proofEq , ∣ inl (pr₁pr₂proofEq , subst (λ r → r ⊩ ∣ y ∣ x') (sym pr₂pr₂proofEq) pr₂pr₂a⊩y) ∣₁) ∣₁ }
                           ; (inr (pr₁a≡k' , pr₂a⊩z)) →
                           let
                             proof≡pair : λ* proof ⨾ a ≡ pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a))
                             proof≡pair =
                               λ* proof ⨾ a
                                 ≡⟨ λ*ComputationRule proof (a ∷ []) ⟩
                               if (pr₁ ⨾ a) then
                                 if (pr₁ ⨾ (pr₂ ⨾ a)) then
                                   (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                 else
                                   (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                               else
                                 (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ≡⟨ cong (λ x → if x then mainThen else mainElse) pr₁a≡k' ⟩
                               if false then
                                 if (pr₁ ⨾ (pr₂ ⨾ a)) then
                                   (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a)))
                                 else
                                   (pair ⨾ false ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pr₂ ⨾ a))))
                               else
                                 (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ≡⟨ ifFalseElse _ _ ⟩
                               (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ∎

                             pr₁proof≡false : pr₁ ⨾ (λ* proof ⨾ a) ≡ false
                             pr₁proof≡false =
                               pr₁ ⨾ (λ* proof ⨾ a)
                                 ≡⟨ cong (λ x → pr₁ ⨾ x) proof≡pair ⟩
                               pr₁ ⨾ (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a)))
                                 ≡⟨ pr₁pxy≡x _ _ ⟩
                               false
                                 ∎

                             pr₂proof≡pair : pr₂ ⨾ (λ* proof ⨾ a) ≡ (pair ⨾ false ⨾ (pr₂ ⨾ a))
                             pr₂proof≡pair =
                               (pr₂ ⨾ (λ* proof ⨾ a))
                                 ≡⟨ cong (λ x → (pr₂ ⨾ x)) proof≡pair ⟩
                               (pr₂ ⨾ (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a))))
                                 ≡⟨ (pr₂pxy≡y _ _) ⟩
                               (pair ⨾ false ⨾ (pr₂ ⨾ a))
                                 ∎

                             pr₁pr₂proof≡false : pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ false
                             pr₁pr₂proof≡false =
                               pr₁ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                                 ≡⟨ cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) proof≡pair ⟩
                               pr₁ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a))))
                                 ≡⟨ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ⟩
                               pr₁ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a))
                                 ≡⟨ pr₁pxy≡x _ _ ⟩
                               false
                                 ∎

                             pr₂pr₂proof≡pr₂a : pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a)) ≡ pr₂ ⨾ a
                             pr₂pr₂proof≡pr₂a =
                               pr₂ ⨾ (pr₂ ⨾ (λ* proof ⨾ a))
                                 ≡⟨ cong (λ x → pr₂ ⨾ x ) pr₂proof≡pair ⟩
                               pr₂ ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ a))
                                 ≡⟨ pr₂pxy≡y _ _ ⟩
                               pr₂ ⨾ a
                                 ∎
                           in ∣ inr (pr₁proof≡false , ∣ inr (pr₁pr₂proof≡false , subst (λ r → r ⊩ ∣ z ∣ x') (sym pr₂pr₂proof≡pr₂a) pr₂a⊩z) ∣₁) ∣₁ } ))
