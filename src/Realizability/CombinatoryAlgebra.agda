{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Nat

open import Realizability.ApplicativeStructure hiding (S;K)

module Realizability.CombinatoryAlgebra where

record CombinatoryAlgebra {ℓ} (A : Type ℓ) : Type ℓ where
  field
    as : ApplicativeStructure A
    completeness : isCombinatoriallyComplete as
  fefermanStructure : Feferman as
  fefermanStructure = completeness→feferman as completeness
  open Feferman fefermanStructure public
  open ApplicativeStructure as public

module Combinators {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  open CombinatoryAlgebra ca
  
  i : A
  i = s ⨾ k ⨾ k

  k' : A
  k' = k ⨾ i

  ia≡a : ∀ a → i ⨾ a ≡ a
  ia≡a a = (cong (λ x → x ⨾ a) refl) ∙ (sabc≡ac_bc k k a) ∙ (kab≡a a (k ⨾ a))

  k'ab≡b : ∀ a b → k' ⨾ a ⨾ b ≡ b
  k'ab≡b a b = k' ⨾ a ⨾ b
                  ≡⟨ refl ⟩
                (k ⨾ i ⨾ a ⨾ b)
                  ≡⟨ cong (λ x → x ⨾ b) (kab≡a i a) ⟩
                (i ⨾ b)
                  ≡⟨ ia≡a b ⟩
                b
                  ∎

  true : A
  true = k

  false : A
  false = k'

  if_then_else_ : ∀ c t e → A
  if c then t else e = i ⨾ c ⨾ t ⨾ e

  ifTrueThen : ∀ t e → if true then t else e ≡ t
  ifTrueThen t e =  if true then t else e
                      ≡⟨ refl ⟩
                    i ⨾ true ⨾ t ⨾ e
                      ≡⟨ cong (λ x → i ⨾ x ⨾ t ⨾ e) refl ⟩
                    i ⨾ k ⨾ t ⨾ e
                      ≡⟨ cong (λ x → x ⨾ t ⨾ e) (ia≡a k) ⟩
                    k ⨾ t ⨾ e
                      ≡⟨ kab≡a t e ⟩
                    t
                      ∎

  ifFalseElse : ∀ t e → if false then t else e ≡ e
  ifFalseElse t e =  if false then t else e
                        ≡⟨ refl ⟩
                     i ⨾ false ⨾ t ⨾ e
                        ≡⟨ cong (λ x → i ⨾ x ⨾ t ⨾ e) refl ⟩
                     i ⨾ k' ⨾ t ⨾ e
                        ≡⟨ cong (λ x → x ⨾ t ⨾ e) (ia≡a k') ⟩
                     k' ⨾ t ⨾ e
                        ≡⟨ k'ab≡b t e ⟩
                     e
                        ∎

  -- I used a Scheme script to generate this
  pair : A
  pair = s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (s)))) ⨾
         (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (s)))) ⨾
         (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (s)))) ⨾
         (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (k))))) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (k)))))) ⨾ (s ⨾
         (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (k)))) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (s ⨾ (k) ⨾ (k))))))) ⨾
         (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (s ⨾ (k ⨾ (k)) ⨾ (k ⨾ (k)))) ⨾ (s ⨾ (s ⨾ (k ⨾ (s)) ⨾ (k ⨾ (k))) ⨾ (k ⨾ (k))))

  pr₁ : A
  pr₁ = s ⨾ (s ⨾ k ⨾ k) ⨾ (k ⨾ k)

  pr₂ : A
  pr₂ = s ⨾ (s ⨾ k ⨾ k) ⨾ (k ⨾ k')

  -- TODO : Prove computation rules
  postulate pr₁pxy≡x : ∀ x y → pr₁ ⨾ (pair ⨾ x ⨾ y) ≡ x
  postulate pr₂pxy≡y : ∀ x y → pr₂ ⨾ (pair ⨾ x ⨾ y) ≡ y

  -- Curry numbers
  ℕ→curry : ℕ → A
  ℕ→curry zero = i
  ℕ→curry (suc n) = pair ⨾ k' ⨾ (ℕ→curry n)

  Z : A
  Z = pr₁

  Zzero≡true : Z ⨾ (ℕ→curry zero) ≡ true
  Zzero≡true = Z ⨾ (ℕ→curry zero)
                 ≡⟨ cong (λ x → Z ⨾ x) refl ⟩
               Z ⨾ i
                 ≡⟨ cong (λ x → x ⨾ i) refl ⟩
               s ⨾ (s ⨾ k ⨾ k) ⨾ (k ⨾ k) ⨾ i
                 ≡⟨ sabc≡ac_bc (s ⨾ k ⨾ k) (k ⨾ k) i ⟩
               ((s ⨾ k ⨾ k) ⨾ i) ⨾ (k ⨾ k ⨾ i)
                 ≡⟨ cong (λ x → (x ⨾ i) ⨾ (k ⨾ k ⨾ i)) refl ⟩
               (i ⨾ i) ⨾ (k ⨾ k ⨾ i)
                 ≡⟨ cong (λ x → x ⨾ (k ⨾ k ⨾ i)) (ia≡a i) ⟩
               i ⨾ (k ⨾ k ⨾ i)
                 ≡⟨ cong (λ x → i ⨾ x) (kab≡a k i) ⟩
               i ⨾ k
                 ≡⟨ ia≡a k ⟩
               k
                 ∎

  Zsuc≡false : ∀ n → Z ⨾ (ℕ→curry (suc n)) ≡ false
  Zsuc≡false n = Z ⨾ (ℕ→curry (suc n))
                   ≡⟨ cong (λ x → Z ⨾ x) refl ⟩
                 Z ⨾ (pair ⨾ k' ⨾ (ℕ→curry n))
                   ≡⟨ cong (λ x → x ⨾ (pair ⨾ k' ⨾ (ℕ→curry n))) refl ⟩
                 pr₁ ⨾ (pair ⨾ k' ⨾ (ℕ→curry n))
                   ≡⟨ pr₁pxy≡x k' (ℕ→curry n) ⟩
                 false
                   ∎

  S : A
  S = pair ⨾ k'

  Sn≡sucn : ∀ n → S ⨾ (ℕ→curry n) ≡ ℕ→curry (suc n)
  Sn≡sucn n = S ⨾ (ℕ→curry n)
                ≡⟨ cong (λ x → x ⨾ (ℕ→curry n)) refl ⟩
              pair ⨾ k' ⨾ (ℕ→curry n)
                ∎

  P : A
  P = s ⨾ (s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ i) ⨾ (k ⨾ (ℕ→curry zero))) ⨾ (s ⨾ (k ⨾ (pr₂)) ⨾ i)

  postulate Pzero≡zero : P ⨾ (ℕ→curry zero) ≡ ℕ→curry zero
  postulate Psucn≡n : ∀ n → P ⨾ (ℕ→curry (suc n)) ≡ ℕ→curry n

  B : ∀ g f → A
  B g f = s ⨾ (k ⨾ g) ⨾ (s ⨾ (k ⨾ f) ⨾ i)

  Ba≡gfa : ∀ g f a → B g f ⨾ a ≡ g ⨾ (f ⨾ a)
  Ba≡gfa g f a =
               s ⨾ (k ⨾ g) ⨾ (s ⨾ (k ⨾ f) ⨾ i) ⨾ a
                 ≡⟨ sabc≡ac_bc (k ⨾ g) (s ⨾ (k ⨾ f) ⨾ i) a ⟩
               (k ⨾ g ⨾ a) ⨾ (s ⨾ (k ⨾ f) ⨾ i ⨾ a)
                 ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ f) ⨾ i ⨾ a)) (kab≡a g a) ⟩
               g ⨾ (s ⨾ (k ⨾ f) ⨾ i ⨾ a)
                 ≡⟨ cong (λ x → g ⨾ x) (sabc≡ac_bc (k ⨾ f) i a) ⟩
               g ⨾ ((k ⨾ f ⨾ a) ⨾ (i ⨾ a))
                 ≡⟨ cong (λ x → g ⨾ (x ⨾ (i ⨾ a))) (kab≡a f a) ⟩
               g ⨾ (f ⨾ (i ⨾ a))
                 ≡⟨ cong (λ x → g ⨾ (f ⨾ x)) (ia≡a a) ⟩
               g ⨾ (f ⨾ a)
                 ∎


module Trivial {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  open CombinatoryAlgebra ca
  open Combinators ca
  module _ (isNonTrivial : s ≡ k → ⊥) where

    k≠k' : k ≡ k' → ⊥
    k≠k' k≡k' = isNonTrivial s≡k where
      cond = if true then s else k
      cond' = if false then s else k
      condEq : cond ≡ cond'
      condEq = cong (λ x → if x then s else k) k≡k'
  
      cond≡s : cond ≡ s
      cond≡s = ifTrueThen _ _

      cond'≡k : cond' ≡ k
      cond'≡k = ifFalseElse _ _

      cond≡k : cond ≡ k
      cond≡k = subst (λ x → x ≡ k) (sym condEq) cond'≡k

      s≡k : s ≡ k
      s≡k =
        s
          ≡⟨ sym cond≡s ⟩
        cond
          ≡⟨ cond≡k ⟩
        k
          ∎
        

