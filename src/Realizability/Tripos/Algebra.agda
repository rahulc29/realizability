open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Fin
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad

module Realizability.Tripos.Algebra {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where
open import Realizability.Tripos.Predicate ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca

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

  ⊔idempotent→ : ∀ x ϕ a → a ⊩ ∣ ϕ ⊔ ϕ ∣ x → a ⊩ ∣ ϕ ∣ x
  ⊔idempotent→ x ϕ a a⊩ϕ⊔ϕ =
    equivFun (propTruncIdempotent≃ (ϕ .isPropValued x a))
      (a⊩ϕ⊔ϕ >>= λ { (inl la⊩ϕx) → {!!} ; (inr ra⊩ϕx) → {!!} })

  ⊔idempotent : ∀ a → a ⊔ a ≡ a
  ⊔idempotent a i =
    PredicateIsoΣ X .inv
      (PredicateΣ≡ {ℓ'' = ℓ''} X
        ((λ x a' → (a' ⊩ ∣ a ⊔ a ∣ x) , (a ⊔ a) .isPropValued x a') , ((a ⊔ a) .isSetX))
        ((λ x a' → (a' ⊩ ∣ a ∣ x) , (a .isPropValued x a')) , (a .isSetX))
      (funExt₂ (λ x a' → Σ≡Prop (λ x → isPropIsProp {A = x}) (hPropExt isPropPropTrunc (a .isPropValued x a') (⊔idempotent→ x a a') {!!})))
      i)
