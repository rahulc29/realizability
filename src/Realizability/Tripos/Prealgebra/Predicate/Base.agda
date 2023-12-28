open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure renaming (⟦_⟧ to `⟦_⟧; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv

module Realizability.Tripos.Prealgebra.Predicate.Base {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

record Predicate {ℓ' ℓ''} (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
    ∣_∣ : X → A → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isPropValued : ∀ x a → isProp (∣_∣ x a)
  infix 25 ∣_∣

open Predicate
infix 26 _⊩_
_⊩_ : ∀ {ℓ'} → A → (A → Type ℓ') → Type ℓ'
a ⊩ ϕ = ϕ a

PredicateΣ : ∀ {ℓ' ℓ''} → (X : Type ℓ') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
PredicateΣ {ℓ'} {ℓ''} X = Σ[ rel ∈ (X → A → hProp (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) ] (isSet X)

isSetPredicateΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (PredicateΣ {ℓ'' = ℓ''} X)
isSetPredicateΣ X = isSetΣ (isSetΠ (λ x → isSetΠ λ a → isSetHProp)) λ _ → isProp→isSet isPropIsSet

PredicateIsoΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Iso (Predicate {ℓ'' = ℓ''} X) (PredicateΣ {ℓ'' = ℓ''} X)
PredicateIsoΣ {ℓ'} {ℓ''} X =
  iso
    (λ p → (λ x a → (a ⊩ ∣ p ∣ x) , p .isPropValued x a) , p .isSetX)
    (λ p → record { isSetX = p .snd ; ∣_∣ = λ x a → p .fst x a .fst ; isPropValued = λ x a → p .fst x a .snd })
    (λ b → refl)
    λ a → refl

Predicate≡PredicateΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Predicate {ℓ'' = ℓ''} X ≡ PredicateΣ {ℓ'' = ℓ''} X
Predicate≡PredicateΣ {ℓ'} {ℓ''} X = isoToPath (PredicateIsoΣ X)

isSetPredicate : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (Predicate {ℓ'' = ℓ''} X)
isSetPredicate {ℓ'} {ℓ''} X = subst (λ predicateType → isSet predicateType) (sym (Predicate≡PredicateΣ X)) (isSetPredicateΣ {ℓ'' = ℓ''} X)

PredicateΣ≡ : ∀ {ℓ' ℓ''} (X : Type ℓ') → (P Q : PredicateΣ {ℓ'' = ℓ''} X) → (P .fst ≡ Q .fst) → P ≡ Q
PredicateΣ≡ X P Q ∣P∣≡∣Q∣ = Σ≡Prop (λ _ → isPropIsSet) ∣P∣≡∣Q∣

Predicate≡ :
  ∀ {ℓ' ℓ''} (X : Type ℓ')
  → (P Q : Predicate {ℓ'' = ℓ''} X)
  → (∀ x a → a ⊩ ∣ P ∣ x → a ⊩ ∣ Q ∣ x)
  → (∀ x a → a ⊩ ∣ Q ∣ x → a ⊩ ∣ P ∣ x)
  -----------------------------------
  → P ≡ Q
Predicate≡ {ℓ'} {ℓ''} X P Q P→Q Q→P i =
  PredicateIsoΣ X .inv
    (PredicateΣ≡
      {ℓ'' = ℓ''}
      X
      (PredicateIsoΣ X .fun P)
      (PredicateIsoΣ X .fun Q)
      (funExt₂
        (λ x a → Σ≡Prop (λ A → isPropIsProp)
        (hPropExt
          (P .isPropValued x a)
          (Q .isPropValued x a)
          (P→Q x a)
          (Q→P x a)))) i) where open Iso
