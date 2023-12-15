open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary.Order

module Realizability.Tripos.Predicate {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

record Predicate {ℓ' ℓ''} (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
    ∣_∣ : X → A → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isPropValued : ∀ x a → isProp (∣_∣ x a)

open Predicate
_⊩_ : ∀ {ℓ'} → A → (A → Type ℓ') → Type ℓ'
a ⊩ ϕ = ϕ a

PredicateΣ : ∀ {ℓ' ℓ''} → (X : Type ℓ') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
PredicateΣ {ℓ'} {ℓ''} X = Σ[ isSetX ∈ isSet X ] (X → A → hProp (ℓ-max (ℓ-max ℓ ℓ') ℓ''))

isSetPredicateΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (PredicateΣ {ℓ'' = ℓ''} X)
isSetPredicateΣ X = isSetΣ (isProp→isSet isPropIsSet) λ isSetX → isSetΠ λ x → isSetΠ λ a → isSetHProp

PredicateIsoΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Iso (Predicate {ℓ'' = ℓ''} X) (PredicateΣ {ℓ'' = ℓ''} X)
PredicateIsoΣ {ℓ'} {ℓ''} X =
  iso
    (λ p → p .isSetX , λ x a → ∣ p ∣ x a , p .isPropValued x a)
    (λ p → record { isSetX = p .fst ; ∣_∣ = λ x a → p .snd x a .fst ; isPropValued = λ x a → p .snd x a .snd })
    (λ b → refl)
    λ a → refl

Predicate≡Σ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Predicate {ℓ'' = ℓ''} X ≡ PredicateΣ {ℓ'' = ℓ''} X
Predicate≡Σ {ℓ'} {ℓ''} X = isoToPath (PredicateIsoΣ X)

isSetPredicate : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (Predicate {ℓ'' = ℓ''} X)
isSetPredicate {ℓ'} {ℓ''} X = subst (λ predicateType → isSet predicateType) (sym (Predicate≡Σ X)) (isSetPredicateΣ {ℓ'' = ℓ''} X)

module PredicateProperties {ℓ' ℓ''} (X : Type ℓ') where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  _≤_ : Predicate {ℓ'' = ℓ''} X → Predicate {ℓ'' = ℓ''} X → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  ϕ ≤ ψ = ∃[ b ∈ A ] (∀ (x : X) (a : A) → a ⊩ (∣ ϕ ∣ x) → (b ⨾ a) ⊩ ∣ ψ ∣ x)

  isProp≤ : ∀ ϕ ψ → isProp (ϕ ≤ ψ)
  isProp≤ ϕ ψ = isPropPropTrunc

  isRefl≤ : ∀ ϕ → ϕ ≤ ϕ
  isRefl≤ ϕ = ∣ Id , (λ x a a⊩ϕx → subst (λ r → r ⊩ ∣ ϕ ∣ x) (sym (Ida≡a a)) a⊩ϕx) ∣₁

  isTrans≤ : ∀ ϕ ψ ξ → ϕ ≤ ψ → ψ ≤ ξ → ϕ ≤ ξ
  isTrans≤ ϕ ψ ξ ϕ≤ψ ψ≤ξ = do
                           (a , ϕ≤[a]ψ) ← ϕ≤ψ
                           (b , ψ≤[b]ξ) ← ψ≤ξ
                           return ((B b a) , (λ x a' a'⊩ϕx → subst (λ r → r ⊩ ∣ ξ ∣ x) (sym (Ba≡gfa b a a')) (ψ≤[b]ξ x (a ⨾ a') (ϕ≤[a]ψ x a' a'⊩ϕx))))
    

  open IsPreorder renaming (is-set to isSet; is-prop-valued to isPropValued; is-refl to isRefl; is-trans to isTrans)

  preorder≤ : _
  preorder≤ = preorder (Predicate X) _≤_ (ispreorder (isSetPredicate X) isProp≤ isRefl≤ isTrans≤)

  infix 25 _⊔_
  _⊔_ : PredicateX → PredicateX → PredicateX
  (ϕ ⊔ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⊔ ψ ∣ x a = ∥ ((pair ⨾ k ⨾ a) ⊩ ∣ ϕ ∣ x) ⊎ ((pair ⨾ k' ⨾ a) ⊩ ∣ ψ ∣ x) ∥₁
  (ϕ ⊔ ψ) .isPropValued x a = isPropPropTrunc

  infix 25 _⊓_
  _⊓_ : PredicateX → PredicateX → PredicateX
  (ϕ ⊓ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⊓ ψ ∣ x a = ((pr₁ ⨾ a) ⊩ ∣ ϕ ∣ x) × ((pr₂ ⨾ a) ⊩ ∣ ψ ∣ x)
  (ϕ ⊓ ψ) .isPropValued x a = isProp× (ϕ .isPropValued x (pr₁ ⨾ a)) (ψ .isPropValued x (pr₂ ⨾ a))

  infix 25 _⇒_
  _⇒_ : PredicateX → PredicateX → PredicateX
  (ϕ ⇒ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⇒ ψ ∣ x a = ∀ b → (b ⊩ ∣ ϕ ∣ x) → (a ⨾ b) ⊩ ∣ ψ ∣ x
  (ϕ ⇒ ψ) .isPropValued x a = isPropΠ λ a → isPropΠ λ a⊩ϕx → ψ .isPropValued _ _

module Morphism {ℓ' ℓ''} {X Y : Type ℓ'} (isSetX : isSet X) (isSetY : isSet Y)  where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  PredicateY = Predicate {ℓ'' = ℓ''} Y

  _⋆ : (X → Y) → (PredicateY → PredicateX)
  f ⋆ = λ ϕ → record { isSetX = isSetX ; ∣_∣ = λ x a → a ⊩ ∣ ϕ ∣ (f x) ; isPropValued = λ x a → ϕ .isPropValued (f x) a }

  `∀_ : (X → Y) → (PredicateX → PredicateY)
  `∀ f = λ ϕ → record { isSetX = isSetY ; ∣_∣ = λ y a → (∀ b x → f x ≡ y → (a ⨾ b) ⊩ ∣ ϕ ∣ x) ; isPropValued = λ y a → isPropΠ λ a' → isPropΠ λ x → isPropΠ λ fx≡y → ϕ .isPropValued x (a ⨾ a') }

  `∃_ : (X → Y) → (PredicateX → PredicateY)
  `∃ f = λ ϕ → record { isSetX = isSetY ; ∣_∣ = λ y a → ∃[ x ∈ X ] (f x ≡ y) × (a ⊩ ∣ ϕ ∣ x) ; isPropValued = λ y a → isPropPropTrunc }
