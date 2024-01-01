open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin
module Experiments.LCNDChoice where

data Term (n : ℕ) : Type where
  var : Fin n → Term n
  abs : Term (suc n) → Term n
  appl : Term n → Term n → Term n
  _⊕_ : Term n → Term n → Term n

infixr 5 _∷_
data FiniteSet {ℓ} (A : Type ℓ) : Type ℓ where
  [] : FiniteSet A
  _∷_ : A → FiniteSet A → FiniteSet A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  idem : ∀ x xs → x ∷ (x ∷ xs) ≡ x ∷ xs
  trunc : isSet (FiniteSet A)

singleton : ∀ {ℓ} {A : Type ℓ} → A → FiniteSet A
singleton a = a ∷ []

-- Sanity Check
_．_ : ∀ {n : ℕ} → Term n → Term n → FiniteSet (Term n)
var x ． var y = appl (var x) (var y) ∷ []
var x ． abs y = appl (var x) (abs y) ∷ []
var x ． appl y y₁ = singleton (appl (var x) (appl y y₁))
var x ． (y ⊕ y₁) = appl (var x) y ∷ appl (var x) y₁ ∷ []
abs x ． var x₁ = singleton (appl (abs x) (var x₁))
abs x ． abs y = {!singleton (appl !}
abs x ． appl y y₁ = {!!}
abs x ． (y ⊕ y₁) = {!!}
appl x x₁ ． y = {!!}
(x ⊕ x₁) ． y = {!!}

