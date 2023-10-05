{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP

module Realizability.Partiality {𝓢} where

infix 20 ♯_

record ♯_ {ℓ} (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
  field
    support : Type 𝓢
    isProp-support : isProp support
    force : support → A

open ♯_

return : ∀ {ℓ} {A : Type ℓ} → A → ♯ A
return a .support = Unit*
return a .isProp-support = isPropUnit*
return a .force _ = a

infixl 21 _>>=_
_>>=_ : ∀ {ℓ} {A B : Type ℓ} → ♯ A → (A → ♯ B) → ♯ B
(♯a >>= f) .support = Σ[ s ∈ (♯a .support) ] ((f (♯a .force s)) .support)
(♯a >>= f) .isProp-support =  isPropΣ (♯a .isProp-support) λ x → f (♯a .force x) .isProp-support
(♯a >>= f) .force (s , s') = f (♯a .force s) .force s' 

map-♯ : ∀ {ℓ} {A B : Type ℓ} → (A → B) → (♯ A → ♯ B)
map-♯ f ♯a .support = ♯a .support
map-♯ f ♯a .isProp-support = ♯a .isProp-support
map-♯ f ♯a .force s = f (♯a .force s)

-- Goofy ahh universe necessary
-- for Agda to check
join : ∀ {ℓ} {A : Type (ℓ-max ℓ (ℓ-suc 𝓢))} → ♯ ♯ A → ♯ A
join {ℓ} {A} ♯♯a = ♯♯a >>= (idfun (♯ A))

♯-id : ∀ {ℓ} {A : Type ℓ} → map-♯ (idfun A) ≡ (idfun (♯ A))
♯-id = refl

♯-∘ : ∀ {ℓ} {A B C : Type ℓ} → (f : A → B) → (g : B → C) → map-♯ (g ∘ f) ≡ map-♯ g ∘ map-♯ f
♯-∘ f g = refl

infixl 21 _>=>_
_>=>_ : ∀ {ℓ} {A B C : Type ℓ} → (A → ♯ B) → (B → ♯ C) → (A → ♯ C)
(f >=> g) a = do
              b ← f a
              g b

isTotal : ∀ {ℓ} {A B : Type ℓ} → (f : A → ♯ B) → Type (ℓ-max 𝓢 ℓ)
isTotal f = ∀ x → (f x) .support

range : ∀ {ℓ} {A B : Type ℓ} → (f : A → ♯ B) → B → Type (ℓ-max ℓ (ℓ-suc 𝓢))
range {A = A} f b = ∃[ a ∈ A ] f a ≡ return b

domain : ∀ {ℓ} {A B : Type ℓ} → (f : A → ♯ B) → A → Type _
domain f a = (f a) .support

record _≈_ {ℓ} {A : Type ℓ} (x y : ♯ A) : Type (ℓ-max ℓ (ℓ-suc 𝓢)) where
  field
    support-≃ : x .support ≃ y .support
    force-≡ : x .force ≡ y .force ∘ (support-≃ .fst)
open _≈_

-- The proofs are ugly af
-- TODO : Refactor
return-left-identity : ∀ {ℓ} {A B : Type ℓ} (f : A → ♯ B) (x : A) → (return >=> f) x ≈ f x
return-left-identity f x .support-≃ = isoToEquiv (iso (λ (tt* , support) → support) (λ support → (tt* , support)) (λ b → refl) (λ (tt* , support) → refl))
return-left-identity f x .force-≡ i (tt* , fx-support) = f x .force fx-support

return-right-identity : ∀ {ℓ} {A B : Type ℓ} (f : A → ♯ B) (x : A) → (f >=> return) x ≈ f x
return-right-identity f x .support-≃ = isoToEquiv (iso (λ (support , tt*) → support) (λ support → (support , tt*)) (λ b → refl) λ (support , tt*) → refl)
return-right-identity f x .force-≡ i (fx-support , tt*) = f x .force fx-support

-- This is just the associativity of the (dependent) product
>=>-assoc : ∀ {ℓ} {A B C D : Type ℓ} (f : A → ♯ B) (g : B → ♯ C) (h : C → ♯ D) (x : A) → (f >=> g >=> h) x ≈ (f >=> (g >=> h)) x
>=>-assoc f g h x .support-≃ = isoToEquiv (iso (λ ((fx-support , g-fx-forces-support) , hgfx-support) → fx-support , (g-fx-forces-support , hgfx-support)) (λ (fx-support , (g-fx-forces-support , hgfx-support)) → (fx-support , g-fx-forces-support) , hgfx-support) (λ b → refl) λ a → refl)
>=>-assoc f g h x .force-≡ i ((fx-support , gfx-support) , hgfx-support) = (h ((g ((f x) .force fx-support)) .force gfx-support)) .force hgfx-support

