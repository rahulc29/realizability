{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad 
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.BinCoproducts {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open import Realizability.Assembly.Base ca
open Realizability.CombinatoryAlgebra.Combinators ca
open import Realizability.Assembly.Morphism ca

infixl 23 _⊕_
_⊕_ : {A B : Type ℓ} → Assembly A → Assembly B → Assembly (A ⊎ B)
(as ⊕ bs) .isSetX = isSet⊎ (as .isSetX) (bs .isSetX)
(as ⊕ bs) ._⊩_ r (inl a) = ∃[ aᵣ ∈ A ] (as ._⊩_ aᵣ a) × (r ≡ pair ⨾ true ⨾ aᵣ)
(as ⊕ bs) ._⊩_ r (inr b) = ∃[ bᵣ ∈ A ] (bs ._⊩_ bᵣ b) × (r ≡ pair ⨾ false ⨾ bᵣ)
(as ⊕ bs) .⊩isPropValued r (inl a) = squash₁
(as ⊕ bs) .⊩isPropValued r (inr b) = squash₁
(as ⊕ bs) .⊩surjective (inl a) =
                               do
                               (a~ , a~realizes) ← as .⊩surjective a
                               return ( pair ⨾ true ⨾ a~
                                      , ∣ a~
                                      , a~realizes
                                      , refl ∣₁
                                      )
(as ⊕ bs) .⊩surjective (inr b) =
                               do
                               (b~ , b~realizes) ← bs .⊩surjective b
                               return ( pair ⨾ false ⨾ b~
                                      , ∣ b~
                                      , b~realizes
                                      , refl ∣₁
                                      )
                                        
κ₁ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism as (as ⊕ bs)
κ₁ .map = inl
κ₁ .tracker = ∣ pair ⨾ true , (λ x aₓ aₓ⊩x → ∣ aₓ , aₓ⊩x , refl ∣₁) ∣₁

κ₂ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism bs (as ⊕ bs)
κ₂ .map b = inr b
κ₂ .tracker = ∣ pair ⨾ false , (λ x bₓ bₓ⊩x → ∣ bₓ , bₓ⊩x , refl ∣₁) ∣₁

-- TODO : Universal Property
