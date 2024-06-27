open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

module Realizability.PropResizing where

-- Formulation of propositional resizing inspired by the corresponding formulation
-- in TypeTopology
-- https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html

copyOf : ∀ {ℓ} → Type ℓ → (ℓ' : Level) → Type _
copyOf {ℓ} X ℓ' = Σ[ copy ∈ Type ℓ' ] X ≃ copy

copy = fst
copyEquiv = snd

-- We need the principle that TypeTopology calls Ω resizing
-- that the universe of props in a universe 𝓤 has a copy in 𝓤
-- This we call hPropResizing
hPropResizing : ∀ ℓ → Type _
hPropResizing ℓ = copyOf (hProp ℓ) ℓ

-- We obtain a copy of the powerset using hPropResizing
module ResizedPowerset {ℓ} (resizing : hPropResizing ℓ) where

  smallHProp = resizing .fst
  hProp≃smallHProp = resizing .snd
  smallHProp≃hProp = invEquiv hProp≃smallHProp

  𝓟 : Type ℓ → Type ℓ
  𝓟 X = X → smallHProp

  ℙ≃𝓟 : ∀ X → ℙ X ≃ 𝓟 X
  ℙ≃𝓟 X =
    ℙ X
      ≃⟨ idEquiv (ℙ X) ⟩
    (X → hProp ℓ)
      ≃⟨ equiv→ (idEquiv X) hProp≃smallHProp ⟩
    (X → smallHProp)
      ≃⟨ idEquiv (𝓟 X) ⟩
    𝓟 X
      ■

  𝓟≃ℙ : ∀ X → 𝓟 X ≃ ℙ X
  𝓟≃ℙ X = invEquiv (ℙ≃𝓟 X)

  ℙ→𝓟 : ∀ X → ℙ X → 𝓟 X
  ℙ→𝓟 X = equivFun (ℙ≃𝓟 X)

  𝓟→ℙ : ∀ X → 𝓟 X → ℙ X
  𝓟→ℙ X = equivFun (invEquiv (ℙ≃𝓟 X))

  compIsIdEquiv : ∀ X → compEquiv (ℙ≃𝓟 X) (invEquiv (ℙ≃𝓟 X)) ≡ idEquiv (ℙ X)
  compIsIdEquiv X = invEquiv-is-rinv (ℙ≃𝓟 X)

  compIsIdFunc : ∀ {X} (p : ℙ X) → 𝓟→ℙ X (ℙ→𝓟 X p) ≡ p
  compIsIdFunc {X} p i = equivFun (compIsIdEquiv X i) p

  _ϵ_ : ∀ {X} → X → 𝓟 X → Type ℓ
  _ϵ_ {X} x P = x ∈ 𝓟→ℙ X P

  isPropϵ : ∀ {X} (x : X) P → isProp (x ϵ P)
  isPropϵ {X} x P = ∈-isProp (𝓟→ℙ X P) x

  isSet𝓟 : ∀ X → isSet (𝓟 X)
  isSet𝓟 X = isOfHLevelRespectEquiv 2 (ℙ≃𝓟 X) isSetℙ

  𝓟≡Equiv : ∀ {X} (P Q : 𝓟 X) → (P ≡ Q) ≃ (𝓟→ℙ X P ≡ 𝓟→ℙ X Q)
  𝓟≡Equiv {X} P Q = congEquiv {x = P} {y = Q} (𝓟≃ℙ X)

  𝓟≡ : ∀ {X} (P Q : 𝓟 X) → 𝓟→ℙ X P ≡ 𝓟→ℙ X Q → P ≡ Q
  𝓟≡ {X} P Q equ = equivFun (invEquiv (𝓟≡Equiv P Q)) equ
  
