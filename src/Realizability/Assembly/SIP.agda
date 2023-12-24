open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.SIP {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

Assembly≡ : ∀ {X Y : Type ℓ}
          → (asmX : Assembly X)
          → (asmY : Assembly Y)
          → (P : X ≡ Y)
          → (⊩overP : PathP (λ i → ∀ (a : A) (p : P i) → Type ℓ) (asmX ._⊩_) (asmY ._⊩_))
          → PathP (λ i → Assembly (P i)) asmX asmY
Assembly≡ {X} {Y} asmX asmY P ⊩overP = {!AssemblyIsoΣ!}
