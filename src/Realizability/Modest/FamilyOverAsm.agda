open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Limits.Pullback
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.FamilyOverAsm {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Pullbacks ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Modest.Base ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Pullback

module _ {X : Type ℓ} (asmX : Assembly X) (Y : Type ℓ) (asmY : Assembly Y) where
  record FamilyOver : Type (ℓ-suc ℓ) where
    no-eta-equality
    constructor makeFamilyOver
    field
      fibration : AssemblyMorphism asmY asmX
      {-
        A[x] ------> A
         |_|         |
         |           |
         |           | fibration
         |           |
         ↓           ↓
         1 --------> X
              x

        For any x the fiber over x is modest
      -}
      fiberOver :
        ∀ (x : X) (a : A) → (a⊩x : a ⊩[ asmX ] x) →
        Pullback
          ASM
          (cospan
            (Unit* , terminalAsm)
            (X , asmX)
            (Y , asmY)
            (globalElement asmX x a a⊩x)
            fibration)
      isModestFibreOver : ∀ (x : X) (a : A) (a⊩x : a ⊩[ asmX ] x) → isModest (fiberOver x a a⊩x .pbOb .snd)

