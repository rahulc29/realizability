open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.SIP {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca


AssemblyStr : (X : Type ℓ) → Type _
AssemblyStr X = AssemblyΣ X

AssemblyStrEquiv : StrEquiv AssemblyStr _
AssemblyStrEquiv =
  λ { (X , isSetX , _⊩X_ , ⊩Xsurjective) (Y , isSetY , _⊩Y_ , ⊩Ysurjective) e → {!!} }
