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

AssemblyStr : (X : Type ℓ) → Type _
AssemblyStr X = AssemblyΣ X

AssemblyStrEquiv : StrEquiv AssemblyStr _
AssemblyStrEquiv =
  λ {
    (X , isSetX , _⊩X_ , ⊩Xsurjective)
    (Y , isSetY , _⊩Y_ , ⊩Ysurjective) e →
      ∀ (x : X) (r : A) → ⟨ r ⊩X x ⟩ ≃ ⟨ r ⊩Y (equivFun e x) ⟩  }

AssemblyStrEquiv→PathP : ∀ {X Y} → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → AssemblyStrEquiv X Y e → PathP (λ i → AssemblyStr (ua e i)) (str X) (str Y)
AssemblyStrEquiv→PathP asmX@{X , isSetX , _⊩X_ , ⊩Xsurjective} asmY@{Y , isSetY , _⊩Y_ , ⊩Ysurjective} e strEquiv i
  = isProp→PathP {B = λ j → isSet (ua e j)} (λ i → isPropIsSet) isSetX isSetY i , (λ a p → {!!} , {!!}) , {!!}

AssemblyStrUnivalent : UnivalentStr AssemblyStr AssemblyStrEquiv
AssemblyStrUnivalent {A = X} {B = Y} e = {!!}
