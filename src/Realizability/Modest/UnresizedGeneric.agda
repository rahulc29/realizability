open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Constructions.Slice
open import Categories.CartesianMorphism
open import Categories.GenericObject
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.UnresizedGeneric {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.ResizedPER ca resizing
open import Realizability.PERs.SubQuotient ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Contravariant UNIMOD
open UniformFamily
open DisplayedUFamMap

module Unresized
  {X : Type ℓ}
  (asmX : Assembly X)
  (M : UniformFamily asmX) where

  theCanonicalPER : ∀ x → PER
  theCanonicalPER x = canonicalPER (M . assemblies x) (M .isModestFamily x)

  elimRealizerForMx : ∀ {x : X} {Mx : M .carriers x} → Σ[ a ∈ A ] (a ⊩[ M .assemblies x ] Mx) → subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))
  elimRealizerForMx {x} {Mx} (a , a⊩Mx) = [ a , (return (Mx , a⊩Mx , a⊩Mx)) ]
  
  elimRealizerForMx2Constant : ∀ {x Mx} → 2-Constant (elimRealizerForMx {x} {Mx})
  elimRealizerForMx2Constant {x} {Mx} (a , a⊩Mx) (b , b⊩Mx) =
    eq/
      (a , (return (Mx , a⊩Mx , a⊩Mx)))
      (b , return (Mx , b⊩Mx , b⊩Mx))
      (return (Mx , a⊩Mx , b⊩Mx))

  mainMap : (x : X) (Mx : M .carriers x) → subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))
  mainMap x Mx =
    PT.rec→Set
      squash/
      (elimRealizerForMx {x = x} {Mx = Mx})
      (elimRealizerForMx2Constant {x = x} {Mx = Mx})
      (M .assemblies x .⊩surjective Mx)
      
  opaque
    isTrackedMainMap : ∃[ r ∈ A ] (∀ (x : X) (a : A) → a ⊩[ asmX ] x → (Mx : M .carriers x) → (b : A) → b ⊩[ M .assemblies x ] Mx → (r ⨾ a ⨾ b) ⊩[ subQuotientAssembly (theCanonicalPER x) ] (mainMap x Mx))
    isTrackedMainMap =
      return
        ((λ*2 (# zero)) ,
        (λ x a a⊩x Mx b b⊩Mx →
           PT.elim
             {P = λ MxRealizer → (λ*2 (# zero) ⨾ a ⨾ b) ⊩[ subQuotientAssembly (theCanonicalPER x) ] (PT.rec→Set squash/ (elimRealizerForMx {x = x} {Mx = Mx}) (elimRealizerForMx2Constant {x = x} {Mx = Mx}) MxRealizer)}
             (λ ⊩Mx → subQuotientAssembly (theCanonicalPER x) .⊩isPropValued (λ*2 (# zero) ⨾ a ⨾ b) (rec→Set squash/ elimRealizerForMx elimRealizerForMx2Constant ⊩Mx))
             (λ { (c , c⊩Mx) →
               subst
                 (_⊩[ subQuotientAssembly (theCanonicalPER x) ] (elimRealizerForMx (c , c⊩Mx)))
                 (sym (λ*2ComputationRule (# zero) a b))
                 (return (Mx , b⊩Mx , c⊩Mx))})
             (M .assemblies x .⊩surjective Mx)))
