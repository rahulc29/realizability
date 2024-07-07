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

  elimRealizerForMx : ∀ (x : X) (Mx : M .carriers x) → Σ[ a ∈ A ] (a ⊩[ M .assemblies x ] Mx) → subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))
  elimRealizerForMx x Mx (a , a⊩Mx) = [ a , (return (Mx , a⊩Mx , a⊩Mx)) ]

  opaque
    elimRealizerForMx2Constant : ∀ x Mx → 2-Constant (elimRealizerForMx x Mx)
    elimRealizerForMx2Constant x Mx (a , a⊩Mx) (b , b⊩Mx) =
      eq/
        (a , (return (Mx , a⊩Mx , a⊩Mx)))
        (b , return (Mx , b⊩Mx , b⊩Mx))
        (return (Mx , a⊩Mx , b⊩Mx))

  mainMapType : Type _
  mainMapType =
    ∀ (x : X) (Mx : M .carriers x) →
    Σ[ out ∈ (subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))) ]
    (∀ (a : A) → a ⊩[ asmX ] x → (b : A) → b ⊩[ M .assemblies x ] Mx → (λ*2 (# zero) ⨾ a ⨾ b) ⊩[ subQuotientAssembly (theCanonicalPER x) ] out)

  opaque
    mainMap : mainMapType
    mainMap x Mx =
      PT.rec→Set
        (isSetΣ
            squash/
            (λ out →
              isSetΠ3
                λ a a⊩x b →
                  isSet→
                    (isProp→isSet
                      (str
                        (subQuotientRealizability (theCanonicalPER x) (λ*2 (# zero) ⨾ a ⨾ b) out)))))
        ((λ { (c , c⊩Mx) →
          (elimRealizerForMx x Mx (c , c⊩Mx)) ,
          (λ a a⊩x b b⊩Mx →
            subst (_⊩[ subQuotientAssembly (theCanonicalPER x) ] (elimRealizerForMx x Mx (c , c⊩Mx))) (sym (λ*2ComputationRule (# zero) a b)) (return (Mx , b⊩Mx , c⊩Mx))) }))
        (λ { (a , a⊩Mx) (b , b⊩Mx) →
          Σ≡Prop (λ out → isPropΠ4 λ a a⊩x b b⊩Mx → str (subQuotientRealizability (theCanonicalPER x) (λ*2 (# zero) ⨾ a ⨾ b) out)) (elimRealizerForMx2Constant x Mx (a , a⊩Mx) (b , b⊩Mx)) })
        (M .assemblies x .⊩surjective Mx)
