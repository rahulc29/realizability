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

module Realizability.Modest.GenericUniformFamily {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

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

uniformFamilyCleavage : cleavage
uniformFamilyCleavage {X , asmX} {Y , asmY} f N =
  N' , fᴰ , cartfᴰ where
    N' : UniformFamily asmX
    UniformFamily.carriers N' x = N .carriers (f .map x)
    UniformFamily.assemblies N' x = N .assemblies (f .map x)
    UniformFamily.isModestFamily N' x = N .isModestFamily (f .map x)

    fᴰ : DisplayedUFamMap asmX asmY f N' N
    DisplayedUFamMap.fibrewiseMap fᴰ x Nfx = Nfx
    DisplayedUFamMap.isTracked fᴰ =
      do
        let
          realizer : Term as 2
          realizer = # zero
        return
          (λ*2 realizer ,
          (λ x a a⊩x Nfx b b⊩Nfx →
            subst
              (_⊩[ N .assemblies (f .map x) ] Nfx)
              (sym (λ*2ComputationRule realizer a b))
              b⊩Nfx))

    opaque
      unfolding isCartesian'
      cart'fᴰ : isCartesian' f fᴰ
      cart'fᴰ {Z , asmZ} {M} g hᴰ =
        (! , !⋆fᴰ≡hᴰ) ,
        λ { (!' , !'comm) →
          Σ≡Prop
            (λ ! → UNIMOD .Categoryᴰ.isSetHomᴰ _ _)
            (DisplayedUFamMapPathP
              _ _ _ _ _ _ _ _ _
              λ z Mz →
                sym
                  (!' .fibrewiseMap z Mz
                    ≡[ i ]⟨ !'comm i .fibrewiseMap z Mz ⟩
                  hᴰ .fibrewiseMap z Mz
                    ∎)) } where
          ! : DisplayedUFamMap asmZ asmX g M N'
          DisplayedUFamMap.fibrewiseMap ! z Mz = hᴰ .fibrewiseMap z Mz
          DisplayedUFamMap.isTracked ! = hᴰ .isTracked

          !⋆fᴰ≡hᴰ : composeDisplayedUFamMap asmZ asmX asmY g f M N' N ! fᴰ ≡ hᴰ
          !⋆fᴰ≡hᴰ =
            DisplayedUFamMapPathP
              asmZ asmY _ _
              M N
              (composeDisplayedUFamMap asmZ asmX asmY g f M N' N ! fᴰ) hᴰ refl
              λ z Mz → refl

    cartfᴰ : isCartesian f fᴰ
    cartfᴰ = isCartesian'→isCartesian f fᴰ cart'fᴰ

∇PER = ∇ ⟅ ResizedPER , isSetResizedPER ⟆
asm∇PER = ∇PER .snd

genericUniformFamily : GenericObject UNIMOD
GenericObject.base genericUniformFamily = ∇PER
UniformFamily.carriers (GenericObject.displayed genericUniformFamily) per = subQuotient (enlargePER per)
UniformFamily.assemblies (GenericObject.displayed genericUniformFamily) per = subQuotientAssembly (enlargePER per)
UniformFamily.isModestFamily (GenericObject.displayed genericUniformFamily) per = isModestSubQuotientAssembly (enlargePER per)
GenericObject.isGeneric genericUniformFamily {X , asmX} M =
  f , fᴰ , {!!} where

    f : AssemblyMorphism asmX asm∇PER
    AssemblyMorphism.map f x = shrinkPER (canonicalPER (M .assemblies x) (M .isModestFamily x))
    AssemblyMorphism.tracker f = return (k , (λ _ _ _ → tt*))

    subQuotientTargetType : (x : X) → M .carriers x → Type ℓ
    subQuotientTargetType x Mx = subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))

    fᴰ : DisplayedUFamMap asmX asm∇PER f M (genericUniformFamily .GenericObject.displayed)
    DisplayedUFamMap.fibrewiseMap fᴰ x Mx =
      subst (λ x → subQuotient x) (sym equation) target module CartesianMapDefinition where
        targetType : Type ℓ
        targetType = subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))

        opaque
          equation : enlargePER (shrinkPER (canonicalPER (M .assemblies x) (M .isModestFamily x))) ≡ canonicalPER (M .assemblies x) (M .isModestFamily x)
          equation = enlargePER⋆shrinkPER≡id (canonicalPER (M .assemblies x) (M .isModestFamily x))

        mainMap : Σ[ a ∈ A ] (a ⊩[ M .assemblies x ] Mx) → subQuotient (canonicalPER (M .assemblies x) (M .isModestFamily x))
        mainMap (a , a⊩Mx) = [ a ]

        mainMap2Constant : 2-Constant mainMap
        mainMap2Constant (a , a⊩Mx) (b , b⊩Mx) = eq/ a b (return (Mx , a⊩Mx , b⊩Mx))

        opaque
          target : targetType
          target =
            PT.rec→Set
              squash/
              mainMap
              mainMap2Constant
              (M .assemblies x .⊩surjective Mx)

        opaque
          isTrackedCartesianMap :
            ∀ (a : A)
            → a ⊩[ asmX ] x
            → (b : A)
            → b ⊩[ M .assemblies x ] Mx
            → ⟨
              subQuotientRealizability
                (enlargePER (shrinkPER (canonicalPER (M .assemblies x) (M .isModestFamily x))))
                (λ*2 (# one) ⨾ a ⨾ b)
                (subst subQuotient (sym equation) target)
              ⟩
          isTrackedCartesianMap a a⊩x b b⊩Mx =
            {!!}
    DisplayedUFamMap.isTracked fᴰ =
      do
        return
          (λ*2 (# one) ,
           λ x a a⊩x Mx b b⊩Mx → {!CartesianMapDefinition.isTrackedCartesianMap x Mx a a⊩x b b⊩Mx!})
    
