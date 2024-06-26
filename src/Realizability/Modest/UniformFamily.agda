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
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Constructions.Slice
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.UniformFamily {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Modest.Base ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

record UniformFamily {I : Type ℓ} (asmI : Assembly I) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    carriers : I → Type ℓ
    assemblies : ∀ i → Assembly (carriers i)
    isModestFamily : ∀ i → isModest (assemblies i)
open UniformFamily
record DisplayedUFamMap {I J : Type ℓ} (asmI : Assembly I) (asmJ : Assembly J) (u : AssemblyMorphism asmI asmJ) (X : UniformFamily asmI) (Y : UniformFamily asmJ) : Type ℓ where
  no-eta-equality
  field
    fibrewiseMap : ∀ i → X .carriers i → Y .carriers (u .map i)
    isTracked : ∃[ e ∈ A ] (∀ (i : I) (a : A) (a⊩i : a ⊩[ asmI ] i) (x : X .carriers i) (b : A) (b⊩x : b ⊩[ X .assemblies i ] x) → (e ⨾ a ⨾ b) ⊩[ Y .assemblies (u .map i) ] (fibrewiseMap i x))

open DisplayedUFamMap

DisplayedUFamMapPathP :
  ∀ {I J} (asmI : Assembly I) (asmJ : Assembly J) →
  ∀ u v X Y
  → (uᴰ : DisplayedUFamMap asmI asmJ u X Y)
  → (vᴰ : DisplayedUFamMap asmI asmJ v X Y)
  → (p : u ≡ v)
  → (∀ (i : I) (x : X .carriers i) → PathP (λ j → Y .carriers (p j .map i)) (uᴰ .fibrewiseMap i x) (vᴰ .fibrewiseMap i x))
  -----------------------------------------------------------------------------------------------------------------------
  → PathP (λ i → DisplayedUFamMap asmI asmJ (p i) X Y) uᴰ vᴰ
fibrewiseMap (DisplayedUFamMapPathP {I} {J} asmI asmJ u v X Y uᴰ vᴰ p pᴰ dimI) i x = pᴰ i x dimI
isTracked (DisplayedUFamMapPathP {I} {J} asmI asmJ u v X Y uᴰ vᴰ p pᴰ dimI) =
  isProp→PathP
    {B = λ dimJ → ∃[ e ∈ A ] ((i : I) (a : A) → a ⊩[ asmI ] i → (x : X .carriers i) (b : A) → b ⊩[ X .assemblies i ] x → (e ⨾ a ⨾ b) ⊩[ Y .assemblies (p dimJ .map i) ] pᴰ i x dimJ)}
    (λ dimJ → isPropPropTrunc)
    (uᴰ .isTracked)
    (vᴰ .isTracked)
    dimI

isSetDisplayedUFamMap : ∀ {I J} (asmI : Assembly I) (asmJ : Assembly J) → ∀ u X Y → isSet (DisplayedUFamMap asmI asmJ u X Y)
fibrewiseMap (isSetDisplayedUFamMap {I} {J} asmI asmJ u X Y f g p q dimI dimJ) i x =
  isSet→isSet'
    (Y .assemblies (u .map i) .isSetX)
    {a₀₀ = fibrewiseMap f i x}
    {a₀₁ = fibrewiseMap f i x}
    refl
    {a₁₀ = fibrewiseMap g i x}
    {a₁₁ = fibrewiseMap g i x}
    refl
    (λ dimK → fibrewiseMap (p dimK) i x)
    (λ dimK → fibrewiseMap (q dimK) i x)
    dimJ dimI
isTracked (isSetDisplayedUFamMap {I} {J} asmI asmJ u X Y f g p q dimI dimJ) =
  isProp→SquareP
    {B = λ dimI dimJ →
      ∃[ e ∈ A ]
        ((i : I) (a : A) →
         a ⊩[ asmI ] i →
         (x : X .carriers i) (b : A) →
         b ⊩[ X .assemblies i ] x →
         (e ⨾ a ⨾ b) ⊩[ Y .assemblies (u .map i) ]
         isSet→isSet'
         (Y .assemblies
          (u .map i)
          .isSetX)
         (λ _ → fibrewiseMap f i x) (λ _ → fibrewiseMap g i x)
         (λ dimK → fibrewiseMap (p dimK) i x)
         (λ dimK → fibrewiseMap (q dimK) i x) dimJ dimI)}
      (λ dimI dimJ → isPropPropTrunc)
      {a = isTracked f}
      {b = isTracked g}
      {c = isTracked f}
      {d = isTracked g}
      refl
      refl
      (λ dimK → isTracked (p dimK))
      (λ dimK → isTracked (q dimK))
      dimI dimJ

DisplayedUFamMapPathPIso :
  ∀ {I J} (asmI : Assembly I) (asmJ : Assembly J) →
  ∀ u v X Y
  → (uᴰ : DisplayedUFamMap asmI asmJ u X Y)
  → (vᴰ : DisplayedUFamMap asmI asmJ v X Y)
  → (p : u ≡ v)
  → Iso
    (∀ (i : I) (x : X .carriers i) → PathP (λ dimI → Y .carriers (p dimI .map i)) (uᴰ .fibrewiseMap i x) (vᴰ .fibrewiseMap i x))
    (PathP (λ dimI → DisplayedUFamMap asmI asmJ (p dimI) X Y) uᴰ vᴰ)
Iso.fun (DisplayedUFamMapPathPIso {I} {J} asmI asmJ u v X Y uᴰ vᴰ p) pᴰ = DisplayedUFamMapPathP asmI asmJ u v X Y uᴰ vᴰ p pᴰ
Iso.inv (DisplayedUFamMapPathPIso {I} {J} asmI asmJ u v X Y uᴰ vᴰ p) uᴰ≡vᴰ i x dimI = (uᴰ≡vᴰ dimI) .fibrewiseMap i x
Iso.rightInv (DisplayedUFamMapPathPIso {I} {J} asmI asmJ u v X Y uᴰ vᴰ p) uᴰ≡vᴰ dimI dimJ =
  isSet→SquareP
    {A = λ dimK dimL → DisplayedUFamMap asmI asmJ (p dimL) X Y}
    (λ dimI dimJ → isSetDisplayedUFamMap asmI asmJ (p dimJ) X Y)
    {a₀₀ = uᴰ}
    {a₀₁ = vᴰ}
    (λ dimK → DisplayedUFamMapPathP asmI asmJ u v X Y uᴰ vᴰ p (λ i x dimL → uᴰ≡vᴰ dimL .fibrewiseMap i x) dimK)
    {a₁₀ = uᴰ}
    {a₁₁ = vᴰ}
    uᴰ≡vᴰ
    refl
    refl dimI dimJ
Iso.leftInv (DisplayedUFamMapPathPIso {I} {J} asmI asmJ u v X Y uᴰ vᴰ p) pᴰ = refl

idDisplayedUFamMap : ∀ {I} (asmI : Assembly I) (p : UniformFamily asmI) → DisplayedUFamMap asmI asmI (identityMorphism asmI) p p
DisplayedUFamMap.fibrewiseMap (idDisplayedUFamMap {I} asmI p) i pi = pi
DisplayedUFamMap.isTracked (idDisplayedUFamMap {I} asmI p) =
  return
    (λ*2 realizer ,
     λ i a a⊩i x b b⊩x →
       subst
         (λ r → r ⊩[ p .assemblies i ] x)
         (sym (λ*2ComputationRule realizer a b))
         b⊩x) where
  realizer : Term as 2
  realizer = # zero

module _
  {I J K : Type ℓ}
  (asmI : Assembly I)
  (asmJ : Assembly J)
  (asmK : Assembly K)
  (f : AssemblyMorphism asmI asmJ)
  (g : AssemblyMorphism asmJ asmK)
  (X : UniformFamily asmI)
  (Y : UniformFamily asmJ)
  (Z : UniformFamily asmK)
  (fᴰ : DisplayedUFamMap asmI asmJ f X Y)
  (gᴰ : DisplayedUFamMap asmJ asmK g Y Z) where

  composeDisplayedUFamMap : DisplayedUFamMap asmI asmK (f ⊚ g) X Z
  DisplayedUFamMap.fibrewiseMap composeDisplayedUFamMap i Xi = gᴰ .fibrewiseMap (f .map i) (fᴰ .fibrewiseMap i Xi)
  DisplayedUFamMap.isTracked composeDisplayedUFamMap =
    do
      (gᴰ~ , isTrackedGᴰ) ← gᴰ .isTracked
      (fᴰ~ , isTrackedFᴰ) ← fᴰ .isTracked
      (f~ , isTrackedF) ← f .tracker
      let
        realizer : Term as 2
        realizer = ` gᴰ~ ̇ (` f~ ̇ # one) ̇ (` fᴰ~ ̇ # one ̇ # zero)
      return
        (λ*2 realizer ,
        (λ i a a⊩i x b b⊩x →
          subst
            (_⊩[ Z .assemblies (g .map (f .map i)) ] _)
            (sym (λ*2ComputationRule realizer a b))
            (isTrackedGᴰ (f .map i) (f~ ⨾ a) (isTrackedF i a a⊩i) (fᴰ .fibrewiseMap i x) (fᴰ~ ⨾ a ⨾ b) (isTrackedFᴰ i a a⊩i x b b⊩x))))

UNIMOD : Categoryᴰ ASM (ℓ-suc ℓ) ℓ
Categoryᴰ.ob[ UNIMOD ] (I , asmI) = UniformFamily asmI
Categoryᴰ.Hom[_][_,_] UNIMOD {I , asmI} {J , asmJ} u X Y = DisplayedUFamMap asmI asmJ u X Y
Categoryᴰ.idᴰ UNIMOD {I , asmI} {X} = idDisplayedUFamMap asmI X
Categoryᴰ._⋆ᴰ_ UNIMOD {I , asmI} {J , asmJ} {K , asmK} {f} {g} {X} {Y} {Z} fᴰ gᴰ = composeDisplayedUFamMap asmI asmJ asmK f g X Y Z fᴰ gᴰ
Categoryᴰ.⋆IdLᴰ UNIMOD {I , asmI} {J , asmJ} {f} {X} {Y} fᴰ =
  DisplayedUFamMapPathP
    asmI asmJ
    (identityMorphism asmI ⊚ f) f
    X Y
    (composeDisplayedUFamMap asmI asmI asmJ (Category.id ASM) f X X Y (idDisplayedUFamMap asmI X) fᴰ)
    fᴰ
    (Category.⋆IdL ASM f)
    (λ i x → refl)
Categoryᴰ.⋆IdRᴰ UNIMOD {I , asmI} {J , asmJ} {f} {X} {Y} fᴰ =
  DisplayedUFamMapPathP
    asmI asmJ
    (f ⊚ identityMorphism asmJ) f
    X Y
    (composeDisplayedUFamMap asmI asmJ asmJ f (Category.id ASM) X Y Y fᴰ (idDisplayedUFamMap asmJ Y))
    fᴰ
    (Category.⋆IdR ASM f)
    λ i x → refl
Categoryᴰ.⋆Assocᴰ UNIMOD {I , asmI} {J , asmJ} {K , asmK} {L , asmL} {f} {g} {h} {X} {Y} {Z} {W} fᴰ gᴰ hᴰ =
  DisplayedUFamMapPathP
    asmI asmL
    ((f ⊚ g) ⊚ h) (f ⊚ (g ⊚ h))
    X W
    (composeDisplayedUFamMap
      asmI asmK asmL
      (f ⊚ g) h X Z W
      (composeDisplayedUFamMap asmI asmJ asmK f g X Y Z fᴰ gᴰ)
      hᴰ)
    (composeDisplayedUFamMap
      asmI asmJ asmL
      f (g ⊚ h) X Y W
      fᴰ (composeDisplayedUFamMap asmJ asmK asmL g h Y Z W gᴰ hᴰ))
    (Category.⋆Assoc ASM f g h)
    λ i x → refl
Categoryᴰ.isSetHomᴰ UNIMOD {I , asmI} {J , asmJ} {f} {X} {Y} = isSetDisplayedUFamMap asmI asmJ f X Y
