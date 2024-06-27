open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
open import Realizability.PropResizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

module Realizability.PERs.UniformFamiliesOverAsm
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.PERs.PER ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

module _
  {I J : Type ℓ} {asmI : Assembly I} {asmJ : Assembly J} (u : AssemblyMorphism asmI asmJ) (R : I → PER) (S : J → PER) where

  isDisplayedTracker : A → Type _
  isDisplayedTracker a = ∀ (i : I) (b : A) → b ⊩[ asmI ] i → isTracker (R i) (S (u .map i)) (a ⨾ b)

  isPropIsDisplayedTracker : ∀ a → isProp (isDisplayedTracker a)
  isPropIsDisplayedTracker a = isPropΠ3 λ i b b⊩i → isPropΠ3 λ r r' r~r' → isProp~ _ (S (u .map i)) _

  displayedTracker : Type _
  displayedTracker = Σ[ a ∈ A ] isDisplayedTracker a

  isSetDisplayedTracker : isSet displayedTracker
  isSetDisplayedTracker = isSetΣ isSetA (λ a → isProp→isSet (isPropIsDisplayedTracker a))

  isEquivDisplayedTracker : displayedTracker → displayedTracker → Type _
  isEquivDisplayedTracker (f , f⊩f) (g , g⊩g) = ∀ (i : I) (a : A) (a⊩i : a ⊩[ asmI ] i) → isEquivTracker (R i) (S (u .map i)) (f ⨾ a , f⊩f i a a⊩i) (g ⨾ a , g⊩g i a a⊩i)

  displayedPerMorphism : Type _
  displayedPerMorphism = displayedTracker / isEquivDisplayedTracker

idDisplayedTracker : {I : Type ℓ} → (asmI : Assembly I) → (R : I → PER) → displayedTracker (identityMorphism asmI) R R
idDisplayedTracker {I} asmI R = λ*2 (# zero) , (λ i a a⊩i r r' r~r' → subst2 _~[ R i ]_ (sym (λ*2ComputationRule (# zero) a r)) (sym (λ*2ComputationRule (# zero) a r')) r~r' )

open Category ASM
module _
  {I J K : Type ℓ}
  {asmI : Assembly I}
  {asmJ : Assembly J}
  {asmK : Assembly K}
  (f : AssemblyMorphism asmI asmJ)
  (g : AssemblyMorphism asmJ asmK)
  (R : I → PER)
  (S : J → PER)
  (T : K → PER)
  (fᴰ : displayedPerMorphism f R S)
  (gᴰ : displayedPerMorphism g S T) where

UFAMPER : Categoryᴰ ASM (ℓ-suc ℓ) ℓ
Categoryᴰ.ob[ UFAMPER ] (X , asmX) = X → PER
Categoryᴰ.Hom[_][_,_] UFAMPER {I , asmI} {J , asmJ} u R S = displayedPerMorphism u R S
Categoryᴰ.idᴰ UFAMPER {I , asmI} {R} = [ idDisplayedTracker asmI R ]
Categoryᴰ._⋆ᴰ_ UFAMPER {I , asmI} {J , asmJ} {K , asmK} {f} {g} {R} {S} {T} fᴰ gᴰ = {!!}
Categoryᴰ.⋆IdLᴰ UFAMPER = {!!}
Categoryᴰ.⋆IdRᴰ UFAMPER = {!!}
Categoryᴰ.⋆Assocᴰ UFAMPER = {!!}
Categoryᴰ.isSetHomᴰ UFAMPER = {!!}
