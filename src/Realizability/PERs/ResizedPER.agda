open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
open import Realizability.PropResizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (Id)

module Realizability.PERs.ResizedPER
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.PERs.PER ca

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

smallHProp = resizing .fst
hProp≃smallHProp = resizing .snd
smallHProp≃hProp = invEquiv hProp≃smallHProp

hPropIsoSmallHProp : Iso (hProp ℓ) smallHProp
hPropIsoSmallHProp = equivToIso hProp≃smallHProp

shrink : hProp ℓ → smallHProp
shrink = Iso.fun hPropIsoSmallHProp

enlarge : smallHProp → hProp ℓ
enlarge = Iso.inv hPropIsoSmallHProp

enlarge⋆shrink≡id : section shrink enlarge
enlarge⋆shrink≡id = Iso.rightInv hPropIsoSmallHProp

shrink⋆enlarge≡id : retract shrink enlarge
shrink⋆enlarge≡id = Iso.leftInv hPropIsoSmallHProp

extractType : smallHProp → Type ℓ
extractType p = ⟨ enlarge p ⟩

extractFromShrunk : ∀ p isPropP → extractType (shrink (p , isPropP)) ≡ p
extractFromShrunk p isPropP =
  extractType (shrink (p , isPropP))
    ≡⟨ refl ⟩
  ⟨ enlarge (shrink (p , isPropP)) ⟩
    ≡⟨ cong ⟨_⟩ (shrink⋆enlarge≡id (p , isPropP)) ⟩
  p
    ∎

record ResizedPER : Type ℓ where
  no-eta-equality
  constructor makeResizedPER
  field
    relation : A → A → smallHProp
    isSymmetric : ∀ a b → extractType (relation a b) → extractType (relation b a)
    isTransitive : ∀ a b c → extractType (relation a b) → extractType (relation b c) → extractType (relation a c)
    
open ResizedPER

ResizedPERHAEquivPER : HAEquiv ResizedPER PER
PER.relation (fst ResizedPERHAEquivPER resized) =
  (λ a b → extractType (resized .relation a b)) ,
   λ a b → str (enlarge (resized .relation a b))
fst (PER.isPER (fst ResizedPERHAEquivPER resized)) a b a~b = resized .isSymmetric a b a~b
snd (PER.isPER (fst ResizedPERHAEquivPER resized)) a b c a~b b~c = resized .isTransitive a b c a~b b~c
relation (isHAEquiv.g (snd ResizedPERHAEquivPER) per) a b =
  shrink ((per .PER.relation .fst a b) , (per .PER.relation .snd a b))
isSymmetric (isHAEquiv.g (snd ResizedPERHAEquivPER) per) a b a~b =
  subst _ (sym (extractFromShrunk (per .PER.relation .fst b a) (per .PER.relation .snd b a))) {!per .PER.isPER .fst a b a~b!}
isTransitive (isHAEquiv.g (snd ResizedPERHAEquivPER) per) a b c a~b b~c = {!!}
isHAEquiv.linv (snd ResizedPERHAEquivPER) resized = {!!}
isHAEquiv.rinv (snd ResizedPERHAEquivPER) per = {!!}
isHAEquiv.com (snd ResizedPERHAEquivPER) resized = {!!}

ResizedPER≃PER : ResizedPER ≃ PER
ResizedPER≃PER = ResizedPERHAEquivPER .fst , isHAEquiv→isEquiv (ResizedPERHAEquivPER .snd)
