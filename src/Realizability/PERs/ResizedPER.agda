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
open import Cubical.Foundations.Path
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
open import Realizability.Modest.Base ca

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

smallHProp = resizing .fst
hProp≃smallHProp = resizing .snd
smallHProp≃hProp = invEquiv hProp≃smallHProp

isSetSmallHProp : isSet smallHProp
isSetSmallHProp = isOfHLevelRespectEquiv 2 hProp≃smallHProp isSetHProp

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

isPropExtractType : ∀ p → isProp (extractType p)
isPropExtractType p = str (enlarge p)

extractFromShrunk : ∀ p isPropP → extractType (shrink (p , isPropP)) ≡ p
extractFromShrunk p isPropP =
  extractType (shrink (p , isPropP))
    ≡⟨ refl ⟩
  ⟨ enlarge (shrink (p , isPropP)) ⟩
    ≡⟨ cong ⟨_⟩ (shrink⋆enlarge≡id (p , isPropP)) ⟩
  p
    ∎

shrinkFromExtracted : ∀ p → shrink (extractType p , isPropExtractType p) ≡ p
shrinkFromExtracted p =
  shrink (extractType p , isPropExtractType p)
    ≡⟨ refl ⟩
  shrink (enlarge p)
    ≡⟨ enlarge⋆shrink≡id p ⟩
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

unquoteDecl ResizedPERIsoΣ = declareRecordIsoΣ ResizedPERIsoΣ (quote ResizedPER)

ResizedPERΣ : Type ℓ
ResizedPERΣ =
  Σ[ relation ∈ (A → A → smallHProp) ]
  (∀ a b → extractType (relation a b) → extractType (relation b a)) ×
  (∀ a b c → extractType (relation a b) → extractType (relation b c) → extractType (relation a c))

isSetResizedPERΣ : isSet ResizedPERΣ
isSetResizedPERΣ =
  isSetΣ
    (isSet→ (isSet→ isSetSmallHProp))
    (λ relation → isProp→isSet (isProp× (isPropΠ3 λ _ _ _ → isPropExtractType _) (isPropΠ5 λ _ _ _ _ _ → isPropExtractType _)))

isSetResizedPER : isSet ResizedPER
isSetResizedPER = isOfHLevelRetractFromIso 2 ResizedPERIsoΣ isSetResizedPERΣ

ResizedPER≡Iso : ∀ (R S : ResizedPER) → Iso (R ≡ S) (∀ a b → R .relation a b ≡ S .relation a b)
Iso.fun (ResizedPER≡Iso R S) R≡S a b i = (R≡S i) .relation a b
relation (Iso.inv (ResizedPER≡Iso R S) pointwise i) a b = pointwise a b i
isSymmetric (Iso.inv (ResizedPER≡Iso R S) pointwise i) =
  isProp→PathP
    {B = λ j → (a b : A) → extractType (pointwise a b j) → extractType (pointwise b a j)}
    (λ j → isPropΠ3 λ _ _ _ → isPropExtractType _)
    (isSymmetric R)
    (isSymmetric S) i
isTransitive (Iso.inv (ResizedPER≡Iso R S) pointwise i) =
  isProp→PathP
    {B = λ j → (a b c : A) → extractType (pointwise a b j) → extractType (pointwise b c j) → extractType (pointwise a c j)}
    (λ j → isPropΠ5 λ _ _ _ _ _ → isPropExtractType _)
    (R .isTransitive)
    (S .isTransitive)
    i
Iso.rightInv (ResizedPER≡Iso R S) pointwise = refl
Iso.leftInv (ResizedPER≡Iso R S) R≡S = isSetResizedPER R S _ _

ResizedPER≡ : ∀ (R S : ResizedPER) → (∀ a b → R .relation a b ≡ S .relation a b) → R ≡ S
ResizedPER≡ R S pointwise = Iso.inv (ResizedPER≡Iso R S) pointwise

ResizedPERIsoPER : Iso ResizedPER PER
PER.relation (Iso.fun ResizedPERIsoPER resized) a b = extractType (resized .relation a b)
PER.isPropValued (Iso.fun ResizedPERIsoPER resized) a b = isPropExtractType _
fst (PER.isPER (Iso.fun ResizedPERIsoPER resized)) a b a~b = resized .isSymmetric a b a~b
snd (PER.isPER (Iso.fun ResizedPERIsoPER resized)) a b c a~b b~c = resized .isTransitive a b c a~b b~c
relation (Iso.inv ResizedPERIsoPER per) a b = shrink (per .PER.relation a b , per .PER.isPropValued a b)
isSymmetric (Iso.inv ResizedPERIsoPER per) a b a~[resized]b = b~[resized]a where
  a~b : per .PER.relation a b
  a~b = transport (extractFromShrunk _ _) a~[resized]b

  b~a : per .PER.relation b a
  b~a = per .PER.isPER .fst a b a~b

  b~[resized]a : extractType (shrink (per .PER.relation b a , per .PER.isPropValued b a))
  b~[resized]a = transport (sym (extractFromShrunk _ _)) b~a
isTransitive (Iso.inv ResizedPERIsoPER per) a b c a~[resized]b b~[resized]c = a~[resized]c where
  a~b : per .PER.relation a b
  a~b = transport (extractFromShrunk _ _) a~[resized]b

  b~c : per .PER.relation b c
  b~c = transport (extractFromShrunk _ _) b~[resized]c

  a~c : per .PER.relation a c
  a~c = per .PER.isPER .snd a b c a~b b~c

  a~[resized]c : extractType (shrink (per .PER.relation a c , per .PER.isPropValued a c))
  a~[resized]c = transport (sym (extractFromShrunk _ _)) a~c
Iso.rightInv ResizedPERIsoPER per =
  PER≡ _ _
    (funExt₂
      λ a b →
        extractFromShrunk (per .PER.relation a b) (per .PER.isPropValued a b))
Iso.leftInv ResizedPERIsoPER resizedPer =
  ResizedPER≡ _ _
    λ a b → shrinkFromExtracted (resizedPer .relation a b)

opaque
  shrinkPER : PER → ResizedPER
  shrinkPER = ResizedPERIsoPER .Iso.inv

opaque
  enlargePER : ResizedPER → PER
  enlargePER = ResizedPERIsoPER .Iso.fun

opaque
  unfolding shrinkPER
  unfolding enlargePER
  shrinkPER⋆enlargePER≡id : ∀ resized → shrinkPER (enlargePER resized) ≡ resized
  shrinkPER⋆enlargePER≡id resized = ResizedPERIsoPER .Iso.leftInv resized

opaque
  unfolding shrinkPER
  unfolding enlargePER
  enlargePER⋆shrinkPER≡id : ∀ per → enlargePER (shrinkPER per) ≡ per
  enlargePER⋆shrinkPER≡id per = ResizedPERIsoPER .Iso.rightInv per

ResizedPER≃PER : ResizedPER ≃ PER
ResizedPER≃PER = isoToEquiv ResizedPERIsoPER

opaque
  transportFromSmall : ∀ {ℓ'} {P : ResizedPER → Type ℓ'} → (∀ per → P (shrinkPER per)) → ∀ resized → P resized
  transportFromSmall {ℓ'} {P} small resized = subst P (shrinkPER⋆enlargePER≡id resized) (small (enlargePER resized))

opaque
  transportFromLarge : ∀ {ℓ'} {P : PER → Type ℓ'} → (∀ resized → P (enlargePER resized)) → ∀ per → P per
  transportFromLarge {ℓ'} {P} large per = subst P (enlargePER⋆shrinkPER≡id per) (large (shrinkPER per))
