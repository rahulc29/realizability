open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
open import Realizability.PropResizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma

module Realizability.PERs.PER
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

isPartialEquivalenceRelation : PropRel A A ℓ → Type _
isPartialEquivalenceRelation (rel , isPropValuedRel) = BinaryRelation.isSym rel × BinaryRelation.isTrans rel

isPropIsPartialEquivalenceRelation : ∀ r → isProp (isPartialEquivalenceRelation r)
isPropIsPartialEquivalenceRelation (rel , isPropValuedRel) =
  isProp×
    (isPropΠ (λ x → isPropΠ λ y → isProp→ (isPropValuedRel y x)))
    (isPropΠ λ x → isPropΠ λ y → isPropΠ λ z → isProp→ (isProp→ (isPropValuedRel x z)))

record PER : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor makePER
  field
    relation : A → A → Type ℓ
    isPropValuedRelation : ∀ x y → isProp (relation x y)
    isPER : isPartialEquivalenceRelation (relation , isPropValuedRelation)
  isSymmetric = isPER .fst
  isTransitive = isPER .snd

open PER

PERΣ : Type (ℓ-suc ℓ)
PERΣ = Σ[ relation ∈ (A → A → hProp ℓ) ] isPartialEquivalenceRelation ((λ a b → ⟨ relation a b ⟩) , λ a b → str (relation a b))

IsoPERΣPER : Iso PERΣ PER
PER.relation (Iso.fun IsoPERΣPER (relation , isPER)) x y = ⟨ relation x y ⟩
PER.isPropValuedRelation (Iso.fun IsoPERΣPER (relation , isPER)) x y = str (relation x y)
PER.isPER (Iso.fun IsoPERΣPER (relation , isPER)) = isPER
Iso.inv IsoPERΣPER per = (λ x y → per .relation x y , per .isPropValuedRelation x y) , (isSymmetric per) , (isTransitive per)
-- refl does not work because of no-eta-equality maybe?
relation (Iso.rightInv IsoPERΣPER per i) = λ a b → per .relation a b
isPropValuedRelation (Iso.rightInv IsoPERΣPER per i) = λ a b → per .isPropValuedRelation a b
isPER (Iso.rightInv IsoPERΣPER per i) = (isSymmetric per) , (isTransitive per)
Iso.leftInv IsoPERΣPER perΣ =
  Σ≡Prop
    (λ x → isPropIsPartialEquivalenceRelation ((λ a b → ⟨ x a b ⟩) , (λ a b → str (x a b))))
    (funExt₂ λ a b → Σ≡Prop (λ x → isPropIsProp) refl)

PERΣ≃PER : PERΣ ≃ PER
PERΣ≃PER = isoToEquiv IsoPERΣPER

isSetPERΣ : isSet PERΣ
isSetPERΣ = isSetΣ (isSet→ (isSet→ isSetHProp)) (λ rel → isProp→isSet (isPropIsPartialEquivalenceRelation ((λ a b → ⟨ rel a b ⟩) , (λ a b → str (rel a b)))))

isSetPER : isSet PER
isSetPER = isOfHLevelRespectEquiv 2 PERΣ≃PER isSetPERΣ

module ResizedPER (resizing : hPropResizing ℓ) where
  private
    smallHProp = resizing .fst
    hProp≃smallHProp = resizing .snd
    smallHProp≃hProp = invEquiv hProp≃smallHProp

  ResizedPER : Type ℓ
  ResizedPER = Σ[ relation ∈ (A → A → smallHProp) ] isPartialEquivalenceRelation ((λ a b → ⟨ equivFun (smallHProp≃hProp) (relation a b) ⟩) , λ a b → str (equivFun (smallHProp≃hProp) (relation a b)))

  PERΣ≃ResizedPER : PERΣ ≃ ResizedPER
  PERΣ≃ResizedPER =
    Σ-cong-equiv-prop
      (equiv→ (idEquiv A) (equiv→ (idEquiv A) hProp≃smallHProp))
      (λ relation → isPropIsPartialEquivalenceRelation ((λ a b → ⟨ relation a b ⟩) , (λ a b → str (relation a b))))
      (λ resizedRelation → isPropIsPartialEquivalenceRelation ((λ a b → ⟨ equivFun (smallHProp≃hProp) (resizedRelation a b) ⟩) , λ a b → str (equivFun smallHProp≃hProp (resizedRelation a b))))
      (λ relation isPERRelation → (λ a b aRb → {!!}) , λ a b c aRb bRc → {!!})
      λ relation isPERRelation → {!!}

  PER≃ResizedPER : PER ≃ ResizedPER
  PER≃ResizedPER = compEquiv (invEquiv PERΣ≃PER) PERΣ≃ResizedPER
