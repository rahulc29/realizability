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
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category

module Realizability.PERs.PER
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module BR = BinaryRelation

isPartialEquivalenceRelation : PropRel A A ℓ → Type _
isPartialEquivalenceRelation (rel , isPropValuedRel) = BR.isSym rel × BR.isTrans rel

isPropIsPartialEquivalenceRelation : ∀ r → isProp (isPartialEquivalenceRelation r)
isPropIsPartialEquivalenceRelation (rel , isPropValuedRel) =
  isProp×
    (isPropΠ (λ x → isPropΠ λ y → isProp→ (isPropValuedRel y x)))
    (isPropΠ λ x → isPropΠ λ y → isPropΠ λ z → isProp→ (isProp→ (isPropValuedRel x z)))

record PER : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor makePER
  field
    relation : PropRel A A ℓ
    isPER : isPartialEquivalenceRelation relation
  ∣_∣ = relation .fst
  isSymmetric = isPER .fst
  isTransitive = isPER .snd
  isPropValued = relation .snd

open PER

module _ (R : PER) where
  Quotient = A / ∣ R ∣

  -- mimics the proof at Cubical.HITs.SetQuotients.Properties
  effectiveOnDomain : ∀ a b → ∣ R ∣ a a → [ a ] ≡ [ b ] → ∣ R ∣ a b
  effectiveOnDomain a b aRa [a]≡[b] = transport aRa≡aRb aRa where
    helper : Quotient → hProp _
    helper x =
      SQ.rec
        isSetHProp
        (λ c → (∣ R ∣ a c) , (isPropValued R a c))
        (λ c d cRd →
          Σ≡Prop
            (λ _ → isPropIsProp)
            (hPropExt
              (isPropValued R a c)
              (isPropValued R a d)
              (λ aRc → isTransitive R a c d aRc cRd)
              (λ aRd → isTransitive R a d c aRd (isSymmetric R c d cRd))))
        x

    aRa≡aRb : ∣ R ∣ a a ≡ ∣ R ∣ a b
    aRa≡aRb i = helper ([a]≡[b] i) .fst

record PERMorphism (R S : PER) : Type ℓ where
  no-eta-equality
  constructor makePERMorphism
  field
    map : Quotient R → Quotient S
    isTracked : ∃[ e ∈ A ] (∀ (a : A) → ∣ R ∣ a a → (map [ a ] ≡ [ e ⨾ a ]) × ∣ S ∣ (e ⨾ a) (e ⨾ a))

open PERMorphism

unquoteDecl PERMorphismIsoΣ = declareRecordIsoΣ PERMorphismIsoΣ (quote PERMorphism)

PERMorphismΣ : PER → PER → Type ℓ
PERMorphismΣ R S = Σ[ map ∈ (Quotient R → Quotient S) ] ∃[ e ∈ A ] (∀ (a : A) → ∣ R ∣ a a → (map [ a ] ≡ [ e ⨾ a ]) × ∣ S ∣ (e ⨾ a) (e ⨾ a))

isSetPERMorphismΣ : ∀ {R S} → isSet (PERMorphismΣ R S)
isSetPERMorphismΣ {R} {S} = isSetΣ (isSet→ squash/) (λ map → isProp→isSet isPropPropTrunc)

isSetPERMorphism : ∀ {R S} → isSet (PERMorphism R S)
isSetPERMorphism {R} {S} = subst (λ type → isSet type) (sym (isoToPath PERMorphismIsoΣ)) (isSetPERMorphismΣ {R = R} {S = S})

PERMorphism≡Iso : ∀ {R S} → (f g : PERMorphism R S) → Iso (f ≡ g) (f .map ≡ g .map)
Iso.fun (PERMorphism≡Iso {R} {S} f g) f≡g i = f≡g i .map
map (Iso.inv (PERMorphism≡Iso {R} {S} f g) fMap≡gMap i) = fMap≡gMap i
isTracked (Iso.inv (PERMorphism≡Iso {R} {S} f g) fMap≡gMap i) =
  isProp→PathP
    (λ i →
      isPropPropTrunc
      {A = Σ[ e ∈ A ] (∀ (a : A) → ∣ R ∣ a a → ((fMap≡gMap i) [ a ] ≡ [ e ⨾ a ]) × ∣ S ∣ (e ⨾ a) (e ⨾ a))})
    (f .isTracked) (g .isTracked) i
Iso.rightInv (PERMorphism≡Iso {R} {S} f g) fMap≡gMap = refl
Iso.leftInv (PERMorphism≡Iso {R} {S} f g) f≡g = isSetPERMorphism f g (Iso.inv (PERMorphism≡Iso f g) (λ i → f≡g i .map)) f≡g

PERMorphism≡ : ∀ {R S} → (f g : PERMorphism R S) → f .map ≡ g .map → f ≡ g
PERMorphism≡ {R} {S} f g fMap≡gMap = Iso.inv (PERMorphism≡Iso f g) fMap≡gMap

idPERMorphism : ∀ {R : PER} → PERMorphism R R
map (idPERMorphism {R}) x = x
isTracked (idPERMorphism {R}) =
  return (Id , (λ a aRa → (subst (λ r → [ a ] ≡ [ r ]) (sym (Ida≡a a)) refl) , (subst (λ r → ∣ R ∣ r r) (sym (Ida≡a a)) aRa)))

composePERMorphism : ∀ {R S T : PER} → PERMorphism R S → PERMorphism S T → PERMorphism R T
map (composePERMorphism {R} {S} {T} f g) x = g .map (f .map x)
isTracked (composePERMorphism {R} {S} {T} f g) =
  do
    (f~ , isTrackedF) ← f .isTracked
    (g~ , isTrackedG) ← g .isTracked
    let
      realizer : Term as 1
      realizer = ` g~ ̇ (` f~ ̇ # zero)
    return
      (λ* realizer ,
      (λ a aRa →
        (g .map (f .map [ a ])
          ≡⟨ cong (g .map) (isTrackedF a aRa .fst) ⟩
        g .map [ f~ ⨾ a ]
          ≡⟨ isTrackedG (f~ ⨾ a) (isTrackedF a aRa .snd) .fst ⟩
        [ g~ ⨾ (f~ ⨾ a) ]
          ≡⟨ cong [_] (sym (λ*ComputationRule realizer a)) ⟩
        [ λ* realizer ⨾ a ]
          ∎) ,
        (subst (λ r' → ∣ T ∣ r' r') (sym (λ*ComputationRule realizer a)) (isTrackedG (f~ ⨾ a) (isTrackedF a aRa .snd) .snd))))

-- all definitional
idLPERMorphism : ∀ {R S} → (f : PERMorphism R S) → composePERMorphism idPERMorphism f ≡ f
idLPERMorphism {R} {S} f = PERMorphism≡ _ _ refl

idRPERMorphism : ∀ {R S} → (f : PERMorphism R S) → composePERMorphism f idPERMorphism ≡ f
idRPERMorphism {R} {S} f = PERMorphism≡ _ _ refl

assocPERMorphism :
  ∀ {R S T U}
  → (f : PERMorphism R S)
  → (g : PERMorphism S T)
  → (h : PERMorphism T U)
  → composePERMorphism (composePERMorphism f g) h ≡ composePERMorphism f (composePERMorphism g h)
assocPERMorphism {R} {S} {T} {U} f g h = PERMorphism≡ _ _ refl

PERCat : Category (ℓ-suc ℓ) ℓ
Category.ob PERCat = PER
Category.Hom[_,_] PERCat R S = PERMorphism R S
Category.id PERCat {R} = idPERMorphism
Category._⋆_ PERCat {R} {S} {T} f g = composePERMorphism f g
Category.⋆IdL PERCat f = idLPERMorphism f
Category.⋆IdR PERCat f = idRPERMorphism f
Category.⋆Assoc PERCat f g h = assocPERMorphism f g h
Category.isSetHom PERCat = isSetPERMorphism
