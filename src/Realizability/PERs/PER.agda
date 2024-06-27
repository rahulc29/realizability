open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
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
open import Cubical.Data.Vec
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (Id)

module Realizability.PERs.PER
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module BR = BinaryRelation

isPartialEquivalenceRelation : (A → A → Type ℓ) → Type _
isPartialEquivalenceRelation rel = BR.isSym rel × BR.isTrans rel

isPropIsPartialEquivalenceRelation : ∀ r → (∀ a b → isProp (r a b)) → isProp (isPartialEquivalenceRelation r)
isPropIsPartialEquivalenceRelation rel isPropValuedRel =
  isProp×
    (isPropΠ (λ x → isPropΠ λ y → isProp→ (isPropValuedRel y x)))
    (isPropΠ λ x → isPropΠ λ y → isPropΠ λ z → isProp→ (isProp→ (isPropValuedRel x z)))

record PER : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor makePER
  field
    relation : A → A → Type ℓ
    isPropValued : ∀ a b → isProp (relation a b)
    isPER : isPartialEquivalenceRelation relation
  isSymmetric = isPER .fst
  isTransitive = isPER .snd

open PER

PERΣ : Type (ℓ-suc ℓ)
PERΣ = Σ[ relation ∈ (A → A → hProp ℓ) ] isPartialEquivalenceRelation λ a b → ⟨ relation a b ⟩

isSetPERΣ : isSet PERΣ
isSetPERΣ =
  isSetΣ
    (isSet→ (isSet→ isSetHProp))
    (λ relation →
      isProp→isSet
        (isPropIsPartialEquivalenceRelation
          (λ a b → ⟨ relation a b ⟩)
          (λ a b → str (relation a b))))

PER≡ : ∀ (R S : PER) → (R .relation ≡ S .relation) → R ≡ S
relation (PER≡ R S rel≡ i) = rel≡ i
isPropValued (PER≡ R S rel≡ i) a b =
  isProp→PathP
    {B = λ j → isProp (rel≡ j a b)}
    (λ j → isPropIsProp)
    (R .isPropValued a b)
    (S .isPropValued a b) i
isPER (PER≡ R S rel≡ i) =
  isProp→PathP
    {B = λ j → isPartialEquivalenceRelation (rel≡ j)}
    (λ j → isPropIsPartialEquivalenceRelation (rel≡ j) λ a b → isPropRelJ a b j)
    (R .isPER)
    (S .isPER) i where
      isPropRelJ : ∀ a b j → isProp (rel≡ j a b)
      isPropRelJ a b j = isProp→PathP {B = λ k → isProp (rel≡ k a b)} (λ k → isPropIsProp) (R .isPropValued a b) (S .isPropValued a b) j

PERIsoΣ : Iso PER PERΣ
Iso.fun PERIsoΣ per = (λ a b → per .relation a b , per .isPropValued a b) , per .isPER
relation (Iso.inv PERIsoΣ perΣ) a b = ⟨ perΣ .fst a b ⟩
isPropValued (Iso.inv PERIsoΣ perΣ) a b = str (perΣ .fst a b)
isPER (Iso.inv PERIsoΣ perΣ) = perΣ .snd
Iso.rightInv PERIsoΣ perΣ = refl
Iso.leftInv PERIsoΣ per = PER≡ _ _ refl

isSetPER : isSet PER
isSetPER = isOfHLevelRetractFromIso 2 PERIsoΣ isSetPERΣ

PER≡Iso : ∀ (R S : PER) → Iso (R ≡ S) (R .relation ≡ S .relation)
Iso.fun (PER≡Iso R S) R≡S i = R≡S i .relation
Iso.inv (PER≡Iso R S) rel≡ = PER≡ R S rel≡
Iso.rightInv (PER≡Iso R S) rel≡ = refl
Iso.leftInv (PER≡Iso R S) R≡S = isSetPER R S _ _

_~[_]_ : A → PER → A → Type ℓ
a ~[ R ] b = R .relation a b

isProp~ : ∀ a R b → isProp (a ~[ R ] b)
isProp~ a R b = R .isPropValued a b

isTracker : (R S : PER) → A → Type ℓ
isTracker R S a = ∀ r r' → r ~[ R ] r' → (a ⨾ r) ~[ S ] (a ⨾ r')

perTracker : (R S : PER) → Type ℓ
perTracker R S = Σ[ a ∈ A ] isTracker R S a

isEquivTracker : (R S : PER) → perTracker R S → perTracker R S → Type ℓ
isEquivTracker R S (a , _) (b , _) = (∀ r → r ~[ R ] r → (a ⨾ r) ~[ S ] (b ⨾ r))

isEquivRelIsEquivTracker : (R S : PER) → BR.isEquivRel (isEquivTracker R S)
BinaryRelation.isEquivRel.reflexive (isEquivRelIsEquivTracker R S) (a , isTrackerA) r r~r = isTrackerA r r r~r
BinaryRelation.isEquivRel.symmetric (isEquivRelIsEquivTracker R S) (a , isTrackerA) (b , isTrackerB) a~b r r~r =
  isSymmetric S (a ⨾ r) (b ⨾ r) (a~b r r~r)
BinaryRelation.isEquivRel.transitive (isEquivRelIsEquivTracker R S) (a , isTrackerA) (b , isTrackerB) (c , isTrackerC) a~b b~c r r~r =
  isTransitive S (a ⨾ r) (b ⨾ r) (c ⨾ r) (a~b r r~r) (b~c r r~r)

isPropIsEquivTracker : ∀ R S a b → isProp (isEquivTracker R S a b)
isPropIsEquivTracker R S (a , isTrackerA) (b , isTrackerB) = isPropΠ2 λ r r~r → isPropValued S (a ⨾ r) (b ⨾ r)

isEffectiveIsEquivTracker : ∀ R S → BR.isEffective (isEquivTracker R S)
isEffectiveIsEquivTracker R S = isEquivRel→isEffective (isPropIsEquivTracker R S) (isEquivRelIsEquivTracker R S)

perMorphism : (R S : PER) → Type ℓ
perMorphism R S = perTracker R S / (isEquivTracker R S)

effectiveIsEquivTracker : ∀ R S a b → [ a ] ≡ [ b ] → isEquivTracker R S a b
effectiveIsEquivTracker R S a b eq' = effective (isPropIsEquivTracker R S) (isEquivRelIsEquivTracker R S) a b eq'

isSetPerMorphism : ∀ R S → isSet (perMorphism R S)
isSetPerMorphism R S = squash/

idPerMorphism : (R : PER) → perMorphism R R
idPerMorphism R = [ Id , (λ r r' r~r' → subst2 (λ r r' → r ~[ R ] r') (sym (Ida≡a r)) (sym (Ida≡a r')) r~r') ]

composePerTracker : (R S T : PER) → perTracker R S → perTracker S T → perTracker R T
composePerTracker R S T (a , a⊩f) (b , b⊩g) =
  let
    realizer : Term as 1
    realizer = ` b ̇ (` a ̇ # zero)
  in
  λ* realizer ,
  λ r r' r~r' →
    subst2
      _~[ T ]_
      (sym (λ*ComputationRule realizer r))
      (sym (λ*ComputationRule realizer r'))
      (b⊩g (a ⨾ r) (a ⨾ r') (a⊩f r r' r~r'))

composePerMorphism : (R S T : PER) → perMorphism R S → perMorphism S T → perMorphism R T
composePerMorphism R S T f g =
  SQ.rec2
    squash/
    (λ { (a , a⊩f) (b , b⊩g) →
      [ composePerTracker R S T (a , a⊩f) (b , b⊩g) ] })
    (λ { (a , a⊩f) (b , b⊩f) (c , c⊩g) a~b →
      eq/ _ _
        λ r r~r →
          subst2
            (λ car cbr → car ~[ T ] cbr)
            (sym (λ*ComputationRule (` c ̇ (` a ̇ # zero)) r))
            (sym (λ*ComputationRule (` c ̇ (` b ̇ # zero)) r))
            (c⊩g (a ⨾ r) (b ⨾ r) (a~b r r~r)) })
    (λ { (a , a⊩f) (b , b⊩g) (c , c⊩g) b~c →
      eq/ _ _
        λ r r~r →
          subst2
            (λ bar car → bar ~[ T ] car)
            (sym (λ*ComputationRule (` b ̇ (` a ̇ # zero)) r))
            (sym (λ*ComputationRule (` c ̇ (` a ̇ # zero)) r))
            (b~c (a ⨾ r) (a⊩f r r r~r)) })
    f g

idLPerMorphism : ∀ R S f → composePerMorphism R R S (idPerMorphism R) f ≡ f
idLPerMorphism R S f =
  SQ.elimProp
    (λ f → squash/ (composePerMorphism R R S (idPerMorphism R) f) f)
    (λ { (a , a⊩f) →
      eq/ _ _
      λ r r~r →
        subst
          (λ ar → ar ~[ S ] (a ⨾ r))
          (sym (λ*ComputationRule (` a ̇ (` Id ̇ # zero)) r ∙ cong (λ x → a ⨾ x) (Ida≡a r)))
          (a⊩f r r r~r) })
    f

idRPerMorphism : ∀ R S f → composePerMorphism R S S f (idPerMorphism S) ≡ f
idRPerMorphism R S f =
  SQ.elimProp
    (λ f → squash/ (composePerMorphism R S S f (idPerMorphism S)) f)
    (λ { (a , a⊩f) →
      eq/ _ _
        λ r r~r →
          subst (λ ar → ar ~[ S ] (a ⨾ r)) (sym (λ*ComputationRule (` Id ̇ (` a ̇ # zero)) r ∙ Ida≡a (a ⨾ r))) (a⊩f r r r~r) })
    f

assocPerMorphism : ∀ R S T U f g h → composePerMorphism R T U (composePerMorphism R S T f g) h ≡ composePerMorphism R S U f (composePerMorphism S T U g h)
assocPerMorphism R S T U f g h =
  SQ.elimProp3
    (λ f g h → squash/ (composePerMorphism R T U (composePerMorphism R S T f g) h) (composePerMorphism R S U f (composePerMorphism S T U g h)))
    (λ { (a , a⊩f) (b , b⊩g) (c , c⊩h) →
      eq/ _ _
        λ r r~r →
          subst2
            (λ cba cba' → cba ~[ U ] cba')
            (sym (λ*ComputationRule (` c ̇ (` ⟦ as ⟧ (λ*abst (` b ̇ (` a ̇ # zero))) []  ̇ # zero)) r ∙ cong (λ bar → c ⨾ bar) (λ*ComputationRule (` b ̇ (` a ̇ # zero)) r)))
            (sym (λ*ComputationRule (` ⟦ as ⟧ (λ*abst (` c ̇ (` b ̇ # zero))) [] ̇ (` a ̇ # zero)) r ∙ λ*ComputationRule (` c ̇ (` b ̇ # zero)) (a ⨾ r)))
            (c⊩h (b ⨾ (a ⨾ r)) (b ⨾ (a ⨾ r)) (b⊩g (a ⨾ r) (a ⨾ r) (a⊩f r r r~r)) ) })
    f g h

PERCat : Category (ℓ-suc ℓ) ℓ
Category.ob PERCat = PER
Category.Hom[_,_] PERCat R S = perMorphism R S
Category.id PERCat {R} = idPerMorphism R
Category._⋆_ PERCat {R} {S} {T} f g = composePerMorphism R S T f g
Category.⋆IdL PERCat {R} {S} f = idLPerMorphism R S f
Category.⋆IdR PERCat {R} {S} f = idRPerMorphism R S f
Category.⋆Assoc PERCat {R} {S} {T} {U} f g h = assocPerMorphism R S T U f g h
Category.isSetHom PERCat {R} {S} = isSetPerMorphism R S
