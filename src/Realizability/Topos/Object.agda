open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Reflection.RecordEquiv

module Realizability.Topos.Object
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where
  
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

record isPartialEquivalenceRelation (X : Type ℓ') (equality : Predicate (X × X)) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
    isSymmetric : ∃[ s ∈ A ] (∀ x y r → r ⊩ ∣ equality ∣ (x , y) → (s ⨾ r) ⊩ ∣ equality ∣ (y , x))
    isTransitive : ∃[ t ∈ A ] (∀ x y z a b → a ⊩ ∣ equality ∣ (x , y) → b ⊩ ∣ equality ∣ (y , z) → (t ⨾ a ⨾ b) ⊩ ∣ equality ∣ (x , z))

open isPartialEquivalenceRelation
isPropIsPartialEquivalenceRelation : ∀ {X : Type ℓ'} → (equality : Predicate (X × X)) → isProp (isPartialEquivalenceRelation X equality)
isPropIsPartialEquivalenceRelation {X} equality x y i =
  record { isSetX = isProp→PathP (λ i → isPropIsSet) (x .isSetX) (y .isSetX) i ; isSymmetric = squash₁ (x .isSymmetric) (y .isSymmetric) i ; isTransitive = squash₁ (x .isTransitive) (y .isTransitive) i }

record PartialEquivalenceRelation (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    equality : Predicate (X × X)
    isPerEquality : isPartialEquivalenceRelation X equality
  open isPartialEquivalenceRelation isPerEquality public

-- Directly from previous commit
unquoteDecl PartialEquivalenceRelationIsoΣ = declareRecordIsoΣ PartialEquivalenceRelationIsoΣ (quote PartialEquivalenceRelation)

PartialEquivalenceRelationΣ : (X : Type ℓ') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
PartialEquivalenceRelationΣ X = Σ[ equality ∈ Predicate (X × X) ] isPartialEquivalenceRelation X equality

open PartialEquivalenceRelation
module _ (X : Type ℓ') where opaque
  open Iso
  PartialEquivalenceRelationΣ≡ : (perA perB : PartialEquivalenceRelationΣ X) → perA .fst ≡ perB .fst → perA ≡ perB
  PartialEquivalenceRelationΣ≡ perA perB predicateEq = Σ≡Prop (λ x → isPropIsPartialEquivalenceRelation x) predicateEq 

  PartialEquivalenceRelationΣ≃ : (perA perB : PartialEquivalenceRelationΣ X) → (perA .fst ≡ perB .fst) ≃ (perA ≡ perB)
  PartialEquivalenceRelationΣ≃ perA perB = Σ≡PropEquiv λ x → isPropIsPartialEquivalenceRelation x

  PartialEquivalenceRelationIso : (perA perB : PartialEquivalenceRelation X) → Iso (Iso.fun PartialEquivalenceRelationIsoΣ perA ≡ Iso.fun PartialEquivalenceRelationIsoΣ perB) (perA ≡ perB)
  Iso.fun (PartialEquivalenceRelationIso perA perB) p i = Iso.inv PartialEquivalenceRelationIsoΣ (p i)
  inv (PartialEquivalenceRelationIso perA perB) = cong (λ x → Iso.fun PartialEquivalenceRelationIsoΣ x)
  rightInv (PartialEquivalenceRelationIso perA perB) b = refl
  leftInv (PartialEquivalenceRelationIso perA perB) a = refl

  -- Main SIP
  PartialEquivalenceRelation≃ : (perA perB : PartialEquivalenceRelation X) → (perA .equality ≡ perB .equality) ≃ (perA ≡ perB)
  PartialEquivalenceRelation≃ perA perB =
    perA .equality ≡ perB .equality
      ≃⟨ idEquiv (perA .equality ≡ perB .equality) ⟩
    Iso.fun PartialEquivalenceRelationIsoΣ perA .fst ≡ Iso.fun PartialEquivalenceRelationIsoΣ perB .fst
      ≃⟨ PartialEquivalenceRelationΣ≃ (Iso.fun PartialEquivalenceRelationIsoΣ perA) (Iso.fun PartialEquivalenceRelationIsoΣ perB) ⟩
    Iso.fun PartialEquivalenceRelationIsoΣ perA ≡ Iso.fun PartialEquivalenceRelationIsoΣ perB
      ≃⟨ isoToEquiv (PartialEquivalenceRelationIso perA perB) ⟩
    perA ≡ perB
      ■
