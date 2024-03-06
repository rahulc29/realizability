{-# OPTIONS --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Tripoi.PosetReflection
open import Tripoi.HeytingAlgebra
open import Realizability.ApplicativeStructure renaming (λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Fin
open import Cubical.Data.Sum renaming (rec to sumRec)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ renaming (rec to quotRec; rec2 to quotRec2)
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

module Realizability.Tripos.Algebra.Base {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
import Realizability.Tripos.Prealgebra.Predicate ca as Pred
open import Realizability.Tripos.Prealgebra.Joins.Commutativity ca
open import Realizability.Tripos.Prealgebra.Joins.Identity ca
open import Realizability.Tripos.Prealgebra.Joins.Idempotency ca
open import Realizability.Tripos.Prealgebra.Joins.Associativity ca
open import Realizability.Tripos.Prealgebra.Meets.Commutativity ca
open import Realizability.Tripos.Prealgebra.Meets.Identity ca
open import Realizability.Tripos.Prealgebra.Meets.Idempotency ca
open import Realizability.Tripos.Prealgebra.Meets.Associativity ca
open import Realizability.Tripos.Prealgebra.Absorbtion ca

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure

AlgebraicPredicate : Type ℓ' → Type _
AlgebraicPredicate X = PosetReflection (Pred.PredicateProperties._≤_ {ℓ'' = ℓ''} X)

infixl 50 _⊩[_]_
opaque
  realizes : ∀ {X : Type ℓ'} → A → AlgebraicPredicate X → X → hProp (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  realizes {X} r ϕ x =
    SQ.rec
        isSetHProp
        (λ Ψ → (∃[ s ∈ A ] Pred.Predicate.∣ Ψ ∣ x (s ⨾ r)) , isPropPropTrunc)
        (λ { Ψ Ξ (Ψ≤Ξ , Ξ≤Ψ) →
          Σ≡Prop
            (λ _ → isPropIsProp)
            (hPropExt isPropPropTrunc isPropPropTrunc
              (λ Ψholds →
                do
                  (s , s⊩Ψ≤Ξ) ← Ψ≤Ξ
                  (p , p⊩Ψ) ← Ψholds
                  let
                    prover : Term as 1
                    prover = ` s ̇ (` p ̇ # fzero)
                  return (λ* prover , subst (λ r' → Pred.Predicate.∣ Ξ ∣ x r') (sym (λ*ComputationRule prover (r ∷ []))) (s⊩Ψ≤Ξ x (p ⨾ r) p⊩Ψ)))
              (λ Ξholds →
                do
                  (s , s⊩Ξ≤Ψ) ← Ξ≤Ψ
                  (p , p⊩Ξ) ← Ξholds
                  let
                    prover : Term as 1
                    prover = ` s ̇ (` p ̇ # fzero)
                  return (λ* prover , subst (λ r' → Pred.Predicate.∣ Ψ ∣ x r') (sym (λ*ComputationRule prover (r ∷ []))) (s⊩Ξ≤Ψ x (p ⨾ r) p⊩Ξ)))) })
        ϕ

  _⊩[_]_ : ∀ {X : Type ℓ'} → A → AlgebraicPredicate X → X → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  r ⊩[ ϕ ] x = ⟨ realizes r ϕ x ⟩

  isProp⊩ : ∀ {X : Type ℓ'} → (a : A) → (ϕ : AlgebraicPredicate X) → (x : X) → isProp (a ⊩[ ϕ ] x)
  isProp⊩ {X} a ϕ x = realizes a ϕ x .snd

  transformRealizes : ∀ {X : Type ℓ'} → (r : A) → (ϕ : Pred.Predicate X) → (x : X) → (∃[ s ∈ A ] (s ⨾ r) ⊩[ [ ϕ ] ] x) → r ⊩[ [ ϕ ] ] x
  transformRealizes {X} r ϕ x ∃ =
    do
      (s , s⊩ϕx) ← ∃
      (p , ps⊩ϕx) ← s⊩ϕx
      let
        prover : Term as 1
        prover = ` p ̇ (` s ̇ # fzero)
      return (λ* prover , subst (λ r' → Pred.Predicate.∣ ϕ ∣ x r') (sym (λ*ComputationRule prover (r ∷ []))) ps⊩ϕx)

module AlgebraicProperties (X : Type ℓ') (isSetX' : isSet X) (isNonTrivial : s ≡ k → ⊥) where
  open Pred
  private PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  open PredicateProperties {ℓ'' = ℓ''} X
  open Tripoi.PosetReflection.Properties _≤_ (PreorderStr.isPreorder (preorder≤ .snd))
  PredicateAlgebra = PosetReflection _≤_
  open PreorderReasoning preorder≤
  open PreorderStr (preorder≤ .snd) renaming (is-trans to isTrans)

  _∨l_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a ∨l b =
    quotRec2
      squash/
      (λ x y → [ x ⊔ y ])
      (λ x y z (x≤y , y≤x) → eq/ (x ⊔ z) (y ⊔ z) (antiSym→x⊔z≤y⊔z X isSetX' x y z x≤y y≤x , antiSym→x⊔z≤y⊔z X isSetX' y x z y≤x x≤y))
      (λ x y z (y≤z , z≤y) →
        let
          I : x ⊔ y ≤ y ⊔ x
          I = a⊔b→b⊔a X isSetX' x y
          II : y ⊔ x ≤ z ⊔ x
          II = antiSym→x⊔z≤y⊔z X isSetX' y z x y≤z z≤y
          III : z ⊔ x ≤ x ⊔ z
          III = a⊔b→b⊔a X isSetX' z x
          IV : x ⊔ z ≤ z ⊔ x
          IV = a⊔b→b⊔a X isSetX' x z
          V : z ⊔ x ≤ y ⊔ x
          V = antiSym→x⊔z≤y⊔z X isSetX' z y x z≤y y≤z
          VI : y ⊔ x ≤ x ⊔ y
          VI = a⊔b→b⊔a X isSetX' y x
        in
        eq/ (x ⊔ y) (x ⊔ z)
          -- TODO : not use preorder reasoning
          ((x ⊔ y
              ≲⟨ I ⟩
             y ⊔ x
              ≲⟨ II ⟩
             z ⊔ x
              ≲⟨ III ⟩ (
             x ⊔ z ◾)) ,
          (x ⊔ z
            ≲⟨ IV ⟩
           z ⊔ x
            ≲⟨ V ⟩
           y ⊔ x
            ≲⟨ VI ⟩
           x ⊔ y
            ◾)))
      a b

  open SemigroupStr
  PredicateAlgebra∨SemigroupStr : SemigroupStr PredicateAlgebra
  SemigroupStr._·_ PredicateAlgebra∨SemigroupStr = _∨l_
  IsSemigroup.is-set (isSemigroup PredicateAlgebra∨SemigroupStr) = squash/
  IsSemigroup.·Assoc (isSemigroup PredicateAlgebra∨SemigroupStr) x y z =
    elimProp3
      (λ x y z → squash/ (x ∨l (y ∨l z)) ((x ∨l y) ∨l z))
      (λ x y z →
        eq/
          (x ⊔ (y ⊔ z)) ((x ⊔ y) ⊔ z)
          (x⊔_y⊔z≤x⊔y_⊔z X isSetX' isNonTrivial x y z ,
          x⊔y_⊔z≤x⊔_y⊔z X isSetX' isNonTrivial x y z))
      x y z

  private pre0' = pre0 {ℓ'' = ℓ''} X isSetX' isNonTrivial
  
  0predicate : PredicateAlgebra
  0predicate = [ pre0' ]
  

  PredicateAlgebra∨MonoidStr : MonoidStr PredicateAlgebra
  MonoidStr.ε PredicateAlgebra∨MonoidStr = 0predicate
  MonoidStr._·_ PredicateAlgebra∨MonoidStr = _∨l_
  IsMonoid.isSemigroup (MonoidStr.isMonoid PredicateAlgebra∨MonoidStr) = PredicateAlgebra∨SemigroupStr .isSemigroup
  IsMonoid.·IdR (MonoidStr.isMonoid PredicateAlgebra∨MonoidStr) x =
    elimProp
      (λ x → squash/ (x ∨l 0predicate) x)
      (λ x →
        eq/
          (x ⊔ pre0') x
          ((x⊔0≤x X isSetX' isNonTrivial x) , x≤x⊔0 X isSetX' isNonTrivial x)) x
  IsMonoid.·IdL (MonoidStr.isMonoid PredicateAlgebra∨MonoidStr) x =
    elimProp
      (λ x → squash/ (0predicate ∨l x) x)
      (λ x →
        eq/
          (pre0' ⊔ x) x
          ((0⊔x≤x X isSetX' isNonTrivial x) , x≤0⊔x X isSetX' isNonTrivial x)) x

  PredicateAlgebra∨CommMonoidStr : CommMonoidStr PredicateAlgebra
  CommMonoidStr.ε PredicateAlgebra∨CommMonoidStr = 0predicate
  CommMonoidStr._·_ PredicateAlgebra∨CommMonoidStr = _∨l_
  IsCommMonoid.isMonoid (CommMonoidStr.isCommMonoid PredicateAlgebra∨CommMonoidStr) = MonoidStr.isMonoid PredicateAlgebra∨MonoidStr
  IsCommMonoid.·Comm (CommMonoidStr.isCommMonoid PredicateAlgebra∨CommMonoidStr) x y =
    elimProp2 (λ x y → squash/ (x ∨l y) (y ∨l x)) (λ x y → eq/ (x ⊔ y) (y ⊔ x) ((a⊔b→b⊔a X isSetX' x y) , (a⊔b→b⊔a X isSetX' y x))) x y

  PredicateAlgebra∨SemilatticeStr : SemilatticeStr PredicateAlgebra
  SemilatticeStr.ε PredicateAlgebra∨SemilatticeStr = 0predicate
  SemilatticeStr._·_ PredicateAlgebra∨SemilatticeStr = _∨l_
  IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice PredicateAlgebra∨SemilatticeStr) = CommMonoidStr.isCommMonoid PredicateAlgebra∨CommMonoidStr
  IsSemilattice.idem (SemilatticeStr.isSemilattice PredicateAlgebra∨SemilatticeStr) x =
    elimProp
      (λ x → squash/ (x ∨l x) x)
      (λ x → eq/ (x ⊔ x) x ((x⊔x≤x X isSetX' isNonTrivial x) , (x≤x⊔x X isSetX' isNonTrivial x)))
      x


  _∧l_ : PredicateAlgebra → PredicateAlgebra → PredicateAlgebra
  a ∧l b =
    quotRec2
      squash/
      (λ a b → [ a ⊓ b ])
      (λ { a b c (a≤b , b≤a) → eq/ (a ⊓ c) (b ⊓ c) ((antiSym→x⊓z≤y⊓z X isSetX' a b c a≤b b≤a) , (antiSym→x⊓z≤y⊓z X isSetX' b a c b≤a a≤b)) })
      (λ { a b c (b≤c , c≤b) → eq/ (a ⊓ b) (a ⊓ c) (antiSym→x⊓y≤x⊓z X isSetX' a b c b≤c c≤b , antiSym→x⊓y≤x⊓z X isSetX' a c b c≤b b≤c) })
      a b

  PredicateAlgebra∧SemigroupStr : SemigroupStr PredicateAlgebra
  _·_ PredicateAlgebra∧SemigroupStr = _∧l_
  IsSemigroup.is-set (isSemigroup PredicateAlgebra∧SemigroupStr) = squash/
  IsSemigroup.·Assoc (isSemigroup PredicateAlgebra∧SemigroupStr) x y z =
    elimProp3
      (λ x y z → squash/ (x ∧l (y ∧l z)) ((x ∧l y) ∧l z))
      (λ x y z → eq/ (x ⊓ (y ⊓ z)) ((x ⊓ y) ⊓ z) ((x⊓_y⊓z≤x⊓y_⊓z X isSetX' isNonTrivial x y z) , (x⊓y_⊓z≤x⊓_y⊓z X isSetX' isNonTrivial x y z)))
      x y z

  private pre1' = pre1 {ℓ'' = ℓ''} X isSetX' isNonTrivial

  1predicate : PredicateAlgebra
  1predicate = [ pre1' ]

  PredicateAlgebra∧MonoidStr : MonoidStr PredicateAlgebra
  MonoidStr.ε PredicateAlgebra∧MonoidStr = 1predicate
  MonoidStr._·_ PredicateAlgebra∧MonoidStr = _∧l_
  IsMonoid.isSemigroup (MonoidStr.isMonoid PredicateAlgebra∧MonoidStr) = PredicateAlgebra∧SemigroupStr .isSemigroup
  IsMonoid.·IdR (MonoidStr.isMonoid PredicateAlgebra∧MonoidStr) x =
    elimProp (λ x → squash/ (x ∧l 1predicate) x) (λ x → eq/ (x ⊓ pre1') x ((x⊓1≤x X isSetX' isNonTrivial x) , (x≤x⊓1 X isSetX' isNonTrivial x))) x
  IsMonoid.·IdL (MonoidStr.isMonoid PredicateAlgebra∧MonoidStr) x =
    elimProp (λ x → squash/ (1predicate ∧l x) x) (λ x → eq/ (pre1' ⊓ x) x (1⊓x≤x X isSetX' isNonTrivial x , x≤1⊓x X isSetX' isNonTrivial x)) x

  PredicateAlgebra∧CommMonoidStr : CommMonoidStr PredicateAlgebra
  CommMonoidStr.ε PredicateAlgebra∧CommMonoidStr = 1predicate
  CommMonoidStr._·_ PredicateAlgebra∧CommMonoidStr = _∧l_
  IsCommMonoid.isMonoid (CommMonoidStr.isCommMonoid PredicateAlgebra∧CommMonoidStr) = MonoidStr.isMonoid PredicateAlgebra∧MonoidStr
  IsCommMonoid.·Comm (CommMonoidStr.isCommMonoid PredicateAlgebra∧CommMonoidStr) x y =
    elimProp2 (λ x y → squash/ (x ∧l y) (y ∧l x)) (λ x y → eq/ (x ⊓ y) (y ⊓ x) ((x⊓y≤y⊓x X isSetX' x y) , (x⊓y≤y⊓x X isSetX' y x))) x y

  PredicateAlgebra∧SemilatticeStr : SemilatticeStr PredicateAlgebra
  SemilatticeStr.ε PredicateAlgebra∧SemilatticeStr = 1predicate
  SemilatticeStr._·_ PredicateAlgebra∧SemilatticeStr = _∧l_
  IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice PredicateAlgebra∧SemilatticeStr) = CommMonoidStr.isCommMonoid PredicateAlgebra∧CommMonoidStr
  IsSemilattice.idem (SemilatticeStr.isSemilattice PredicateAlgebra∧SemilatticeStr) x =
    elimProp (λ x → squash/ (x ∧l x) x) (λ x → eq/ (x ⊓ x) x ((x⊓x≤x X isSetX' isNonTrivial x) , (x≤x⊓x X isSetX' isNonTrivial x))) x

  absorb∨ : ∀ x y → x ∨l (x ∧l y) ≡ x
  absorb∨ x y =
    elimProp2 (λ x y → squash/ (x ∨l (x ∧l y)) x) (λ x y → eq/ (x ⊔ (x ⊓ y)) x (absorb⊔≤x X isSetX' isNonTrivial x y , x≤absorb⊔ X isSetX' isNonTrivial x y)) x y

  absorb∧ : ∀ x y → x ∧l (x ∨l y) ≡ x
  absorb∧ x y =
    elimProp2 (λ x y → squash/ (x ∧l (x ∨l y)) x) (λ x y → eq/ (x ⊓ (x ⊔ y)) x (absorb⊓≤x X isSetX' isNonTrivial x y , x≤absorb⊓ X isSetX' isNonTrivial x y)) x y

  PredicateAlgebraLatticeStr : LatticeStr PredicateAlgebra
  LatticeStr.0l PredicateAlgebraLatticeStr = 0predicate
  LatticeStr.1l PredicateAlgebraLatticeStr = 1predicate
  LatticeStr._∨l_ PredicateAlgebraLatticeStr = _∨l_
  LatticeStr._∧l_ PredicateAlgebraLatticeStr = _∧l_
  IsLattice.joinSemilattice (LatticeStr.isLattice PredicateAlgebraLatticeStr) = SemilatticeStr.isSemilattice PredicateAlgebra∨SemilatticeStr
  IsLattice.meetSemilattice (LatticeStr.isLattice PredicateAlgebraLatticeStr) = SemilatticeStr.isSemilattice PredicateAlgebra∧SemilatticeStr
  IsLattice.absorb (LatticeStr.isLattice PredicateAlgebraLatticeStr) x y = absorb∨ x y , absorb∧ x y
  
