open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; ⟦_⟧ to pre⟦_⟧)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Morphism
open import Realizability.PropResizing
open import Realizability.CombinatoryAlgebra

module Realizability.Topos.SubobjectClassifier
  {ℓ}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  (resizing : hPropResizing ℓ)
  where
  
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Topos.Object {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.Equalizer {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.BinProducts {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.MonicReprFuncRel {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.ResizedPredicate ca isNonTrivial resizing
open import Realizability.Topos.TerminalObject {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.StrictRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open Morphism
open PartialEquivalenceRelation
open FunctionalRelation
open Category RT

⟦_⟧ = pre⟦_⟧ as

Ωper : PartialEquivalenceRelation (ResizedPredicate Unit*)
Predicate.isSetX (equality Ωper) = isSet× isSetResizedPredicate isSetResizedPredicate
Predicate.∣ equality Ωper ∣ (α , β) r =
  (∀ (a : A) (⊩α : a ⊩ ∣ toPredicate α ∣ tt*) → ((pr₁ ⨾ r) ⨾ a) ⊩ ∣ toPredicate β ∣ tt*) ×
  (∀ (a : A) (⊩β : a ⊩ ∣ toPredicate β ∣ tt*) → ((pr₂ ⨾ r) ⨾ a) ⊩ ∣ toPredicate α ∣ tt*)
Predicate.isPropValued (equality Ωper) (α , β) r =
  isProp×
    (isPropΠ (λ _ → isPropΠ λ _ → (toPredicate β) .isPropValued _ _))
    (isPropΠ (λ _ → isPropΠ λ _ → (toPredicate α) .isPropValued _ _))
isPartialEquivalenceRelation.isSetX (isPerEquality Ωper) = isSetResizedPredicate
isPartialEquivalenceRelation.isSymmetric (isPerEquality Ωper) =
  do
    let
      ent₁ : ApplStrTerm as 2
      ent₁ = ` pr₂ ̇ # one ̇ # zero

      ent₂ : ApplStrTerm as 2
      ent₂ = ` pr₁ ̇ # one ̇ # zero

      realizer : ApplStrTerm as 1
      realizer = ` pair ̇ (λ*abst ent₁) ̇ (λ*abst ent₂)
    return
      (λ* realizer ,
      λ { α β r (pr₁r⊩α≤β , pr₂r⊩β≤α) →
        (λ a a⊩β →
          let
            eq : pr₁ ⨾ (λ* realizer ⨾ r) ⨾ a ≡ pr₂ ⨾ r ⨾ a
            eq =
              pr₁ ⨾ (λ* realizer ⨾ r) ⨾ a
                ≡⟨ cong (λ x → pr₁ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ⟩
              pr₁ ⨾ (pair ⨾ _ ⨾ _) ⨾ a
                ≡⟨ cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ⟩
              ⟦ (λ*abst ent₁) ⟧ (r ∷ []) ⨾ a
                ≡⟨ βreduction ent₁ a (r ∷ []) ⟩
              pr₂ ⨾ r ⨾ a
                ∎
          in
          subst (λ r' → r' ⊩ ∣ toPredicate α ∣ tt*) (sym eq) (pr₂r⊩β≤α a a⊩β)) ,
        (λ a a⊩α →
          let
            eq : pr₂ ⨾ (λ* realizer ⨾ r) ⨾ a ≡ pr₁ ⨾ r ⨾ a
            eq =
              pr₂ ⨾ (λ* realizer ⨾ r) ⨾ a
                ≡⟨ cong (λ x → pr₂ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ⟩
              pr₂ ⨾ (pair ⨾ _ ⨾ _) ⨾ a
                ≡⟨ cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ⟩
              ⟦ λ*abst ent₂ ⟧ (r ∷ []) ⨾ a
                ≡⟨ βreduction ent₂ a (r ∷ []) ⟩
              pr₁ ⨾ r ⨾ a
                ∎
          in
          subst (λ r' → r' ⊩ ∣ toPredicate β ∣ tt*) (sym eq) (pr₁r⊩α≤β a a⊩α)) })
isPartialEquivalenceRelation.isTransitive (isPerEquality Ωper) =
  do
    let
      closure1 : ApplStrTerm as 3
      closure1 = ` pr₁ ̇ # one ̇ (` pr₁ ̇ # two ̇ # zero)

      closure2 : ApplStrTerm as 3
      closure2 = ` pr₂ ̇ # two ̇ (` pr₂ ̇ # one ̇ # zero)

      realizer = ` pair ̇ (λ*abst closure1) ̇ (λ*abst closure2)
    return
      (λ*2 realizer ,
      (λ { x y z a b (⊩x≤y , ⊩y≤x) (⊩y≤z , ⊩z≤y) →
        (λ r r⊩x →
          subst
            (λ r' → r' ⊩ ∣ toPredicate z ∣ tt*)
            (sym
              (cong (λ x → pr₁ ⨾ x ⨾ r) (λ*2ComputationRule realizer a b) ∙
               cong (λ x → x ⨾ r) (pr₁pxy≡x _ _) ∙
               βreduction closure1 r (b ∷ a ∷ [])))
            (⊩y≤z _ (⊩x≤y r r⊩x))) ,
        (λ r r⊩z →
          subst
            (λ r' → r' ⊩ ∣ toPredicate x ∣ tt*)
            (sym
              (cong (λ x → pr₂ ⨾ x ⨾ r) (λ*2ComputationRule realizer a b) ∙
               cong (λ x → x ⨾ r) (pr₂pxy≡y _ _) ∙
               βreduction closure2 r (b ∷ a ∷ [])))
            (⊩y≤x _ (⊩z≤y r r⊩z))) }))

opaque
  unfolding terminalPer
  trueFuncRel : FunctionalRelation terminalPer Ωper
  Predicate.isSetX (relation trueFuncRel) = isSet× isSetUnit* isSetResizedPredicate
  Predicate.∣ relation trueFuncRel ∣ (tt* , p) r = ∀ (a : A) → (r ⨾ a) ⊩ ∣ toPredicate p ∣ tt*
  Predicate.isPropValued (relation trueFuncRel) (tt* , p) r = isPropΠ λ a → (toPredicate p) .isPropValued _ _
  isFunctionalRelation.isStrictDomain (isFuncRel trueFuncRel) =
    do
      return
        (k ,
        (λ { tt* y r r⊩⊤≤y → tt*}))
  isFunctionalRelation.isStrictCodomain (isFuncRel trueFuncRel) =
    do
      let
        idClosure : ApplStrTerm as 2
        idClosure = # zero
        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (λ*abst idClosure) ̇ (λ*abst idClosure)
      return
        (λ* realizer ,
        (λ { tt* y r r⊩⊤≤y →
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym
                (cong (λ x → pr₁ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ∙
                 cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ∙
                 βreduction idClosure a (r ∷ [])))
              a⊩y) ,
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym
                (cong (λ x → pr₂ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ∙
                 cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ∙
                 βreduction idClosure a (r ∷ [])))
              a⊩y)}))
  isFunctionalRelation.isRelational (isFuncRel trueFuncRel) =
    do
      let
        realizer : ApplStrTerm as 4
        realizer = ` pr₁ ̇ # one ̇ (# two  ̇ ` k)
      return
        (λ*4 realizer ,
        (λ { tt* tt* x y a b c tt* b⊩⊤≤x (pr₁c⊩x≤y , pr₂c⊩y≤x) r →
          subst
            (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
            (sym (λ*4ComputationRule realizer a b c r))
            (pr₁c⊩x≤y (b ⨾ k) (b⊩⊤≤x k))}))
  isFunctionalRelation.isSingleValued (isFuncRel trueFuncRel) =
    do
      let
        closure1 : ApplStrTerm as 3
        closure1 = # one ̇ ` k

        closure2 : ApplStrTerm as 3
        closure2 = # two ̇ ` k
        
        realizer : ApplStrTerm as 2
        realizer = ` pair ̇ (λ*abst closure1) ̇ (λ*abst closure2)
      return
        (λ*2 realizer ,
        (λ { tt* x y r₁ r₂ r₁⊩⊤≤x r₂⊩⊤≤y →
          (λ a a⊩x →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym
                (cong (λ x → pr₁ ⨾ x ⨾ a) (λ*2ComputationRule realizer r₁ r₂) ∙
                 cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ∙
                 βreduction closure1 a (r₂ ∷ r₁ ∷ [])))
              (r₂⊩⊤≤y k)) ,
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate x ∣ tt*)
              (sym
                (cong (λ x → pr₂ ⨾ x ⨾ a) (λ*2ComputationRule realizer r₁ r₂) ∙
                 cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ∙
                 βreduction closure2 a (r₂ ∷ r₁ ∷ [])))
              (r₁⊩⊤≤x k))}))
  isFunctionalRelation.isTotal (isFuncRel trueFuncRel) =
    do
      return
        (k ,
        (λ { tt* r tt* →
          let
            ⊤ = pre1 Unit* isSetUnit* isNonTrivial
          in
          ∣
            fromPredicate ⊤ ,
            (λ a →
              subst (λ p → (k ⨾ r ⨾ a) ⊩ ∣ p ∣ tt*) (sym (compIsIdFunc ⊤)) tt*)
          ∣₁ }))

opaque
  unfolding isInjectiveFuncRel
  unfolding terminalPer
  isInjectiveTrueFuncRel : isInjectiveFuncRel _ _ trueFuncRel
  isInjectiveTrueFuncRel =
    do
      return
        (k ,
        (λ { tt* tt* p r₁ r₂ r₁⊩⊤≤p r₂⊩⊤≤p → tt* }))

truePredicate : Predicate Unit*
Predicate.isSetX truePredicate = isSetUnit*
Predicate.∣ truePredicate ∣ tt* r = Unit*
Predicate.isPropValued truePredicate tt* r = isPropUnit*

⊤ = fromPredicate truePredicate

-- The subobject classifier classifies subobjects represented by strict relations
module ClassifiesStrictRelations
  (X : Type ℓ)
  (perX : PartialEquivalenceRelation X)
  (ϕ : StrictRelation perX) where

  open InducedSubobject perX ϕ
  open StrictRelation
  resizedϕ = fromPredicate (ϕ .predicate)

  -- the functional relation that represents the unique indicator map
  {-# TERMINATING #-}
  charFuncRel : FunctionalRelation perX Ωper
  Predicate.isSetX (relation charFuncRel) = isSet× (perX .isSetX) isSetResizedPredicate
  Predicate.∣ relation charFuncRel ∣ (x , p) r =
    (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x) ×
    (∀ (b : A) (b⊩ϕx : b ⊩ ∣ ϕ .predicate ∣ x) → (pr₁ ⨾ (pr₂ ⨾ r) ⨾ b) ⊩ ∣ toPredicate p ∣ tt*) ×
    (∀ (b : A) (b⊩px : b ⊩ ∣ toPredicate p ∣ tt*) → (pr₂ ⨾ (pr₂ ⨾ r) ⨾ b) ⊩ ∣ ϕ .predicate ∣ x)
  Predicate.isPropValued (relation charFuncRel) (x , p) r =
    isProp×
      (perX .equality .isPropValued _ _)
      (isProp×
        (isPropΠ (λ _ → isPropΠ λ _ → (toPredicate p) .isPropValued _ _))
        (isPropΠ λ _ → isPropΠ λ _ → ϕ .predicate .isPropValued _ _))
  isFunctionalRelation.isStrictDomain (isFuncRel charFuncRel) =
    do
      return
        (pr₁ ,
        (λ { x p r (pr₁r⊩x~x , ⊩ϕx≤p , ⊩p≤ϕx) → pr₁r⊩x~x}))
  isFunctionalRelation.isStrictCodomain (isFuncRel charFuncRel) =
    do
      let
        idClosure : ApplStrTerm as 2
        idClosure = # zero
        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (λ*abst idClosure) ̇ (λ*abst idClosure)
      return
        (λ* realizer ,
        (λ x y r x₁ →
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym
                (cong (λ x → pr₁ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ∙
                 cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ∙
                 βreduction idClosure a (r ∷ [])))
              a⊩y) ,
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym
                (cong (λ x → pr₂ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ∙
                 cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ∙
                 βreduction idClosure a (r ∷ [])))
              a⊩y)))
  isFunctionalRelation.isRelational (isFuncRel charFuncRel) =
    do
      (sX , sX⊩isSymmetricX) ← perX .isSymmetric
      (tX , tX⊩isTransitiveX) ← perX .isTransitive
      (relϕ , relϕ⊩isRelationalϕ) ← isStrictRelation.isRelational (ϕ .isStrictRelationPredicate)
      let
        closure1 : ApplStrTerm as 4
        closure1 = ` pr₁ ̇ # one ̇ (` pr₁ ̇ (` pr₂ ̇ # two) ̇ (` relϕ ̇ # zero ̇ (` sX ̇ # three)))

        closure2 : ApplStrTerm as 4
        closure2 = ` relϕ ̇ (` pr₂ ̇ (` pr₂ ̇ # two) ̇ (` pr₂ ̇ # one ̇ # zero)) ̇ # three

        realizer : ApplStrTerm as 3
        realizer = ` pair ̇ (` tX ̇ (` sX ̇ # two) ̇ # two) ̇ (` pair ̇ (λ*abst closure1) ̇ (λ*abst closure2))
      return
        (λ*3 realizer ,
        (λ { x x' p p' a b c a⊩x~x' (⊩x~x , ⊩ϕx≤p , ⊩p≤ϕx) (⊩p≤p' , ⊩p'≤p) →
          let
            ⊩x'~x = sX⊩isSymmetricX x x' a a⊩x~x'
            ⊩x'~x' = tX⊩isTransitiveX x' x x' _ _ ⊩x'~x a⊩x~x'
          in
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'))
            (sym (cong (λ x → pr₁ ⨾ x) (λ*3ComputationRule realizer a b c) ∙ pr₁pxy≡x _ _))
            ⊩x'~x' ,
          (λ r r⊩ϕx' →
            subst
              (λ r' → r' ⊩ ∣ toPredicate p' ∣ tt*)
              (sym
                (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x) ⨾ r) (λ*3ComputationRule realizer a b c) ∙
                 cong (λ x → pr₁ ⨾ x ⨾ r) (pr₂pxy≡y _ _) ∙
                 cong (λ x → x ⨾ r) (pr₁pxy≡x _ _) ∙
                 βreduction closure1 r (c ∷ b ∷ a ∷ [])))
              (⊩p≤p' _ (⊩ϕx≤p _ (relϕ⊩isRelationalϕ x' x _ _ r⊩ϕx' ⊩x'~x)))) ,
          λ r r⊩p' →
            subst
              (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x')
              (sym
                (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x) ⨾ r) (λ*3ComputationRule realizer a b c) ∙
                 cong (λ x → pr₂ ⨾ x ⨾ r) (pr₂pxy≡y _ _) ∙
                 cong (λ x → x ⨾ r) (pr₂pxy≡y _ _) ∙
                 βreduction closure2 r (c ∷ b ∷ a ∷ [])))
              (relϕ⊩isRelationalϕ x x' _ _ (⊩p≤ϕx _ (⊩p'≤p r r⊩p')) a⊩x~x') }))
  isFunctionalRelation.isSingleValued (isFuncRel charFuncRel) =
    do
      let
        closure1 : ApplStrTerm as 3
        closure1 = ` pr₁ ̇ (` pr₂ ̇ # one) ̇ (` pr₂ ̇ (` pr₂ ̇ # two) ̇ # zero)

        closure2 : ApplStrTerm as 3
        closure2 = ` pr₁ ̇ (` pr₂ ̇ # two) ̇ (` pr₂ ̇ (` pr₂ ̇ # one) ̇ # zero)

        realizer : ApplStrTerm as 2
        realizer = ` pair ̇ λ*abst closure1 ̇ λ*abst closure2
      return
        (λ*2 realizer ,
        (λ { x y y' r₁ r₂ (⊩x~x , ⊩ϕx≤y , ⊩y≤ϕx) (⊩'x~x , ⊩ϕx≤y' , ⊩y'≤ϕx) →
          (λ a a⊩y →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y' ∣ tt*)
              (sym (cong (λ x → pr₁ ⨾ x ⨾ a) (λ*2ComputationRule realizer r₁ r₂) ∙ cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ∙ βreduction closure1 a (r₂ ∷ r₁ ∷ [])))
              (⊩ϕx≤y' _ (⊩y≤ϕx a a⊩y))) ,
          (λ a a⊩y' →
            subst
              (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*)
              (sym (cong (λ x → pr₂ ⨾ x ⨾ a) (λ*2ComputationRule realizer r₁ r₂) ∙ cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ∙ βreduction closure2 a (r₂ ∷ r₁ ∷ [])))
              (⊩ϕx≤y _ (⊩y'≤ϕx a a⊩y'))) }))
  isFunctionalRelation.isTotal (isFuncRel charFuncRel) =
    do
      let
        idClosure : ApplStrTerm as 2
        idClosure = # zero

        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ # zero ̇ (` pair ̇ λ*abst idClosure ̇ λ*abst idClosure)
      return
        (λ* realizer ,
        (λ x r r⊩x~x →
          let
            resultPredicate : Predicate Unit*
            resultPredicate =
              makePredicate
                isSetUnit*
                (λ { tt* s → s ⊩ ∣ ϕ .predicate ∣ x })
                (λ { tt* s → ϕ .predicate .isPropValued _ _ })
          in
          return
            (fromPredicate resultPredicate ,
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
              r⊩x~x ,
            (λ b b⊩ϕx →
              subst
                (λ r → r ⊩ ∣ toPredicate (fromPredicate resultPredicate) ∣ tt*)
                (sym
                  (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x) ⨾ b) (λ*ComputationRule realizer r) ∙
                   cong (λ x → pr₁ ⨾ x ⨾ b) (pr₂pxy≡y _ _) ∙
                   cong (λ x → x ⨾ b) (pr₁pxy≡x _ _) ∙
                   βreduction idClosure b (r ∷ [])))
                (subst (λ p → b ⊩ ∣ p ∣ tt*) (sym (compIsIdFunc resultPredicate)) b⊩ϕx)) ,
            (λ b b⊩'ϕx →
              subst
                (λ r → r ⊩ ∣ ϕ .predicate ∣ x)
                (sym
                  (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x) ⨾ b) (λ*ComputationRule realizer r) ∙
                   cong (λ x → pr₂ ⨾ x ⨾ b) (pr₂pxy≡y _ _) ∙
                   cong (λ x → x ⨾ b) (pr₂pxy≡y _ _) ∙
                   βreduction idClosure b (r ∷ [])))
                let foo = subst (λ p → b ⊩ ∣ p ∣ tt*) (compIsIdFunc resultPredicate) b⊩'ϕx in foo))))

  subobjectCospan : ∀ char → Cospan RT
  Cospan.l (subobjectCospan char) = X , perX
  Cospan.m (subobjectCospan char) = ResizedPredicate Unit* , Ωper
  Cospan.r (subobjectCospan char) = Unit* , terminalPer
  Cospan.s₁ (subobjectCospan char) = char
  Cospan.s₂ (subobjectCospan char) = [ trueFuncRel ]

  opaque
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding terminalFuncRel
    unfolding trueFuncRel
    unfolding incFuncRel
    subobjectSquareCommutes : [ incFuncRel ] ⋆ [ charFuncRel ] ≡ [ terminalFuncRel subPer ] ⋆ [ trueFuncRel ]
    subobjectSquareCommutes =
      let
        answer =
          do
            (stX , stX⊩isStrictDomainX) ← idFuncRel perX .isStrictDomain
            (relϕ , relϕ⊩isRelationalϕ) ← StrictRelation.isRelational ϕ
            let
              closure : ApplStrTerm as 2
              closure = (` pr₁ ̇ (` pr₂ ̇ (` pr₂ ̇ # one)) ̇ (` relϕ ̇ (` pr₂ ̇ (` pr₁ ̇ # one)) ̇ (` pr₁ ̇ (` pr₁ ̇ # one))))
              realizer : ApplStrTerm as 1
              realizer =
                ` pair ̇
                  (` pair ̇ (` stX ̇ (` pr₁ ̇ (` pr₁ ̇ # zero))) ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇
                  λ*abst closure
            return
              (λ* realizer ,
              (λ { x p r r⊩∃x' →
                do
                  (x' , (⊩x~x' , ⊩ϕx) , ⊩x'~x' , ⊩ϕx'≤p , ⊩p≤ϕx') ← r⊩∃x'
                  return
                    (tt* ,
                    ((subst
                      (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                      (sym (cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₁pxy≡x _ _))
                      (stX⊩isStrictDomainX x x' _ ⊩x~x')) ,
                     (subst
                       (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x)
                       (sym (cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₂pxy≡y _ _))
                       ⊩ϕx)) ,
                    λ r' →
                      let
                        eq : pr₂ ⨾ (λ* realizer ⨾ r) ⨾ r' ≡ pr₁ ⨾ (pr₂ ⨾ (pr₂ ⨾ r)) ⨾ (relϕ ⨾ (pr₂ ⨾ (pr₁ ⨾ r)) ⨾ (pr₁ ⨾ (pr₁ ⨾ r)))
                        eq =
                          cong (λ x → pr₂ ⨾ x ⨾ r') (λ*ComputationRule realizer r) ∙
                          cong (λ x → x ⨾ r') (pr₂pxy≡y _ _) ∙
                          βreduction closure r' (r ∷ [])
                      in
                      subst
                        (λ r' → r' ⊩ ∣ toPredicate p ∣ tt*)
                        (sym eq)
                        (⊩ϕx'≤p _ (relϕ⊩isRelationalϕ x x' _ _ ⊩ϕx ⊩x~x'))) }))
      in
      eq/ _ _ (answer , F≤G→G≤F subPer Ωper (composeFuncRel _ _ _ incFuncRel charFuncRel) (composeFuncRel _ _ _ (terminalFuncRel subPer) trueFuncRel) answer)

  module
    UnivPropWithRepr
    {Y : Type ℓ}
    (perY : PartialEquivalenceRelation Y)
    (F : FunctionalRelation perY perX)
    (G : FunctionalRelation perY terminalPer)
    (entailment : pointwiseEntailment perY Ωper (composeFuncRel _ _ _ G trueFuncRel) (composeFuncRel _ _ _ F charFuncRel)) where

    opaque
      unfolding terminalFuncRel
      G≤idY : pointwiseEntailment perY terminalPer G (terminalFuncRel perY)
      G≤idY =
        do
          (stDG , stDG⊩isStrictDomainG) ← G .isStrictDomain
          return
            (stDG ,
            (λ { y tt* r r⊩Gy → stDG⊩isStrictDomainG y tt* r r⊩Gy }))

    opaque
      idY≤G : pointwiseEntailment perY terminalPer (terminalFuncRel perY) G
      idY≤G = F≤G→G≤F perY terminalPer G (terminalFuncRel perY) G≤idY

    opaque
      unfolding trueFuncRel
      trueFuncRelTruePredicate : ∀ a → (a ⊩ ∣ trueFuncRel .relation ∣ (tt* , fromPredicate truePredicate))
      trueFuncRelTruePredicate a = λ b → subst (λ p → (a ⨾ b) ⊩ ∣ p ∣ tt*) (sym (compIsIdFunc truePredicate)) tt*

    opaque
      unfolding composeFuncRel
      unfolding terminalFuncRel
      {-# TERMINATING #-}
      H : FunctionalRelation perY subPer
      Predicate.isSetX (relation H) = isSet× (perY .isSetX) (perX .isSetX)
      Predicate.∣ relation H ∣ (y , x) r = r ⊩ ∣ F .relation ∣ (y , x)
      Predicate.isPropValued (relation H) (y , x) r = F .relation .isPropValued _ _
      isFunctionalRelation.isStrictDomain (isFuncRel H) =
        do
          (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
          return
            (stFD ,
             (λ y x r r⊩Hyx → stFD⊩isStrictDomainF y x r r⊩Hyx))
      isFunctionalRelation.isStrictCodomain (isFuncRel H) =
        do
          (ent , ent⊩entailment) ← entailment
          (a , a⊩idY≤G) ← idY≤G
          (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
          (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
          (svF , svF⊩isSingleValuedF) ← F .isSingleValued
          (relϕ , relϕ⊩isRelationalϕ) ← StrictRelation.isRelational ϕ
          let
            realizer : ApplStrTerm as 1
            realizer =
              ` pair ̇
                (` stFC ̇ # zero) ̇
                (` relϕ ̇
                  (` pr₂ ̇ (` pr₂ ̇ (` pr₂ ̇ (` ent ̇ (` pair ̇ (` a ̇ (` stFD ̇ # zero)) ̇ ` k)))) ̇ ` k) ̇
                  (` svF ̇ (` pr₁ ̇ (` ent ̇ (` pair ̇ (` a ̇ (` stFD ̇ # zero)) ̇ ` k))) ̇ # zero))
          return
            (λ* realizer ,
             (λ y x r r⊩Hyx →
               subst
                 (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                 (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
                 (stFC⊩isStrictCodomainF y x _ r⊩Hyx) ,
               (equivFun
                 (propTruncIdempotent≃ (ϕ .predicate .isPropValued _ _))
                 (do
                   (x' , ⊩Fyx' , ⊩x'~x' , ⊩ϕx'≤⊤ , ⊩⊤≤ϕx') ←
                     ent⊩entailment
                     y
                     (fromPredicate truePredicate)
                     (pair ⨾ (a ⨾ (stFD ⨾ r)) ⨾ k)
                     (return
                       (tt* ,
                        subst
                          (λ r → r ⊩ ∣ G .relation ∣ (y , tt*))
                          (sym (pr₁pxy≡x _ _))
                          (a⊩idY≤G y tt* (stFD ⨾ r) (stFD⊩isStrictDomainF y x _ r⊩Hyx))  ,
                        trueFuncRelTruePredicate _))
                   let
                     ⊩x'~x = svF⊩isSingleValuedF y x' x _ _ ⊩Fyx' r⊩Hyx
                     ⊩ϕx = relϕ⊩isRelationalϕ x' x _ _ (⊩⊤≤ϕx' k (subst (λ p → k ⊩ ∣ p ∣ tt*) (sym (compIsIdFunc truePredicate)) tt*)) ⊩x'~x
                   return (subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) ⊩ϕx)))))
      isFunctionalRelation.isRelational (isFuncRel H) =
        do
          (relF , relF⊩isRelationalF) ← isFunctionalRelation.isRelational (F .isFuncRel)
          let
            realizer : ApplStrTerm as 3
            realizer = ` relF ̇ # two ̇ # one ̇ (` pr₁ ̇ # zero)
          return
            (λ*3 realizer ,
             (λ y y' x x' a b c ⊩y~y' ⊩Fyx (⊩x~x' , ⊩ϕx) →
               subst
                 (λ r' → r' ⊩ ∣ F .relation ∣ (y' , x'))
                 (sym (λ*3ComputationRule realizer a b c))
                 (relF⊩isRelationalF y y' x x' _ _ _ ⊩y~y' ⊩Fyx ⊩x~x')))
      isFunctionalRelation.isSingleValued (isFuncRel H) =
        do
          (ent , ent⊩entailment) ← entailment
          (a , a⊩idY≤G) ← idY≤G
          (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
          (svF , svF⊩isSingleValuedF) ← F .isSingleValued
          (relϕ , relϕ⊩isRelationalϕ) ← StrictRelation.isRelational ϕ
          let
            realizer : ApplStrTerm as 2
            realizer =
              ` pair ̇
                (` svF ̇ # one ̇ # zero) ̇
                (` relϕ ̇ (` pr₂ ̇ (` pr₂ ̇ (` pr₂ ̇ (` ent ̇ (` pair ̇ (` a ̇ (` stFD  ̇ # one)) ̇ ` k)))) ̇ ` k) ̇ (` svF ̇ (` pr₁ ̇ (` ent ̇ (` pair ̇ (` a ̇ (` stFD ̇ # one)) ̇ ` k))) ̇ # one))
          return
            (λ*2 realizer ,
             (λ y x x' r₁ r₂ ⊩Fyx ⊩Fyx' →
               subst
                 (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                 (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₁pxy≡x _ _))
                 (svF⊩isSingleValuedF y x x' _ _ ⊩Fyx ⊩Fyx') ,
               (equivFun
                 (propTruncIdempotent≃ (ϕ .predicate .isPropValued _ _))
                 (do
                   (x'' , ⊩Fyx'' , ⊩x''~x'' , ⊩ϕx''≤⊤ , ⊩⊤≤ϕx'') ←
                     ent⊩entailment
                     y
                     (fromPredicate truePredicate)
                     (pair ⨾ (a ⨾ (stFD ⨾ r₁)) ⨾ k)
                     (return
                       (tt* ,
                        subst (λ r → r ⊩ ∣ G .relation ∣ (y , tt*)) (sym (pr₁pxy≡x _ _)) (a⊩idY≤G y tt* _ (stFD⊩isStrictDomainF y x _ ⊩Fyx))  ,
                        trueFuncRelTruePredicate _))
                   let
                     ⊩x''~x = svF⊩isSingleValuedF y x'' x _ _ ⊩Fyx'' ⊩Fyx
                     ⊩ϕx = relϕ⊩isRelationalϕ x'' x _ _ (⊩⊤≤ϕx'' k (subst (λ p → k ⊩ ∣ p ∣ tt*) (sym (compIsIdFunc truePredicate)) tt*)) ⊩x''~x
                   return
                     (subst
                       (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x)
                       (sym (cong (λ x → pr₂ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₂pxy≡y _ _))
                       ⊩ϕx)))))
      isFunctionalRelation.isTotal (isFuncRel H) =
        do
          (ent , ent⊩entailment) ← entailment
          (a , a⊩idY≤G) ← idY≤G
          let
            realizer : ApplStrTerm as 1
            realizer = ` pr₁ ̇ (` ent ̇ (` pair ̇ (` a ̇ # zero) ̇ ` k))
          return
            (λ* realizer ,
            (λ { y r r⊩y~y →
              do
                (x , ⊩Fyx , ⊩x~x , ⊩ϕx≤⊤ , ⊩⊤≤ϕx) ←
                  ent⊩entailment
                    y
                    (fromPredicate truePredicate)
                    (pair ⨾ (a ⨾ r) ⨾ k)
                    (return
                      (tt* ,
                       subst (λ r → r ⊩ ∣ G .relation ∣ (y , tt*)) (sym (pr₁pxy≡x _ _)) (a⊩idY≤G y tt* r r⊩y~y)  ,
                       trueFuncRelTruePredicate _))
                return (x , subst (λ r' → r' ⊩ ∣ F .relation ∣ (y , x)) (sym (λ*ComputationRule realizer r)) ⊩Fyx) }))

    opaque
      unfolding composeRTMorphism
      unfolding incFuncRel
      unfolding H
      F≡H⋆inc : [ F ] ≡ [ H ] ⋆ [ incFuncRel ]
      F≡H⋆inc =
        let
          answer =
            do
              (relF , relF⊩isRelationalF) ← isFunctionalRelation.isRelational (F .isFuncRel)
              (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
              let
                realizer : ApplStrTerm as 1
                realizer = ` relF ̇ (` stFD ̇ (` pr₁ ̇ # zero)) ̇ (` pr₁ ̇ # zero) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))
              return
                 (λ* realizer ,
                 (λ y x r ⊩∃x' →
                   equivFun
                     (propTruncIdempotent≃ (F .relation .isPropValued _ _))
                     (do
                       (x' , ⊩Hyx' , ⊩x'~x , ⊩ϕx') ← ⊩∃x'
                       return
                         (subst
                           (λ r' → r' ⊩ ∣ F .relation ∣ (y , x))
                           (sym (λ*ComputationRule realizer r))
                           (relF⊩isRelationalF y y x' x _ _ _ (stFD⊩isStrictDomainF y x' _ ⊩Hyx') ⊩Hyx' ⊩x'~x)))))
        in eq/ _ _ (F≤G→G≤F perY perX (composeFuncRel _ _ _ H incFuncRel) F answer , answer)

    opaque
      unfolding composeRTMorphism
      unfolding terminalFuncRel
      G≡H⋆terminal : [ G ] ≡ [ H ] ⋆ [ terminalFuncRel subPer ]
      G≡H⋆terminal =
        let
          answer =
            do
              (stHD , stHD⊩isStrictDomainH) ← H .isStrictDomain
              (a , a⊩idY≤G) ← idY≤G
              let
                realizer : ApplStrTerm as 1
                realizer = ` a ̇ (` stHD ̇ (` pr₁ ̇ # zero))
              return
                (λ* realizer ,
                 (λ { y tt* r r⊩∃x →
                   equivFun
                     (propTruncIdempotent≃ (G .relation .isPropValued _ _))
                     (do
                       (x , ⊩Hyx , ⊩x~x , ⊩ϕx) ← r⊩∃x
                       return (subst (λ r' → r' ⊩ ∣ G .relation ∣ (y , tt*)) (sym (λ*ComputationRule realizer r)) (a⊩idY≤G y tt* _ (stHD⊩isStrictDomainH y x _ ⊩Hyx)))) }))
        in eq/ _ _ (F≤G→G≤F perY terminalPer (composeFuncRel _ _ _ H (terminalFuncRel subPer)) G answer , answer)

    opaque
      unfolding composeRTMorphism
      unfolding H
      unfolding incFuncRel
      isUniqueH : ∀ (H' : FunctionalRelation perY subPer) → [ F ] ≡ [ H' ] ⋆ [ incFuncRel ] → [ G ] ≡ [ H' ] ⋆ [ terminalFuncRel subPer ] → [_] {R = bientailment perY subPer} H ≡ [ H' ]
      isUniqueH H' F≡H'⋆inc G≡H'⋆term =
        let
          F≤H'⋆inc = [F]≡[G]→F≤G F (composeFuncRel _ _ _ H' incFuncRel) F≡H'⋆inc
          answer : pointwiseEntailment _ _ H H'
          answer =
            do
              (a , a⊩F≤H'⋆inc) ← F≤H'⋆inc
              (relH' , relH'⊩isRelationalH) ← isFunctionalRelation.isRelational (H' .isFuncRel)
              (stDH , stDH⊩isStrictDomainH) ← H .isStrictDomain
              let
                realizer : ApplStrTerm as 1
                realizer = ` relH' ̇ (` stDH ̇ # zero) ̇ (` pr₁ ̇ (` a ̇ # zero)) ̇ (` pr₂ ̇ (` a ̇ # zero))
              return
                (λ* realizer ,
                 (λ y x r r⊩Hyx →
                   equivFun
                     (propTruncIdempotent≃ (H' .relation .isPropValued _ _))
                     (do
                       (x' , ⊩H'yx' , ⊩x'~x , ⊩ϕx') ← a⊩F≤H'⋆inc y x r r⊩Hyx
                       return
                         (subst
                           (λ r' → r' ⊩ ∣ H' .relation ∣ (y , x))
                           (sym (λ*ComputationRule realizer r))
                           (relH'⊩isRelationalH y y x' x _ _ _ (stDH⊩isStrictDomainH y x r r⊩Hyx) ⊩H'yx' (⊩x'~x , ⊩ϕx'))))))
        in
        eq/ _ _ (answer , (F≤G→G≤F _ _ H H' answer))

  opaque
    classifies : isPullback RT (subobjectCospan [ charFuncRel ]) [ incFuncRel ] [ terminalFuncRel subPer ] subobjectSquareCommutes
    classifies {Y , perY} f g f⋆char≡g⋆true =
      SQ.elimProp2
        {P = λ f g → ∀ (commutes : f ⋆ [ charFuncRel ] ≡ g ⋆ [ trueFuncRel ]) → ∃![ hk ∈ RTMorphism perY subPer ] (f ≡ hk ⋆ [ incFuncRel ]) × (g ≡ hk ⋆ [ terminalFuncRel subPer ])}
        (λ f g → isPropΠ λ _ → isPropIsContr)
        (λ F G F⋆char≡G⋆true →
           let
             entailment = [F]⋆[G]≡[H]⋆[I]→H⋆I≤F⋆G F charFuncRel G trueFuncRel F⋆char≡G⋆true
           in
           uniqueExists
             [ UnivPropWithRepr.H perY F G entailment ]
             (UnivPropWithRepr.F≡H⋆inc perY F G entailment ,
             UnivPropWithRepr.G≡H⋆terminal perY F G entailment)
             (λ hk' → isProp× (squash/ _ _) (squash/ _ _))
             -- nested eliminator 🤮
             λ { h' (f≡h'⋆inc , g≡h'⋆term) →
               SQ.elimProp
                 {P = λ h' → ∀ (comm1 : [ F ] ≡ h' ⋆ [ incFuncRel ]) (comm2 : [ G ] ≡ h' ⋆ [ terminalFuncRel subPer ]) → [ UnivPropWithRepr.H perY F G entailment ] ≡ h'}
                 (λ h' → isPropΠ λ _ → isPropΠ λ _ → squash/ _ _)
                 (λ H' F≡H'⋆inc G≡H'⋆term →
                   UnivPropWithRepr.isUniqueH perY F G entailment H' F≡H'⋆inc G≡H'⋆term)
                 h'
                 f≡h'⋆inc
                 g≡h'⋆term })
        f g f⋆char≡g⋆true

  module
    PullbackHelper
    (C : FunctionalRelation perX Ωper)
    (commutes : [ incFuncRel ] ⋆ [ C ] ≡ [ terminalFuncRel subPer ] ⋆ [ trueFuncRel ])
    (classifies : isPullback RT (subobjectCospan [ C ]) [ incFuncRel ] [ terminalFuncRel subPer ] commutes) where

    {-# TERMINATING #-}
    ψ : StrictRelation perX
    Predicate.isSetX (predicate ψ) = perX .isSetX
    Predicate.∣ predicate ψ ∣ x r = r ⊩ ∣ C .relation ∣ (x , ⊤)
    Predicate.isPropValued (predicate ψ) x r = C .relation .isPropValued _ _
    isStrictRelation.isStrict (isStrictRelationPredicate ψ) =
      do
        (stDC , stDC⊩isStrictDomainC) ← C .isStrictDomain
        return
          (stDC ,
           λ x r r⊩Cx⊤ → stDC⊩isStrictDomainC x (fromPredicate truePredicate) r r⊩Cx⊤)
    isStrictRelation.isRelational (isStrictRelationPredicate ψ) =
      do
        (relC , relC⊩isRelationalC) ← isFunctionalRelation.isRelational (C .isFuncRel)
        (stCC , stCC⊩isStrictCodomainC) ← C .isStrictCodomain
        let
          realizer : ApplStrTerm as 2
          realizer = ` relC ̇ # zero ̇ # one ̇ (` stCC ̇ # one)
        return
          (λ*2 realizer ,
           λ x x' a b a⊩Cx⊤ b⊩x~x' →
             subst (λ r' → r' ⊩ ∣ C .relation ∣ (x' , ⊤)) (sym (λ*2ComputationRule realizer a b)) (relC⊩isRelationalC x x' ⊤ ⊤ _ _ _ b⊩x~x' a⊩Cx⊤ (stCC⊩isStrictCodomainC x ⊤ a a⊩Cx⊤)))

    perψ = InducedSubobject.subPer perX ψ
    incFuncRelψ = InducedSubobject.incFuncRel perX ψ

    opaque
      unfolding composeRTMorphism
      unfolding InducedSubobject.incFuncRel
      unfolding terminalFuncRel
      unfolding trueFuncRel
      pbSqCommutes : [ incFuncRelψ ] ⋆ [ C ] ≡ [ terminalFuncRel perψ ] ⋆ [ trueFuncRel ]
      pbSqCommutes =
        let
          answer =
            do
              (stDC , stDC⊩isStrictDomainC) ← C .isStrictDomain
              (stCC , stCC⊩isStrictCodomainC) ← C .isStrictCodomain
              (svC , svC⊩isSingleValuedC) ← C .isSingleValued
              (relC , relC⊩isRelationalC) ← isFunctionalRelation.isRelational (C .isFuncRel)
              (sX , sX⊩isSymmetricX) ← perX .isSymmetric
              let
                closure : ApplStrTerm as 2
                closure = ` pr₁ ̇ (` svC ̇ (` pr₂ ̇ (` pr₁ ̇ # one)) ̇ (` relC ̇ (` sX ̇ (` pr₁ ̇ (` pr₁ ̇ # one))) ̇ (` pr₂ ̇ # one) ̇ (` stCC ̇ (` pr₂ ̇ # one)))) ̇ ` k

                realizer : ApplStrTerm as 1
                realizer = ` pair ̇ (` pair ̇ (` stDC ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇ (λ*abst closure)
              return
                (λ* realizer ,
                 λ { x p r r⊩∃x' →
                   do
                     (x' , (⊩x~x' , ⊩Cx⊤) , ⊩Cx'p) ← r⊩∃x'
                     let
                       ⊩Cxp = relC⊩isRelationalC x' x p p _ _ _ (sX⊩isSymmetricX x x' _ ⊩x~x') ⊩Cx'p (stCC⊩isStrictCodomainC x' p _ ⊩Cx'p) 
                       (⊩⊤≤p , p≤⊤) = svC⊩isSingleValuedC x ⊤ p _ _ ⊩Cx⊤ ⊩Cxp
                     return
                       (tt* ,
                       (subst
                         (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                         (sym
                           (cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer r) ∙
                            cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙
                            pr₁pxy≡x _ _ ))
                         (stDC⊩isStrictDomainC x ⊤ _ ⊩Cx⊤) ,
                        subst
                          (λ r' → r' ⊩ ∣ C .relation ∣ (x , ⊤))
                          (sym
                            (cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer r) ∙
                             cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙
                             pr₂pxy≡y _ _))
                          ⊩Cx⊤) ,
                        λ a →
                          subst
                            (λ r' → r' ⊩ ∣ toPredicate p ∣ tt*)
                            (sym
                              (cong (λ x → pr₂ ⨾ x ⨾ a) (λ*ComputationRule realizer r) ∙
                               cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ∙
                               βreduction closure a (r ∷ [])))
                            (⊩⊤≤p k (subst (λ q → k ⊩ ∣ q ∣ tt*) (sym (compIsIdFunc truePredicate)) tt*))) })
        in eq/ _ _ (answer , F≤G→G≤F _ _ (composeFuncRel _ _ _ incFuncRelψ C) (composeFuncRel _ _ _ (terminalFuncRel perψ) trueFuncRel) answer)

    opaque
      unfolding InducedSubobject.incFuncRel
      unfolding composeFuncRel
      ⊩Cx⊤≤ϕx : ∃[ ent ∈ A ] (∀ (x : X) (r : A) → r ⊩ ∣ C .relation ∣ (x , ⊤) → (ent ⨾ r) ⊩ ∣ ϕ .predicate ∣ x)
      ⊩Cx⊤≤ϕx =
        let
          ((h , incψ≡h⋆incϕ , termψ≡h⋆termϕ) , isUniqueH) = classifies [ incFuncRelψ ] [ terminalFuncRel perψ ] pbSqCommutes
        in
        SQ.elimProp
          {P = λ h → ∀ (incψ≡h⋆incϕ : [ incFuncRelψ ] ≡ h ⋆ [ incFuncRel ]) → ∃[ ent ∈ A ] (∀ (x : X) (r : A) → r ⊩ ∣ C .relation ∣ (x , ⊤) → (ent ⨾ r) ⊩ ∣ ϕ .predicate ∣ x)}
          (λ h → isPropΠ λ _ → isPropPropTrunc)
          (λ H incψ≡H⋆incϕ →
            do
              (a , a⊩incψ≤H⋆incϕ) ← [F]≡[G]⋆[H]→F≤G⋆H incFuncRelψ H incFuncRel incψ≡H⋆incϕ
              (stDC , stDC⊩isStrictDomainC) ← C .isStrictDomain
              (relϕ , relϕ⊩isRelationalϕ) ← isStrictRelation.isRelational (ϕ .isStrictRelationPredicate)
              let
                realizer = ` relϕ ̇ (` pr₂ ̇ (` pr₂ ̇ (` a ̇ (` pair ̇ (` stDC ̇ # zero) ̇ # zero)))) ̇ (` pr₁ ̇ (` pr₂ ̇ (` a ̇ (` pair ̇ (` stDC ̇ # zero) ̇ # zero)))) 
              return
                (λ* realizer ,
                 (λ x r r⊩Cx⊤ →
                   equivFun
                     (propTruncIdempotent≃ (ϕ .predicate .isPropValued _ _))
                     (do
                       (x' , ⊩Hxx' , ⊩x'~x , ⊩ϕx') ←
                           a⊩incψ≤H⋆incϕ
                           x x
                           (pair ⨾ (stDC ⨾ r) ⨾ r)
                           (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (pr₁pxy≡x _ _)) (stDC⊩isStrictDomainC x ⊤ r r⊩Cx⊤) ,
                            subst (λ r' → r' ⊩ ∣ C .relation ∣ (x , ⊤)) (sym (pr₂pxy≡y _ _)) r⊩Cx⊤)
                       return
                         (subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (λ*ComputationRule realizer r)) (relϕ⊩isRelationalϕ x' x _ _ ⊩ϕx' ⊩x'~x))))))
          h
          incψ≡h⋆incϕ

  opaque
    unfolding trueFuncRel
    unfolding composeFuncRel
    unfolding incFuncRel
    unfolding terminalFuncRel
    isUniqueCharMorphism :
      ∀ (char : RTMorphism perX Ωper)
      → (commutes : [ incFuncRel ] ⋆ char ≡ [ terminalFuncRel subPer ] ⋆ [ trueFuncRel ])
      → (classifies : isPullback RT (subobjectCospan char) [ incFuncRel ] [ terminalFuncRel subPer ] commutes)
      → char ≡ [ charFuncRel ]
    isUniqueCharMorphism char commutes classifies =
      SQ.elimProp
        {P =
          λ char →
          ∀ (commutes : [ incFuncRel ] ⋆ char ≡ [ terminalFuncRel subPer ] ⋆ [ trueFuncRel ])
            (classifies : isPullback RT (subobjectCospan char) [ incFuncRel ] [ terminalFuncRel subPer ] commutes)
          → char ≡ [ charFuncRel ]}
        (λ char → isPropΠ λ commutes → isPropΠ λ classifies → squash/ _ _)
        (λ charFuncRel' commutes classifies →
          let
            answer =
              do
                (stDX' , stDX'⊩isStrictDomainX') ← charFuncRel' .isStrictDomain
                (relX' , relX'⊩isRelationalX') ← isFunctionalRelation.isRelational (charFuncRel' .isFuncRel)
                (a , a⊩inc⋆X'≤term⋆true) ← [F]⋆[G]≡[H]⋆[I]→F⋆G≤H⋆I incFuncRel charFuncRel' (terminalFuncRel subPer) trueFuncRel commutes
                (b , b⊩term⋆true≤inc⋆X') ← [F]⋆[G]≡[H]⋆[I]→H⋆I≤F⋆G incFuncRel charFuncRel' (terminalFuncRel subPer) trueFuncRel commutes
                (d , d⊩X'x⊤≤ϕx) ← PullbackHelper.⊩Cx⊤≤ϕx charFuncRel' commutes classifies
                let
                  closure1 : ApplStrTerm as 2
                  closure1 = ` pr₂ ̇ (` a ̇ (` pair ̇ (` pair ̇ (` stDX'  ̇ # one) ̇ # zero) ̇ # one)) ̇ ` k
                  closure2 : ApplStrTerm as 2
                  closure2 = ` d ̇ (` relX' ̇ (` stDX' ̇ # one) ̇ # one ̇ (` pair ̇ ` k ̇ (` k ̇ # zero)))
                  realizer : ApplStrTerm as 1
                  realizer = ` pair ̇ (` stDX' ̇ # zero) ̇ (` pair ̇ λ*abst closure1 ̇ λ*abst closure2)
                return
                  (λ* realizer ,
                   (λ { x p r r⊩X'xp →
                     let
                       ⊩x~x = stDX'⊩isStrictDomainX' x p r r⊩X'xp
                     in
                     subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x  _ _)) ⊩x~x ,
                     (λ b b⊩ϕx →
                       let
                         goal =
                           a⊩inc⋆X'≤term⋆true
                             x p (pair ⨾ (pair ⨾ (stDX' ⨾ r) ⨾ b) ⨾ r)
                             (return
                               (x , (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₁pxy≡x _ _)) ⊩x~x ,
                               subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₂pxy≡y _ _)) b⊩ϕx) ,
                               subst (λ r' → r' ⊩ ∣ charFuncRel' .relation ∣ (x , p)) (sym (pr₂pxy≡y _ _)) r⊩X'xp))

                         eq : pr₁ ⨾ (pr₂ ⨾ (λ* realizer ⨾ r)) ⨾ b ≡ pr₂ ⨾ (a ⨾ (pair ⨾ (pair ⨾ (stDX' ⨾ r) ⨾ b) ⨾ r)) ⨾ k
                         eq =
                           cong (λ x → pr₁ ⨾ (pr₂ ⨾ x) ⨾ b) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₁ ⨾ x ⨾ b) (pr₂pxy≡y _ _) ∙ cong (λ x → x ⨾ b) (pr₁pxy≡x _ _) ∙ βreduction closure1 b (r ∷ [])
                       in
                       equivFun
                         (propTruncIdempotent≃ (toPredicate p .isPropValued _ _))
                         (do
                           (tt* , ⊩'x~x , ⊩⊤≤p) ← goal
                           return (subst (λ r' → r' ⊩ ∣ toPredicate p ∣ tt*) (sym eq) (⊩⊤≤p k)))) ,
                     (λ c c⊩p →
                       let
                         ⊩X'x⊤ =
                           relX'⊩isRelationalX'
                             x x p ⊤ _ _
                             (pair ⨾ k ⨾ (k ⨾ c))
                             ⊩x~x r⊩X'xp
                             ((λ b b⊩p → subst (λ q → (pr₁ ⨾ (pair ⨾ k ⨾ (k ⨾ c))) ⊩ ∣ q ∣ tt*) (sym (compIsIdFunc truePredicate)) tt*) ,
                              (λ b b⊩⊤ → subst (λ r' → r' ⊩ ∣ toPredicate p ∣ tt*) (sym (cong (λ x → x ⨾ b) (pr₂pxy≡y _ _) ∙ kab≡a _ _)) c⊩p))

                         eq : pr₂ ⨾ (pr₂ ⨾ (λ* realizer ⨾ r)) ⨾ c ≡ d ⨾ (relX' ⨾ (stDX' ⨾ r) ⨾ r ⨾ (pair ⨾ k ⨾ (k ⨾ c)))
                         eq =
                           cong (λ x → pr₂ ⨾ (pr₂ ⨾ x) ⨾ c) (λ*ComputationRule realizer r) ∙
                           cong (λ x → pr₂ ⨾ x ⨾ c) (pr₂pxy≡y _ _) ∙
                           cong (λ x → x ⨾ c) (pr₂pxy≡y _ _) ∙
                           βreduction closure2 c (r ∷ [])
                       in
                       subst
                         (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x)
                         (sym eq)
                         (d⊩X'x⊤≤ϕx x _ ⊩X'x⊤)) }))
          in eq/ _ _ (answer , F≤G→G≤F _ _ charFuncRel' charFuncRel answer))
        char
        commutes
        classifies
