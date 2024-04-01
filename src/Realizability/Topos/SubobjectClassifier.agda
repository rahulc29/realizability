open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*; λ* to `λ*abst)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback
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

private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure
  λ*abst = `λ*abst as fefermanStructure

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
      ent₁ = ` pr₂ ̇ # fone ̇ # fzero

      ent₂ : ApplStrTerm as 2
      ent₂ = ` pr₁ ̇ # fone ̇ # fzero

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
                ≡⟨ cong (λ x → pr₁ ⨾ x ⨾ a) (λ*ComputationRule realizer (r ∷ [])) ⟩
              pr₁ ⨾ (pair ⨾ (s ⨾ (s ⨾ (k ⨾ pr₂) ⨾ (k ⨾ r)) ⨾ (s ⨾ k ⨾ k)) ⨾ (s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ (k ⨾ r)) ⨾ (s ⨾ k ⨾ k))) ⨾ a
                ≡⟨ cong (λ x → x ⨾ a) (pr₁pxy≡x _ _) ⟩
              s ⨾ (s ⨾ (k ⨾ pr₂) ⨾ (k ⨾ r)) ⨾ (s ⨾ k ⨾ k) ⨾ a
                ≡⟨ sabc≡ac_bc _ _ _ ⟩
              s ⨾ (k ⨾ pr₂) ⨾ (k ⨾ r) ⨾ a ⨾ (s ⨾ k ⨾ k ⨾ a)
                ≡⟨ cong (λ x → x ⨾ (s ⨾ k ⨾ k ⨾ a)) (sabc≡ac_bc _ _ _) ⟩
              k ⨾ pr₂ ⨾ a ⨾ (k ⨾ r ⨾ a) ⨾ (s ⨾ k ⨾ k ⨾ a)
                ≡⟨ cong (λ x → x ⨾ (k ⨾ r ⨾ a) ⨾ (s ⨾ k ⨾ k ⨾ a)) (kab≡a _ _) ⟩
              pr₂ ⨾ (k ⨾ r ⨾ a) ⨾ (s ⨾ k ⨾ k ⨾ a)
                ≡⟨ cong (λ x → pr₂ ⨾ x ⨾ (s ⨾ k ⨾ k ⨾ a)) (kab≡a _ _) ⟩
              pr₂ ⨾ r ⨾ (s ⨾ k ⨾ k ⨾ a)
                ≡⟨ cong (λ x → pr₂ ⨾ r ⨾ x) (Ida≡a _) ⟩
              pr₂ ⨾ r ⨾ a
                ∎
          in
          subst (λ r' → r' ⊩ ∣ toPredicate α ∣ tt*) (sym eq) (pr₂r⊩β≤α a a⊩β)) ,
        (λ a a⊩α → subst (λ r' → r' ⊩ ∣ toPredicate β ∣ tt*) (sym {!!}) (pr₁r⊩α≤β a a⊩α)) })
isPartialEquivalenceRelation.isTransitive (isPerEquality Ωper) =
  do
    return
      ({!!} ,
      (λ { x y z a b (⊩x≤y , ⊩y≤x) (⊩y≤z , ⊩z≤y) →
        (λ r r⊩x → subst (λ r' → r' ⊩ ∣ toPredicate z ∣ tt*) {!!} (⊩y≤z _ (⊩x≤y r r⊩x))) ,
        (λ r r⊩z → subst (λ r' → r' ⊩ ∣ toPredicate x ∣ tt*) {!!} (⊩y≤x _ (⊩z≤y r r⊩z))) }))

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
      return
        ({!!} ,
        (λ { tt* y r r⊩⊤≤y →
          (λ a a⊩y → subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} a⊩y) ,
          (λ a a⊩y → subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} a⊩y)}))
  isFunctionalRelation.isRelational (isFuncRel trueFuncRel) =
    do
      return
        ({!!} ,
        (λ { tt* tt* x y a b c tt* b⊩⊤≤x (pr₁c⊩x≤y , pr₂c⊩y≤x) r →
          subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} (pr₁c⊩x≤y (b ⨾ k) (b⊩⊤≤x k))}))
  isFunctionalRelation.isSingleValued (isFuncRel trueFuncRel) =
    do
      return
        ({!!} ,
        (λ { tt* x y r₁ r₂ r₁⊩⊤≤x r₂⊩⊤≤y →
          (λ a a⊩x → subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} (r₂⊩⊤≤y k)) ,
          (λ a a⊩y → subst (λ r' → r' ⊩ ∣ toPredicate x ∣ tt*) {!!} (r₁⊩⊤≤x k))}))
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

-- The subobject classifier indeed classifies subobjects
module _
  (X : Type ℓ)
  (perX : PartialEquivalenceRelation X)
  (ϕ : StrictRelation perX) where

  open InducedSubobject perX ϕ
  open StrictRelation
  resizedϕ = fromPredicate (ϕ .predicate)

  -- the functional relation that represents the unique indicator map
  theFuncRel : FunctionalRelation perX Ωper
  Predicate.isSetX (relation theFuncRel) = isSet× (perX .isSetX) isSetResizedPredicate
  Predicate.∣ relation theFuncRel ∣ (x , p) r =
    (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x) ×
    (∀ (b : A) (b⊩ϕx : b ⊩ ∣ ϕ .predicate ∣ x) → (pr₁ ⨾ (pr₂ ⨾ r) ⨾ b) ⊩ ∣ toPredicate p ∣ tt*) ×
    (∀ (b : A) (b⊩px : b ⊩ ∣ toPredicate p ∣ tt*) → (pr₂ ⨾ (pr₂ ⨾ r) ⨾ b) ⊩ ∣ ϕ .predicate ∣ x)
  Predicate.isPropValued (relation theFuncRel) (x , p) r =
    isProp×
      (perX .equality .isPropValued _ _)
      (isProp×
        (isPropΠ (λ _ → isPropΠ λ _ → (toPredicate p) .isPropValued _ _))
        (isPropΠ λ _ → isPropΠ λ _ → ϕ .predicate .isPropValued _ _))
  isFunctionalRelation.isStrictDomain (isFuncRel theFuncRel) =
    do
      return
        (pr₁ ,
        (λ { x p r (pr₁r⊩x~x , ⊩ϕx≤p , ⊩p≤ϕx) → pr₁r⊩x~x}))
  isFunctionalRelation.isStrictCodomain (isFuncRel theFuncRel) =
    do
      return
        ({!!} ,
        (λ x y r x₁ →
          (λ a a⊩y → subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} a⊩y) ,
          (λ a a⊩y → subst (λ r' → r' ⊩ ∣ toPredicate y ∣ tt*) {!!} a⊩y)))
  isFunctionalRelation.isRelational (isFuncRel theFuncRel) =
    do
      return
        ({!!} ,
        (λ { x x' p p' a b c a⊩x~x' (pr₁b⊩x~x , pr₁pr₂b⊩ϕx≤y , pr₂pr₂b⊩y≤ϕx) (pr₁c⊩y≤y' , pr₂c⊩y'≤y) →
          {!!} ,
          (λ r r⊩ϕx' → {!!}) ,
          λ r r⊩p' → {!!} }))
  isFunctionalRelation.isSingleValued (isFuncRel theFuncRel) =
    do
      return
        ({!!} ,
        (λ { x y y' r₁ r₂ (pr₁r₁⊩x~x , pr₁pr₂r₁⊩ϕx≤y , pr₂pr₂r₁⊩y≤ϕx) (pr₂r₂⊩x~x , pr₁pr₂r₂⊩ϕx≤y' , pr₂pr₂r₂⊩y'≤ϕx) →
          {!!} }))
  isFunctionalRelation.isTotal (isFuncRel theFuncRel) =
    do
      return
        ({!!} ,
        (λ x r r⊩x~x →
          let
            resultPredicate : Predicate Unit*
            resultPredicate =
              consPredicate
                isSetUnit*
                (λ { tt* s → s ⊩ ∣ ϕ .predicate ∣ x })
                (λ { tt* s → ϕ .predicate .isPropValued _ _ })
          in
          return
            (fromPredicate resultPredicate ,
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym {!!}) r⊩x~x ,
            (λ b b⊩ϕx → {!compIsIdFunc!}) ,
            λ b b⊩'ϕx → {!!})))


  subobjectCospan : Cospan RT
  Cospan.l subobjectCospan = X , perX
  Cospan.m subobjectCospan = ResizedPredicate Unit* , Ωper
  Cospan.r subobjectCospan = Unit* , terminalPer
  Cospan.s₁ subobjectCospan = [ theFuncRel ]
  Cospan.s₂ subobjectCospan = [ trueFuncRel ]

  opaque
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding terminalFuncRel
    unfolding trueFuncRel
    unfolding incFuncRel
    subobjectSquareCommutes : [ incFuncRel ] ⋆ [ theFuncRel ] ≡ [ terminalFuncRel subPer ] ⋆ [ trueFuncRel ]
    subobjectSquareCommutes =
      let
        answer =
          do
            (stX , stX⊩isStrictDomainX) ← idFuncRel perX .isStrictDomain
            (relϕ , relϕ⊩isRelationalϕ) ← StrictRelation.isRelational ϕ
            let
              realizer : ApplStrTerm as 1
              realizer = ` pair ̇ (` pair ̇ (` stX ̇ (` pr₁ ̇ (` pr₁ ̇ # fzero))) ̇ (` pr₂ ̇ (` pr₁ ̇ # fzero))) ̇ λ*abst (` pr₁ ̇ (` pr₂ ̇ (` pr₂ ̇ # fone)) ̇ (` relϕ ̇ (` pr₂ ̇ (` pr₁ ̇ # fone)) ̇ (` pr₁ ̇ (` pr₁ ̇ # fone))))
            return
              (λ* realizer ,
              (λ { x p r r⊩∃x' →
                do
                  (x' , (⊩x~x' , ⊩ϕx) , ⊩x'~x' , ⊩ϕx'≤p , ⊩p≤ϕx') ← r⊩∃x'
                  return
                    (tt* ,
                    ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer (r ∷ [])) ∙ cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₁pxy≡x _ _)) (stX⊩isStrictDomainX x x' _ ⊩x~x')) ,
                     (subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer (r ∷ [])) ∙ cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₂pxy≡y _ _)) ⊩ϕx)) ,
                    λ r' →
                      subst (λ r' → r' ⊩ ∣ toPredicate p ∣ tt*) (sym (cong (λ x → pr₂ ⨾ x ⨾ r') (λ*ComputationRule realizer (r ∷ [])) ∙ cong (λ x → x ⨾ r') (pr₂pxy≡y _ _) ∙ sabc≡ac_bc _ _ _ ∙ {!!})) (⊩ϕx'≤p _ (relϕ⊩isRelationalϕ x x' _ _ ⊩ϕx ⊩x~x'))) }))
      in
      eq/ _ _ (answer , {!!})

  classifies : isPullback RT subobjectCospan [ incFuncRel ] [ terminalFuncRel subPer ] subobjectSquareCommutes
  classifies {Y , perY} f g f⋆char≡g⋆true =
      SQ.elimProp2
        {P = λ f g → ∀ (commutes : f ⋆ [ theFuncRel ] ≡ g ⋆ [ trueFuncRel ]) → ∃![ hk ∈ RTMorphism perY subPer ] (f ≡ hk ⋆ [ incFuncRel ]) × (g ≡ hk ⋆ [ terminalFuncRel subPer ])}
        (λ f g → isPropΠ λ _ → isPropIsContr)
        (λ F G F⋆char≡G⋆true →
          uniqueExists
            {!!}
            ({!!} , {!!})
            (λ hk' → isProp× (squash/ _ _) (squash/ _ _))
            {!!})
        f g f⋆char≡g⋆true
