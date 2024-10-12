open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Fin hiding (Fin; _/_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Relation.Binary
-- Functional relations that represent monics
module Realizability.Topos.MonicReprFuncRel
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.Equalizer {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.BinProducts {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism
open PartialEquivalenceRelation
open FunctionalRelation
open Category RT

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

-- Monics in RT
module _ {X Y : Type ℓ'} (perX : PartialEquivalenceRelation X) (perY : PartialEquivalenceRelation Y) (F : FunctionalRelation perX perY) where

  opaque
    isInjectiveFuncRel : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
    isInjectiveFuncRel =
      ∃[ inj ∈ A ] (∀ x x' y r₁ r₂ → r₁ ⊩ ∣ F .relation ∣ (x , y) → r₂ ⊩ ∣ F .relation ∣ (x' , y) → (inj ⨾ r₁ ⨾ r₂) ⊩ ∣ perX .equality ∣ (x , x'))

  opaque
    unfolding isInjectiveFuncRel
    isPropIsInjectiveFuncRel : isProp isInjectiveFuncRel
    isPropIsInjectiveFuncRel = isPropPropTrunc

  -- This is the easier part
  -- Essentially just a giant realizer that uses the injectivity
  opaque
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding isInjectiveFuncRel
    isInjectiveFuncRel→isMonic : isInjectiveFuncRel → isMonic RT [ F ]
    isInjectiveFuncRel→isMonic isInjectiveF {Z , perZ} {a} {b} a⋆[F]≡b⋆[F] =
      SQ.elimProp2
        {P = λ a b → composeRTMorphism _ _ _ a [ F ] ≡ composeRTMorphism _ _ _ b [ F ] → a ≡ b}
        (λ a b → isPropΠ λ _ → squash/ a b)
        (λ A B A⋆F≡B⋆F →
          let
            (p , q) = SQ.effective (isPropValuedBientailment perZ perY) (isEquivRelBientailment perZ perY) _ _ A⋆F≡B⋆F
            answer =
              do
                (p , p⊩A⋆F≤B⋆F) ← p
                (stCA , stCA⊩isStrictCodomainA) ← A .isStrictCodomain
                (stDA , stDA⊩isStrictDomainA) ← A .isStrictDomain
                (tlF , tlF⊩isTotalF) ← F .isTotal
                (relB , relB⊩isRelationalB) ← B .isRelational
                (injF , injF⊩isInjectiveF) ← isInjectiveF
                let
                  realizer : ApplStrTerm as 1
                  realizer =
                    ` relB ̇ (` stDA ̇ # fzero) ̇ (` pr₁ ̇ (` p ̇ (` pair ̇ # fzero ̇ (` tlF ̇ (` stCA ̇ # fzero))))) ̇
                      (` injF ̇ (` pr₂ ̇ (` p ̇ (` pair ̇ # fzero ̇ (` tlF ̇ (` stCA ̇ # fzero))))) ̇
                      (` tlF ̇ (` stCA ̇ # fzero)))
                return
                  (λ* realizer ,
                  (λ z x r r⊩Azx →
                    transport
                      (propTruncIdempotent (B .relation .isPropValued _ _))
                      (do
                        let
                          x~x = stCA⊩isStrictCodomainA z x r r⊩Azx
                          z~z = stDA⊩isStrictDomainA z x r r⊩Azx
                        (y , ⊩Fxy) ← tlF⊩isTotalF x _ x~x
                        (x' , ⊩Bzx' , ⊩Fx'y)  ←
                          p⊩A⋆F≤B⋆F
                            z y
                            (pair ⨾ r ⨾ (tlF ⨾ (stCA ⨾ r)))
                            (return
                              (x ,
                              subst (λ r' → r' ⊩ ∣ A .relation ∣ (z , x)) (sym (pr₁pxy≡x _ _)) r⊩Azx ,
                              subst (λ r' → r' ⊩ ∣ F .relation ∣ (x , y)) (sym (pr₂pxy≡y _ _)) ⊩Fxy))
                        let
                          x'~x = injF⊩isInjectiveF x' x y _ _ ⊩Fx'y ⊩Fxy -- this is the only place where we actually need the injectivity
                        return
                          (subst
                            (λ r' → r' ⊩ ∣ B .relation ∣ (z , x))
                            (sym (λ*ComputationRule realizer (r ∷ [])))
                            (relB⊩isRelationalB z z x' x _ _ _ z~z ⊩Bzx' x'~x)))))
          in
          eq/ A B (answer , F≤G→G≤F perZ perX A B answer))
        a b
        a⋆[F]≡b⋆[F]

  opaque
    unfolding binProdPr₁RT
    unfolding binProdPr₁FuncRel
    unfolding binProdPr₂FuncRel
    unfolding equalizerMorphism
    unfolding composeRTMorphism

    π₁ : FunctionalRelation (binProdObRT perX perX) perX
    π₁ = binProdPr₁FuncRel perX perX

    π₂ : FunctionalRelation (binProdObRT perX perX) perX
    π₂ = binProdPr₂FuncRel perX perX

    kernelPairEqualizerFuncRel :
      FunctionalRelation
        (equalizerPer -- hehe
          (binProdObRT perX perX) perY
          ([ π₁ ] ⋆ [ F ])
          ([ π₂ ] ⋆ [ F ])
          (composeFuncRel _ _ _ π₁ F)
          (composeFuncRel _ _ _ π₂ F))
        (binProdObRT perX perX)
    kernelPairEqualizerFuncRel =
      equalizerFuncRel _ _
        ((binProdPr₁RT perX perX) ⋆ [ F ])
        ((binProdPr₂RT perX perX) ⋆ [ F ])
        (composeFuncRel _ _ _ (binProdPr₁FuncRel perX perX) F)
        (composeFuncRel _ _ _ (binProdPr₂FuncRel perX perX) F)

    kernelPairEqualizer⋆π₁≡kernelPairEqualizer⋆π₂ :
      composeRTMorphism _ _ _ [ kernelPairEqualizerFuncRel ] (composeRTMorphism _ _ _ [ π₁ ] [ F ]) ≡ composeRTMorphism _ _ _ [ kernelPairEqualizerFuncRel ] (composeRTMorphism _ _ _ [ π₂ ] [ F ])
    kernelPairEqualizer⋆π₁≡kernelPairEqualizer⋆π₂ =
      inc⋆f≡inc⋆g
        (binProdObRT perX perX) perY
        (composeRTMorphism _ _ _ [ π₁ ] [ F ])
        (composeRTMorphism _ _ _ [ π₂ ] [ F ])
        (composeFuncRel _ _ _ π₁ F)
        (composeFuncRel _ _ _ π₂ F)

    mainKernelPairEquation : ([ kernelPairEqualizerFuncRel ] ⋆ [ π₁ ]) ⋆ [ F ] ≡ ([ kernelPairEqualizerFuncRel ] ⋆ [ π₂ ]) ⋆ [ F ]
    mainKernelPairEquation =
      ([ kernelPairEqualizerFuncRel ] ⋆ [ π₁ ]) ⋆ [ F ]
        ≡⟨ ⋆Assoc [ kernelPairEqualizerFuncRel ] [ π₁ ] [ F ]  ⟩ -- Agda cannot solve these as constraints 😔
      [ kernelPairEqualizerFuncRel ] ⋆ ([ π₁ ] ⋆ [ F ])
        ≡⟨ kernelPairEqualizer⋆π₁≡kernelPairEqualizer⋆π₂ ⟩
      [ kernelPairEqualizerFuncRel ] ⋆ ([ π₂ ] ⋆ [ F ])
        ≡⟨ sym (⋆Assoc [ kernelPairEqualizerFuncRel ] [ π₂ ] [ F ]) ⟩
      ([ kernelPairEqualizerFuncRel ] ⋆ [ π₂ ]) ⋆ [ F ]
        ∎

  opaque
    unfolding isInjectiveFuncRel
    unfolding composeRTMorphism
    unfolding kernelPairEqualizerFuncRel
    unfolding equalizerFuncRel
    unfolding equalizerPer
    unfolding binProdPr₁RT
    unfolding binProdPr₂FuncRel
    isMonic→isInjectiveFuncRel : isMonic RT [ F ] → isInjectiveFuncRel
    isMonic→isInjectiveFuncRel isMonicF =
      do
        let
          equation = isMonicF {a = [ kernelPairEqualizerFuncRel ] ⋆ [ π₁ ]} {a' = [ kernelPairEqualizerFuncRel ] ⋆ [ π₂ ]} mainKernelPairEquation
          (p , q) = SQ.effective (isPropValuedBientailment _ _) (isEquivRelBientailment _ _) _ _ equation
        (p , p⊩kπ₁≤kπ₂) ← p
        (q , q⊩kπ₂≤kπ₁) ← q
        (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
        (stDF , stDF⊩isStrictDomainF) ← F .isStrictDomain
        (s , s⊩isSymmetricEqX) ← perX .isSymmetric
        (t , t⊩isTransitiveEqX) ← perX .isTransitive
        let
          cursed : ApplStrTerm as 2
          cursed =
             (` pair ̇
                  (` pair ̇
                    (` pair ̇ (` stDF ̇ # fzero) ̇ (` stDF ̇ # fone)) ̇
                    (` pair ̇ (` pair ̇ (` pair ̇ (` stDF ̇ # fzero) ̇ (` stDF ̇ # fone)) ̇ # fzero) ̇ (` pair ̇ (` pair ̇ (` stDF ̇ # fone) ̇ (` stDF ̇ # fzero)) ̇ # fone))) ̇
                  (` pair ̇ (` stDF ̇ # fzero) ̇ (` stDF ̇ # fone)))
          realizer : ApplStrTerm as 2
          realizer = ` t ̇ (` s ̇ (` pr₁ ̇ (` pr₂ ̇ (` p ̇ cursed)))) ̇ (` s ̇ (` pr₂ ̇ (` pr₁ ̇ (` pr₁ ̇ (` p ̇ cursed)))))
        return
          (λ* realizer ,
          (λ x₁ x₂ y r₁ r₂ r₁⊩Fx₁y r₂⊩Fx₂y →
            let
              x₁~x₁ = stDF⊩isStrictDomainF x₁ y r₁ r₁⊩Fx₁y
              x₂~x₂ = stDF⊩isStrictDomainF x₂ y r₂ r₂⊩Fx₂y
              foo =
                p⊩kπ₁≤kπ₂ (x₁ , x₂) x₁
                (pair ⨾
                  (pair ⨾
                    (pair ⨾ (stDF ⨾ r₁) ⨾ (stDF ⨾ r₂)) ⨾
                    (pair ⨾ (pair ⨾ (pair ⨾ (stDF ⨾ r₁) ⨾ (stDF ⨾ r₂)) ⨾ r₁) ⨾ (pair ⨾ (pair ⨾ (stDF ⨾ r₂) ⨾ (stDF ⨾ r₁)) ⨾ r₂))) ⨾
                  (pair ⨾ (stDF ⨾ r₁) ⨾ (stDF ⨾ r₂)))
                (return
                  (((x₁ , x₂)) ,
                  ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₁)) (sym (cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (pr₁pxy≡x _ _) ∙ cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₁pxy≡x _ _)) x₁~x₁ ,
                    subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₂)) (sym (cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (pr₁pxy≡x _ _) ∙ cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₂pxy≡y _ _)) x₂~x₂) ,
                 return
                  (y ,
                    return
                      (x₁ ,
                        (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₁))
                          (sym
                            (cong (λ x → pr₁ ⨾ (pr₁ ⨾ (pr₁ ⨾ (pr₂ ⨾ x)))) (pr₁pxy≡x _ _) ∙
                             cong (λ x → pr₁ ⨾ (pr₁ ⨾ (pr₁ ⨾ x))) (pr₂pxy≡y _ _) ∙
                             cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (pr₁pxy≡x _ _) ∙
                             cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙
                             pr₁pxy≡x _ _))
                          x₁~x₁ ,
                         subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₂))
                           (sym
                             (cong (λ x → pr₂ ⨾ (pr₁ ⨾ (pr₁ ⨾ (pr₂ ⨾ x)))) (pr₁pxy≡x _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₁ ⨾ (pr₁ ⨾ x))) (pr₂pxy≡y _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (pr₁pxy≡x _ _) ∙
                              cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙
                              pr₂pxy≡y _ _))
                           x₂~x₂) ,
                         subst (λ r' → r' ⊩ ∣ F .relation ∣ (x₁ , y))
                           (sym
                             (cong (λ x → pr₂ ⨾ (pr₁ ⨾ (pr₂ ⨾ x))) (pr₁pxy≡x _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (pr₂pxy≡y _ _) ∙
                              cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙
                              pr₂pxy≡y _ _))
                           r₁⊩Fx₁y) ,
                    return
                      (x₂ ,
                        (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₂))
                          (sym
                            (cong (λ x → pr₁ ⨾ (pr₁ ⨾ (pr₂ ⨾ (pr₂ ⨾ x)))) (pr₁pxy≡x _ _) ∙
                             cong (λ x → pr₁ ⨾ (pr₁ ⨾ (pr₂ ⨾ x))) (pr₂pxy≡y _ _) ∙
                             cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (pr₂pxy≡y _ _) ∙
                             cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙
                             pr₁pxy≡x _ _))
                          x₂~x₂ ,
                         subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₁))
                           (sym
                             (cong (λ x → pr₂ ⨾ (pr₁ ⨾ (pr₂ ⨾ (pr₂ ⨾ x)))) (pr₁pxy≡x _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₁ ⨾ (pr₂ ⨾ x))) (pr₂pxy≡y _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₁ ⨾ x)) (pr₂pxy≡y _ _) ∙
                              cong (λ x → pr₂ ⨾ x) (pr₁pxy≡x _ _) ∙
                              pr₂pxy≡y _ _))
                           x₁~x₁) ,
                         subst (λ r' → r' ⊩ ∣ F .relation ∣ (x₂ , y))
                           (sym
                             (cong (λ x → pr₂ ⨾ (pr₂ ⨾ (pr₂ ⨾ x))) (pr₁pxy≡x _ _) ∙
                              cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (pr₂pxy≡y _ _) ∙
                              cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙
                              pr₂pxy≡y _ _)) r₂⊩Fx₂y))) ,
                         subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₁)) (sym (cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _)) x₁~x₁ ,
                         subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₂)) (sym (cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _)) x₂~x₂))
            in
            transport
              (propTruncIdempotent (perX .equality .isPropValued _ _))
              (do
                ((x₁' , x₂') , ((x₁~x₁' , x₂~x₂') , kp2) , p2) ← foo
                (y' , bar1 , bar2) ← kp2
                (x₁'' , (x₁~x₁'' , x₂~'x₂) , ⊩Fx₁''y') ← bar1
                (x₂'' , (x₂~x₂'' , x₁~'x₁) , ⊩Fx₂''y') ← bar2
                let
                  (x₂'~x₁ , foo') = p2
                return
                  (subst
                    (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₂))
                    (sym (λ*ComputationRule realizer (r₁ ∷ r₂ ∷ [])))
                    (t⊩isTransitiveEqX x₁ x₂' x₂ _ _ (s⊩isSymmetricEqX x₂' x₁ _ x₂'~x₁) (s⊩isSymmetricEqX x₂ x₂' _ x₂~x₂'))))))
