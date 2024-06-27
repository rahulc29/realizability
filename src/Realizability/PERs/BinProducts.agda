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
open import Cubical.Data.Unit
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct
open import Utils.SQElim as SQElim

module Realizability.PERs.BinProducts 
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.PERs.PER ca
open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open PER
open Category PERCat

module _ (R S : PER) where
  binProdObPER : PER
  PER.relation binProdObPER =
    (λ a b → (pr₁ ⨾ a) ~[ R ] (pr₁ ⨾ b) × (pr₂ ⨾ a) ~[ S ] (pr₂ ⨾ b)) , λ a b → isProp× (isProp~ (pr₁ ⨾ a) R (pr₁ ⨾ b)) (isProp~ (pr₂ ⨾ a) S (pr₂ ⨾ b))
  fst (isPER binProdObPER) a b (pr₁a~[R]pr₁b , pr₂a~[S]pr₂b) =
    (isSymmetric R (pr₁ ⨾ a) (pr₁ ⨾ b) pr₁a~[R]pr₁b) , (isSymmetric S (pr₂ ⨾ a) (pr₂ ⨾ b) pr₂a~[S]pr₂b)
  snd (isPER binProdObPER) a b c (pr₁a~[R]pr₁b , pr₂a~[S]pr₂b) (pr₁b~[R]pr₁c , pr₂b~[S]pr₂c) =
    (isTransitive R (pr₁ ⨾ a) (pr₁ ⨾ b) (pr₁ ⨾ c) pr₁a~[R]pr₁b pr₁b~[R]pr₁c) , (isTransitive S (pr₂ ⨾ a) (pr₂ ⨾ b) (pr₂ ⨾ c) pr₂a~[S]pr₂b pr₂b~[S]pr₂c)

  isTrackerPr₁ : isTracker binProdObPER R pr₁
  isTrackerPr₁ = λ r r' (pr₁r~[R]pr₁r' , pr₂r~[S]pr₂r') → pr₁r~[R]pr₁r'

  binProdPr₁Tracker : perTracker binProdObPER R
  binProdPr₁Tracker = pr₁ , isTrackerPr₁

  binProdPr₁PER : perMorphism binProdObPER R
  binProdPr₁PER = [ binProdPr₁Tracker ]

  isTrackerPr₂ : isTracker binProdObPER S pr₂
  isTrackerPr₂ = λ { r r' (pr₁r~[R]pr₁r' , pr₂r~[S]pr₂r') → pr₂r~[S]pr₂r' }

  binProdPr₂Tracker : perTracker binProdObPER S
  binProdPr₂Tracker = pr₂ , isTrackerPr₂

  binProdPr₂PER : perMorphism binProdObPER S
  binProdPr₂PER = [ binProdPr₂Tracker ]

  binProdUnivPropPER :
    (T : PER)
    (f : perMorphism T R)
    (g : perMorphism T S) →
    ∃![ ! ∈ perMorphism T binProdObPER ] ((composePerMorphism T binProdObPER R ! binProdPr₁PER ≡ f) × (composePerMorphism T binProdObPER S ! binProdPr₂PER ≡ g))
  binProdUnivPropPER T f g =
    inhProp→isContr
      map
      (isPropMapType f g) where

      mapEqProj1 : ∀ ! f' → Type _
      mapEqProj1 ! f' = composePerMorphism T binProdObPER R ! binProdPr₁PER ≡ f'

      mapEqProj2 : ∀ ! g' → Type _
      mapEqProj2 ! g' = composePerMorphism T binProdObPER S ! binProdPr₂PER ≡ g'

      mapEqs : ∀ ! f' g' → Type _
      mapEqs ! f' g' = (composePerMorphism T binProdObPER R ! binProdPr₁PER ≡ f') × (composePerMorphism T binProdObPER S ! binProdPr₂PER ≡ g')

      isPropMapEqs : ∀ ! f' g' → isProp (mapEqs ! f' g')
      isPropMapEqs ! f' g' = isProp× (squash/ _ _) (squash/ _ _)

      mapType : ∀ f' g' → Type _
      mapType f' g' = Σ[ ! ∈ perMorphism T binProdObPER ] (mapEqs ! f' g')

      mapRealizer : ∀ a b → Term as 1
      mapRealizer a b = ` pair ̇ (` a ̇ # zero) ̇ (` b ̇ # zero)

      isSetMapType : ∀ f' g' → isSet (mapType f' g')
      isSetMapType f' g' = isSetΣ squash/ (λ ! → isSet× (isProp→isSet (squash/ _ _)) (isProp→isSet (squash/ _ _)))

      isPropMapType : ∀ f' g' → isProp (mapType f' g')
      isPropMapType f' g' (! , !⋆π₁≡f , !⋆π₂≡g) (!' , !'⋆π₁≡f , !'⋆π₂≡g) =
        Σ≡Prop
          (λ ! → isPropMapEqs ! f' g')
          (SQ.elimProp4
            {P = motive}
            isPropMotive
            goal
            f' g' ! !'
            !⋆π₁≡f
            !⋆π₂≡g
            !'⋆π₁≡f
            !'⋆π₂≡g) where

          motive : ∀ f' g' ! !' → Type _
          motive f' g' ! !' = ∀ (!proj1 : mapEqProj1 ! f') (!proj2 : mapEqProj2 ! g') (!'proj1 : mapEqProj1 !' f') (!'proj2 : mapEqProj2 !' g') → ! ≡ !'

          isPropMotive : ∀ f' g' ! !' → isProp (motive f' g' ! !')
          isPropMotive f' g' ! !' =
            isPropΠ4 λ _ _ _ _ → squash/ _ _

          goal : ∀ f' g' ! !' → motive [ f' ] [ g' ] [ ! ] [ !' ]
          goal (f , f⊩f) (g , g⊩g) (a , a⊩!) (b , b⊩!') !proj1 !proj2 !'proj1 !'proj2 =
            eq/ _ _
              λ r r~r →
                let
                  pr₁Equiv : (pr₁ ⨾ (a ⨾ r)) ~[ R ] (pr₁ ⨾ (b ⨾ r))
                  pr₁Equiv =
                    isTransitive
                    R (pr₁ ⨾ (a ⨾ r)) (f ⨾ r) (pr₁ ⨾ (b ⨾ r))
                    (subst (_~[ R ] (f ⨾ r)) (λ*ComputationRule (` pr₁ ̇ (` a ̇ # zero)) r) (!proj1Equiv r r~r))
                    (isSymmetric R (pr₁ ⨾ (b ⨾ r)) (f ⨾ r) (subst (_~[ R ] (f ⨾ r)) (λ*ComputationRule (` pr₁ ̇ (` b ̇ # zero)) r) (!'proj1Equiv r r~r)))

                  pr₂Equiv : (pr₂ ⨾ (a ⨾ r)) ~[ S ] (pr₂ ⨾ (b ⨾ r))
                  pr₂Equiv =
                    isTransitive
                      S (pr₂ ⨾ (a ⨾ r)) (g ⨾ r) (pr₂ ⨾ (b ⨾ r))
                      (subst (_~[ S ] (g ⨾ r)) (λ*ComputationRule (` pr₂ ̇ (` a ̇ # zero)) r) (!proj2Equiv r r~r))
                      (isSymmetric S (pr₂ ⨾ (b ⨾ r)) (g ⨾ r) (subst (_~[ S ] (g ⨾ r)) (λ*ComputationRule (` pr₂ ̇ (` b ̇ # zero)) r) (!'proj2Equiv r r~r)))
                in
                pr₁Equiv ,
                pr₂Equiv where
                !proj1Equiv : isEquivTracker T R (composePerTracker T binProdObPER R (a , a⊩!) binProdPr₁Tracker) (f , f⊩f)
                !proj1Equiv = effectiveIsEquivTracker T R _ _ !proj1
                
                !proj2Equiv : isEquivTracker T S (composePerTracker T binProdObPER S (a , a⊩!) binProdPr₂Tracker) (g , g⊩g)
                !proj2Equiv = effectiveIsEquivTracker T S _ _ !proj2
                
                !'proj1Equiv : isEquivTracker T R (composePerTracker T binProdObPER R (b , b⊩!') binProdPr₁Tracker) (f , f⊩f)
                !'proj1Equiv = effectiveIsEquivTracker T R _ _ !'proj1
                
                !'proj2Equiv : isEquivTracker T S (composePerTracker T binProdObPER S (b , b⊩!') binProdPr₂Tracker) (g , g⊩g)
                !'proj2Equiv = effectiveIsEquivTracker T S _ _ !'proj2

      coreMap : ∀ a b → mapType [ a ] [ b ]
      coreMap (a , a⊩f) (b , b⊩g) =
        [ (λ* (mapRealizer a b)) ,
            (λ r r' r~r' →
              subst2
                (λ abr abr' → abr ~[ binProdObPER ] abr')
                (sym (λ*ComputationRule (mapRealizer a b) r))
                (sym (λ*ComputationRule (mapRealizer a b) r'))
                (subst2
                  (λ ar ar' → ar ~[ R ] ar')
                  (sym (pr₁pxy≡x _ _))
                  (sym (pr₁pxy≡x _ _))
                  (a⊩f r r' r~r') ,
                subst2
                  (λ br br' → br ~[ S ] br')
                  (sym (pr₂pxy≡y _ _))
                  (sym (pr₂pxy≡y _ _))
                  (b⊩g r r' r~r'))) ] ,
        eq/ _ _
          (λ r r~r →
            subst
              (_~[ R ] (a ⨾ r))
              (sym
                (λ*ComputationRule (` pr₁ ̇ (` λ* (mapRealizer a b) ̇ # zero)) r ∙
                 cong (pr₁ ⨾_) (λ*ComputationRule (mapRealizer a b) r)))
              (subst (_~[ R ] (a ⨾ r)) (sym (pr₁pxy≡x _ _)) (a⊩f r r r~r))) ,
        eq/ _ _
         λ r r~r →
           subst
             (_~[ S ] (b ⨾ r))
             (sym
               (λ*ComputationRule (` pr₂ ̇ (` λ* (mapRealizer a b) ̇ # zero)) r ∙
                cong (pr₂ ⨾_) (λ*ComputationRule (mapRealizer a b) r) ∙
                pr₂pxy≡y _ _))
             (b⊩g r r r~r)

      map : mapType f g
      map =
        SQ.elimProp2
          {P = mapType}
          isPropMapType
          coreMap
          f g

BinProductPER : (R S : PER) → BinProduct PERCat R S
BinProduct.binProdOb (BinProductPER R S) = binProdObPER R S
BinProduct.binProdPr₁ (BinProductPER R S) = binProdPr₁PER R S
BinProduct.binProdPr₂ (BinProductPER R S) = binProdPr₂PER R S
BinProduct.univProp (BinProductPER R S) {T} f g = binProdUnivPropPER R S T f g

BinProductsPER : BinProducts PERCat
BinProductsPER R S = BinProductPER R S
