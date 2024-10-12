{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetCoequalizer renaming (rec to setCoequalizerRec; elimProp to setCoequalizerElimProp)
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.Sigma
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.Coequalizers {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _
    {X Y : Type ℓ}
    (xs : Assembly X)
    (ys : Assembly Y)
    (f g : AssemblyMorphism xs ys)
    where
      private
        _⊩X_ = xs ._⊩_
        _⊩Y_ = ys ._⊩_

      _⊩coeq_ : (a : A) (x : SetCoequalizer (f .map) (g .map)) → hProp ℓ
      a ⊩coeq x =
        setCoequalizerRec
        isSetHProp
        (λ y → (∃[ y' ∈ Y ] (inc {f = f .map} {g = g .map} y ≡ inc y') × (a ⊩Y y')) , squash₁)
        (λ x i → (∃[ y' ∈ Y ] (coeq {f = f .map} {g = g .map} x i ≡ inc y') × (a ⊩Y y')) , squash₁)
        x

      coequalizer : Assembly (SetCoequalizer (f .map) (g .map))
      ⊩coeqSurjective : (x : SetCoequalizer (f .map) (g .map)) → ∃[ a ∈ A ] ((a ⊩coeq x) .fst)
   
      coequalizer .isSetX = squash
      coequalizer ._⊩_ a x = (a ⊩coeq x) .fst
      coequalizer .⊩isPropValued a x = (a ⊩coeq x) .snd
      coequalizer .⊩surjective x = ⊩coeqSurjective x

      ⊩coeqSurjective x =
        setCoequalizerElimProp
          {C = λ b → ∃[ a ∈ A ] ((a ⊩coeq b) .fst)}
          (λ x → squash₁)
          (λ b → do
                  (b~ , b~realizes) ← ys .⊩surjective b
                  return (b~ , b~⊩coeq_inc_b b b~ b~realizes))
          x where
            b~⊩coeq_inc_b : (b : Y) (b~ : A) (b~realizes : b~ ⊩Y b) → (b~ ⊩coeq inc b) .fst
            b~⊩coeq_inc_b b b~ b~realizes = ∣ b , refl , b~realizes ∣₁
      {-
        Coequalziers have a map E ← Y ⇇ X
      -}
      ιcoequalizer : AssemblyMorphism ys coequalizer
      ιcoequalizer .map = inc
      ιcoequalizer .tracker = ∣ Id , (λ y yᵣ yᵣ⊩y → subst (λ r → (r ⊩coeq inc y) .fst) (sym (Ida≡a yᵣ)) ∣ y , refl , yᵣ⊩y ∣₁) ∣₁

      coequalizerFactors : ((Z , zs) : Σ[ Z ∈ Type ℓ ] Assembly Z)
                         → (ι' : AssemblyMorphism ys zs)
                         → (f ⊚ ι' ≡ g ⊚ ι')
                         → ∃![ ! ∈ AssemblyMorphism coequalizer zs ] (ιcoequalizer ⊚ ! ≡ ι')
      coequalizerFactors (Z , zs) ι' f⊚ι'≡g⊚ι' =
        uniqueExists
          (let
              map = (λ x → setCoequalizerRec (zs .isSetX) (ι' .map) (λ x i → f⊚ι'≡g⊚ι' i .map x) x)
            in
            makeAssemblyMorphism
            map
            (do
              (ι'~ , ι'~⊩isTrackedι') ← ι' .tracker
              return
                (ι'~ ,
                (λ x r r⊩x →  setCoequalizerElimProp {C = λ x → ∀ (r : A) → r ⊩[ coequalizer ] x → (ι'~ ⨾ r) ⊩[ zs ] (map x)} {!!} (λ y r r⊩y → {!!}) x r r⊩x))))
          {!!}
          {!!}
          {!!}
        {-
        uniqueExists (λ where
                        .map → setCoequalizerRec (zs .isSetX) (ι' .map) λ x → λ i → f⊚ι'≡g⊚ι' i .map x
                        .tracker → return ({!!} , (λ x r r⊩x → {!setCoequalizerElimProp {C = λ x → !})))
                        (AssemblyMorphism≡ _ _ (funExt λ x → refl))
                        (λ ! → isSetAssemblyMorphism ys zs (ιcoequalizer ⊚ !) ι')
                        λ ! ιcoequalizer⊚!≡ι' → AssemblyMorphism≡ _ _
                            (funExt λ x →
                              setCoequalizerElimProp
                              {C = λ x → setCoequalizerRec (zs .isSetX) (ι' .map) (λ x₁ i → f⊚ι'≡g⊚ι' i .map x₁) x ≡ ! .map x}
                              (λ x → zs .isSetX _ _) (λ y → λ i → ιcoequalizer⊚!≡ι' (~ i) .map y) x) -}
