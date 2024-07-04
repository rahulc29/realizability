open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
open import Realizability.PropResizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
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

module Realizability.PERs.SubQuotient
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.PERs.PER ca
open import Realizability.Modest.Base ca

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _
  (per : PER) where

  subQuotient : Type ℓ
  subQuotient = A / per .PER.relation

  subQuotientRealizability : A → subQuotient → hProp ℓ
  subQuotientRealizability r [a] =
    SQ.rec
      isSetHProp
      (λ a → ([ a ] ≡ [ r ]) , squash/ [ a ] [ r ])
      (λ a b a~b →
        Σ≡Prop
          (λ _ → isPropIsProp)
          (hPropExt (squash/ [ a ] [ r ]) (squash/ [ b ] [ r ]) (λ [a]≡[r] → sym (eq/ a b a~b) ∙ [a]≡[r]) λ [b]≡[r] → sym (eq/ b a (per .PER.isPER .fst a b a~b)) ∙ [b]≡[r]))
      [a]

  subQuotientAssembly : Assembly subQuotient
  Assembly._⊩_ subQuotientAssembly r [a] = ⟨ subQuotientRealizability r [a] ⟩
  Assembly.isSetX subQuotientAssembly = squash/
  Assembly.⊩isPropValued subQuotientAssembly r [a] = str (subQuotientRealizability r [a])
  Assembly.⊩surjective subQuotientAssembly [a] =
    do
      (a , [a]≡[a]) ← []surjective [a]
      return
        (a , (subst (λ [a] → ⟨ subQuotientRealizability a [a] ⟩) [a]≡[a] refl))

  isModestSubQuotientAssembly : isModest subQuotientAssembly
  isModestSubQuotientAssembly x y a a⊩x a⊩y =
    SQ.elimProp2
      {P = motive}
      isPropMotive
      coreMap
      x y a a⊩x a⊩y where
        motive : subQuotient → subQuotient → Type ℓ
        motive x y = (a : A) → a ⊩[ subQuotientAssembly ] x → a ⊩[ subQuotientAssembly ] y → x ≡ y

        isPropMotive : ∀ x y → isProp (motive x y)
        isPropMotive x y = isPropΠ3 λ _ _ _ → squash/ x y

        coreMap : (r s : A) → motive [ r ] [ s ]
        coreMap r s a a⊩[r] a⊩[s] =
          [ r ]
            ≡⟨ a⊩[r] ⟩
          [ a ]
            ≡⟨ sym a⊩[s] ⟩
          [ s ]
            ∎
