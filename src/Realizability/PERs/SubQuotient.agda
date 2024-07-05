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

  domain : Type ℓ
  domain = Σ[ a ∈ A ] (per .PER.relation a a)

  subQuotient : Type ℓ
  subQuotient = domain / λ { (a , _) (b , _) → per .PER.relation a b }

  subQuotientRealizability : A → subQuotient → hProp ℓ
  subQuotientRealizability r [a] =
    SQ.rec
      isSetHProp
      (λ { (a , a~a) → r ~[ per ] a , isProp~ r per a })
      (λ { (a , a~a) (b , b~b) a~b →
        Σ≡Prop
          (λ x → isPropIsProp)
          (hPropExt
            (isProp~ r per a)
            (isProp~ r per b)
            (λ r~a → PER.isTransitive per r a b r~a a~b)
            (λ r~b → PER.isTransitive per r b a r~b (PER.isSymmetric per a b a~b))) })
      [a]
      
  
  subQuotientAssembly : Assembly subQuotient
  Assembly._⊩_ subQuotientAssembly r [a] = ⟨ subQuotientRealizability r [a] ⟩
  Assembly.isSetX subQuotientAssembly = squash/
  Assembly.⊩isPropValued subQuotientAssembly r [a] = str (subQuotientRealizability r [a])
  Assembly.⊩surjective subQuotientAssembly [a] =
    SQ.elimProp
      {P = λ [a] → ∃[ r ∈ A ] ⟨ subQuotientRealizability r [a] ⟩}
      (λ [a] → isPropPropTrunc)
      (λ { (a , a~a) → return (a , a~a) })
      [a]

  
  isModestSubQuotientAssembly : isModest subQuotientAssembly
  isModestSubQuotientAssembly x y a a⊩x a⊩y =
    SQ.elimProp2
      {P = λ x y → motive x y}
      isPropMotive
      (λ { (x , x~x) (y , y~y) a a~x a~y →
        eq/ (x , x~x) (y , y~y) (PER.isTransitive per x a y (PER.isSymmetric per a x a~x) a~y) })
      x y
      a a⊩x a⊩y where
        motive : ∀ (x y : subQuotient) → Type ℓ
        motive x y = ∀ (a : A) (a⊩x : a ⊩[ subQuotientAssembly ] x) (a⊩y : a ⊩[ subQuotientAssembly ] y) → x ≡ y

        isPropMotive : ∀ x y → isProp (motive x y)
        isPropMotive x y = isPropΠ3 λ _ _ _ → squash/ x y
