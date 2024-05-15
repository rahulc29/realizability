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
open import Cubical.Categories.Limits.Terminal

module Realizability.PERs.TerminalObject 
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.PERs.PER ca
open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open PERMorphism

terminalPER : PER
PER.relation terminalPER = (λ x y → Unit*) , λ x y → isPropUnit*
fst (PER.isPER terminalPER) = λ a b x → tt*
snd (PER.isPER terminalPER) = λ a b c x x₁ → tt*

isTerminalTerminalPER : isTerminal PERCat terminalPER
isTerminalTerminalPER X =
  inhProp→isContr
    (makePERMorphism (λ x → [ k ]) (return (Id , (λ a aXa → (eq/ k (Id ⨾ a) tt*) , tt*))))
    λ x y → PERMorphism≡ x y (funExt λ q → {!!})

terminal : Terminal PERCat
terminal = terminalPER , {!!}
