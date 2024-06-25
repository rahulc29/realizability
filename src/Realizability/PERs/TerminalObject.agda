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

terminalPER : PER
PER.relation terminalPER = (λ x y → Unit*) , λ x y → isPropUnit*
fst (PER.isPER terminalPER) = λ a b x → tt*
snd (PER.isPER terminalPER) = λ a b c x x₁ → tt*

isTerminalTerminalPER : isTerminal PERCat terminalPER
isTerminalTerminalPER X =
  inhProp→isContr
    [ k , (λ r r' r~r' → tt*) ]
    λ ! !' →
      SQ.elimProp2
        (λ ! !' → squash/ ! !')
        (λ { (a , a⊩!) (b , b⊩!) →
          eq/ _ _ λ r r~r → tt* })
        ! !'

terminal : Terminal PERCat
terminal = terminalPER , isTerminalTerminalPER
