open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.Terminal
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.Terminal {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where

open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open CombinatoryAlgebra ca
open Assembly
open AssemblyMorphism

terminalAsm : Assembly Unit*
(Assembly._⊩_ terminalAsm) a tt* = Unit*
Assembly.isSetX terminalAsm = isSetUnit*
(Assembly.⊩isPropValued terminalAsm) a tt* = isPropUnit*
Assembly.⊩surjective terminalAsm tt* = ∣ k , tt* ∣₁

isTerminalTerminalAsm : isTerminal ASM (Unit* , terminalAsm)
isTerminalTerminalAsm (X , asmX) =
  inhProp→isContr
    (makeAssemblyMorphism
      (λ x → tt*)
      (return
        (k , (λ x r r⊩x → tt*))))
    (λ f g →
      AssemblyMorphism≡ _ _ (funExt λ x → refl))

TerminalASM : Terminal ASM
fst TerminalASM = Unit* , terminalAsm
snd TerminalASM = isTerminalTerminalAsm

-- global element
module _ {X : Type ℓ} (asmX : Assembly X) (x : X) (r : A) (r⊩x : r ⊩[ asmX ] x) where

  globalElement : AssemblyMorphism terminalAsm asmX
  AssemblyMorphism.map globalElement tt* = x
  AssemblyMorphism.tracker globalElement =
    return
      ((k ⨾ r) ,
      (λ { tt* a tt* → subst (λ r' → r' ⊩[ asmX ] x) (sym (kab≡a _ _)) r⊩x }))
