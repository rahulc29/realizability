open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData renaming (zero to fzero)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

module Realizability.Topos.Object
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open import Realizability.Tripos.Logic.Semantics {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Algebra.Base {ℓ' = ℓ'} {ℓ'' = ℓ''} ca renaming (AlgebraicPredicate to Predicate)
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

record PartialEquivalenceRelation (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
    equality : Predicate (X × X)
    isSymmetric : ∃[ sm ∈ A ] (∀ x x' r → r ⊩[ equality ] (x , x') → (sm ⨾ r) ⊩[ equality ] (x' , x))
    isTransitive : ∃[ ts ∈ A ] (∀ x x' x'' r s → r ⊩[ equality ] (x , x') → s ⊩[ equality ] (x' , x'') → (ts ⨾ r ⨾ s) ⊩[ equality ] (x , x''))
  
