{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Slice
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Categories.PullbackFunctor

module Realizability.Assembly.Reindexing {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a) hiding (Z)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Pullbacks ca
-- Using pullbacks we get a functor that sends any f : X → Y to f* : Asm / Y → Asm / X
module _ {X Y : Type ℓ} {asmX : Assembly X} {asmY : Assembly Y} (f : AssemblyMorphism asmX asmY) where

  open TransformMaps ASM PullbacksASM f
  open SliceOb
  open SliceHom
  open Pullback

  opaque
    reindexPb : {A : Type ℓ} (asmA : Assembly A) (m : AssemblyMorphism asmA asmY) → ASM .Category.ob
    reindexPb {A} asmA m = pullback (cospan (X , asmX) (Y , asmY) (A , asmA) f m) .pbOb

  opaque
    reindexOb : SliceOb ASM (Y , asmY) → SliceOb ASM (X , asmX)
    reindexOb (sliceob {A , asmA} m) = sliceob (pullback (cospan (X , asmX) (Y , asmY) (A , asmA) f m) .pbPr₁)

  opaque
    unfolding reindexOb
    reindexHom : (m n : SliceOb ASM (Y , asmY)) → SliceHom ASM (Y , asmY) m n → SliceHom ASM (X , asmX) (reindexOb m) (reindexOb n)
    reindexHom (sliceob {A , asmA} m) (sliceob {B , asmB} n) (slicehom k tri) = slicehom (arrow m n k tri) (arrow⋆f*n≡f*m m n k tri)

