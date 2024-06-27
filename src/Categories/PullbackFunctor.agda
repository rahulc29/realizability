{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Slice

module Categories.PullbackFunctor where

private
  variable
    ℓ ℓ' : Level
module _ (C : Category ℓ ℓ') (pullbacks : Pullbacks C) where
  open Category C
  open Pullback
  open SliceOb
  open SliceHom
  module _ {X Y : ob} (f : Hom[ X , Y ]) where
    module TransformMaps {A B : ob} (m : Hom[ A , Y ]) (n : Hom[ B , Y ]) (k : Hom[ A , B ]) (tri : k ⋆ n ≡ m) where
      cospanA : Cospan C
      cospanA = cospan X Y A f m

      cospanB : Cospan C
      cospanB = cospan X Y B f n

      P : ob
      P = pullbacks cospanA .pbOb

      Q : ob
      Q = pullbacks cospanB .pbOb

      f*m : Hom[ P , X ]
      f*m = pullbacks cospanA .pbPr₁

      g : Hom[ P , A ]
      g = pullbacks cospanA .pbPr₂

      f*n : Hom[ Q , X ]
      f*n = pullbacks cospanB .pbPr₁

      h : Hom[ Q , B ]
      h = pullbacks cospanB .pbPr₂

      f*m⋆f≡g⋆m : f*m ⋆ f ≡ g ⋆ m
      f*m⋆f≡g⋆m = pullbacks cospanA .pbCommutes

      g⋆k : Hom[ P , B ]
      g⋆k = g ⋆ k

      g⋆k⋆n≡f*m⋆f : (g ⋆ k) ⋆ n ≡ f*m ⋆ f
      g⋆k⋆n≡f*m⋆f =
        (g ⋆ k) ⋆ n
          ≡⟨ ⋆Assoc g k n ⟩
        g ⋆ (k ⋆ n)
          ≡⟨ cong (λ x → g ⋆ x) tri ⟩
        g ⋆ m
          ≡⟨ sym f*m⋆f≡g⋆m ⟩
        f*m ⋆ f
          ∎

      arrow : Hom[ P , Q ]
      arrow = pullbackArrow C (pullbacks cospanB) f*m g⋆k (sym g⋆k⋆n≡f*m⋆f)

      arrow⋆f*n≡f*m : arrow ⋆ f*n ≡ f*m
      arrow⋆f*n≡f*m = sym (pullbackArrowPr₁ C (pullbacks cospanB) f*m g⋆k (sym g⋆k⋆n≡f*m⋆f))

    reindexFunctor : Functor (SliceCat C Y) (SliceCat C X)
    Functor.F-ob reindexFunctor (sliceob {A} m) = sliceob (pullbacks (cospan X Y A f m) .pbPr₁)
    Functor.F-hom reindexFunctor {sliceob {A} m} {sliceob {B} n} (slicehom k tri) = slicehom arrow arrow⋆f*n≡f*m where open TransformMaps m n k tri
    Functor.F-id reindexFunctor {sliceob {A} m} = SliceHom-≡-intro' C X (pullbackArrowUnique C (pullbacks cospanB) f*m g⋆k (sym g⋆k⋆n≡f*m⋆f) id (sym (⋆IdL f*m)) (⋆IdR g ∙ sym (⋆IdL g))) where open TransformMaps m m id (⋆IdL m)
    Functor.F-seq reindexFunctor {sliceob {A} m} {sliceob {B} n} {sliceob {C'} o} (slicehom j jComm) (slicehom k kComm) = SliceHom-≡-intro' C X {!!} where
      module ABTransform = TransformMaps m n j jComm
      module BCTransform = TransformMaps n o k kComm
      module ACTransform = TransformMaps m o (j ⋆ k) (⋆Assoc j k o ∙ cong (λ x → j ⋆ x) kComm ∙ jComm)

      P : ob
      P = ABTransform.P

      f*m : Hom[ P , X ]
      f*m = ABTransform.f*m

      Q : ob
      Q = ABTransform.Q

      R : ob
      R = BCTransform.P

      f*n : Hom[ Q , X ]
      f*n = ABTransform.f*n

      g : Hom[ P , A ]
      g = ABTransform.g

      f*m⋆f≡g⋆m : f*m ⋆ f ≡ g ⋆ m
      f*m⋆f≡g⋆m = ABTransform.f*m⋆f≡g⋆m

      
