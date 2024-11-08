{-# OPTIONS --without-K --safe #-}
module MyCategories.Monad {o ℓ e} where

open import Level

open import Categories.Category using (Category)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open NaturalIsomorphism

record monadMap {C : Category o ℓ e} (S : Monad C) (T : Monad C) : Set (o ⊔ ℓ ⊔ e) where
  field
    α : NaturalTransformation (Monad.F S) (Monad.F T)

  module α = NaturalTransformation α
  module S = Monad.F S
  module T = Monad.F T

  open Category C
  open S
  open T
  open α

  field
    resp-id : ∀ {X : Obj} → Monad.η.η T X ≈ α.η X ∘ Monad.η.η S X
    resp-mu : ∀ {X : Obj} → α.η X ∘ Monad.μ.η S X ≈ (Monad.μ.η T X ∘ NaturalTransformation.η (α ∘ₕ α) X)
