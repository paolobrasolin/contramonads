{-# OPTIONS --without-K --safe #-}
module MyCategories.Functor.Properties where

-- Properties valid of all Functors
open import Level using (Level)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Function.Base using (_$_)
open import Function.Definitions using (Injective; StrictlySurjective)
open import Relation.Binary using (_Preserves_⟶_)

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Categories.Category.Construction.Core using (module Shorthands)
open import Categories.Functor.Core using (Functor)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as Reas
open import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Morphism.Notation

open Shorthands using (_∘ᵢ_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

module _ (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module IsoC = IsoEquiv C
    module IsoD = IsoEquiv D
  open C hiding (_∘_)
  open Functor F
  open Morphism

  private
    variable
      A B E : Obj
      f g h i : A ⇒ B

  [_]-elim : {f : A ⇒ A} → C [ f ≈ id ] → D [ F₁ f ≈ D.id ]
  [_]-elim {f = f} eq = begin
    F₁ f  ≈⟨ F-resp-≈ eq ⟩
    F₁ id ≈⟨ identity ⟩
    D.id  ∎
    where open D.HomReasoning

