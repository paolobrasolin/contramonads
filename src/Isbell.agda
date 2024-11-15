open import Level

open import Categories.Category

open import Categories.Morphism
open import Categories.Adjoint using (_⊣_)

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core

module Isbell {o l e} {C : Category o l e} where

open import Categories.Category.Construction.Presheaves

open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Categories.Yoneda
open Yoneda C

𝓞₀ : Category.Obj (Presheaves C) → Category.Obj (CoPresheaves C)
𝓞₀ P = record 
  { F₀ = λ { x → record 
    { Carrier = Presheaves C [ P , Functor.F₀ embed x ] 
    ; _≈_ = _≃_ 
    ; isEquivalence = ≃-isEquivalence 
    } } 
  ; F₁ = {! !} 
  ; identity = {! !} 
  ; homomorphism = {! !} 
  ; F-resp-≈ = {! !} 
  }

𝓞 : Functor (Presheaves C) (Category.op (CoPresheaves C))
𝓞 = record 
  { F₀ = 𝓞₀ 
  ; F₁ = {! !} 
  ; identity = {! !} 
  ; homomorphism = {! !} 
  ; F-resp-≈ = {! !} 
  }


Spec : Functor (Category.op (CoPresheaves C)) (Presheaves C)
Spec = record 
  { F₀ = {! !} 
  ; F₁ = {! !} 
  ; identity = {! !} 
  ; homomorphism = {! !} 
  ; F-resp-≈ = {! !} 
  }


𝓞⊣S : 𝓞 ⊣ Spec 
𝓞⊣S = record 
  { unit = {! !} 
  ; counit = {! !} 
  ; zig = {! !} 
  ; zag = {! !} 
  }
