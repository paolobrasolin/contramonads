{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core
open import Categories.Functor.IdentityOnObjects
open import Agda.Builtin.Sigma
open import Categories.Category.Unbundled renaming (Category to UCategory)

module Equivalent {o l e} {C : Category o l e} where

open import Level

open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation.Dinatural renaming (DinaturalTransformation to Dinat)
open import Categories.Category.Product
open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR
open MR C

open import BetterReasoning C
open Chain

open import Contramonads
open import InvolutiveMonads

open import Categories.Category.Equivalence using (WeakInverse)
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli
open import Agda.Builtin.Equality using (_≡_; refl)
open import Categories.Category.Unbundled.Utilities using (op)
open import Categories.Category.Unbundled.Properties using (pack′;unpack′)


record Contramonad≡ (R S : Contramonad {𝓒 = C}) : Set _ where
  open module R = Contramonad R 
  open module S = Contramonad S
  field
    F≡ : NaturalIsomorphism R.F S.F
    --ι≡ : ∀ {X} → (R.ι.α X) ≈ {! S.ι.α X  !} 
    --δ≡ : ∀ {X} → (R.δ.α X) ≈ {! S.δ.α X  !} 


record InvolutiveMonad≡ (A B : InvolutiveMonad) : Set _ where
  open module 𝐀 = InvolutiveMonad A
  open module 𝐁 = InvolutiveMonad B
  open module Mᴬ = Monad (𝐀.M)
  open module Mᴮ = Monad (𝐁.M)
  field
    M≡ : NaturalIsomorphism Mᴬ.F Mᴮ.F



Theorem⇒ : (R : Contramonad {𝓒 = C}) → Contramonad≡ R (Invol→Contra (Contra→Invol R))
Theorem⇒ R =  record 
  { F≡ = record 
    { F⇒G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → {! !} }
      }) 
    ; F⇐G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → {! !} }
      }) 
    ; iso = λ { X → record 
      { isoˡ = identity² 
      ; isoʳ = identity² 
      } }
    } 
  }


Theorem⇐ : (𝐀 : InvolutiveMonad) → InvolutiveMonad≡ 𝐀 (Contra→Invol (Invol→Contra 𝐀))
Theorem⇐ 𝐀 = record 
  { M≡ = record
    { F⇒G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → {! !} }
      }) 
    ; F⇐G = ntHelper (record
      { η = λ { X → id } 
      ; commute = λ { f → {! !} }
      }) 
    ; iso = λ { X → record 
      { isoˡ = identity² 
      ; isoʳ = identity² 
      } }
    } 
  }
  
