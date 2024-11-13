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
  module R = Contramonad R 
  module S = Contramonad S
  field
    F≡ : NaturalIsomorphism R.F S.F
    -- It would be formally correct to have also the fields
    --   ι≡ : ∀ {X} → (R.ι.α X) ≈ S.ι.α X
    --   δ≡ : ∀ {X} → (R.δ.α X) ≈ S.δ.α X 
    -- but they would introduce coherences that we would not know 
    -- how to cancel. 


record InvolutiveMonad≡ (A B : InvolutiveMonad) : Set _ where
  module 𝐀 = InvolutiveMonad A
  module 𝐁 = InvolutiveMonad B
  module Mᴬ = Monad (𝐀.M)
  module Mᴮ = Monad (𝐁.M)
  field
    M≡ : NaturalIsomorphism Mᴬ.F Mᴮ.F



  -- CHEATSHEET
  -- C1 : (δ B ∘ ι B) ∘ f             ≈ F² f ∘ δ A ∘ ι A
  -- C2 : F² f ∘ δ A                  ≈ δ B ∘ F (ι B) ∘ F² f ∘ δ A
  -- C3 : id                          ≈ F (ι A) ∘ F (δ A) ∘ δ (F A) ∘ ι (F A)
  -- C4 : F (δ A) ∘ δ (F A)           ≈ δ A ∘ F (ι A) ∘ F (δ A) ∘ δ (F A)
  -- C5 : F (δ A) ∘ F (F² f)          ≈ F (δ A) ∘ F (F² f) ∘ F² (ι B) ∘ F (δ B)
  -- C6 : F (ι X) ∘ δ X               ≈ id
  -- C7 : F (δ X) ∘ δ (F X) ∘ ι (F X) ≈ δ X
  -- C8 : F (δ X)                     ≈ F (δ (F X) ∘ ι (F X)) ∘ F² (δ X)
Theorem⇒ : (R : Contramonad {𝓒 = C}) → Contramonad≡ R (Invol→Contra (Contra→Invol R))
Theorem⇒ R = let open module R = Contramonad R in record 
  { F≡ = record 
    { F⇒G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → 
        begin {! !} ≈⟨ identityˡ ⟩
              {! !} ≈⟨ {! !} ⟩ 
              {! !} ≈˘⟨ refl⟩∘⟨ MR.cancelˡ C C6 ⟩
              {! !} ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ C2 ⟩
              {! !} ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (MR.elim-center C Equiv.refl) ⟩∘⟨refl) ⟩ -- ugly
              {! !} ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (MR.center C C6) ⟩∘⟨refl) ⟩ 
              {! !} ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (Equiv.sym F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl) ⟩ 
              {! !} ≈˘⟨ identityʳ ⟩ 
              {! !} ∎ }
      }) 
-- (F (ι Y) ∘ F (δ Y) ∘ δ (F Y)) ∘ F (ι (F Y)) ∘ F (F (F f ∘ ι X)) ∘ δ X
    ; F⇐G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → 
        begin {! !} ≈⟨ {! !} ⟩
              {!!} ≈⟨ {! !} ⟩ 
              {! !} ∎ }
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
  } where module 𝐀 = InvolutiveMonad 𝐀
          open module C = Category C
          module IOO = IdentityOnObjects 𝐀.Inv.I
  
