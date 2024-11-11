{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core
open import Categories.Functor.IdentityOnObjects
open import Agda.Builtin.Sigma
open import Categories.Category.Unbundled renaming (Category to UCategory)

module InvolutiveMonads {o l e} {C : Category o l e} where

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

open import Categories.Category.Equivalence using (WeakInverse)
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli
open import Agda.Builtin.Equality using (_≡_; refl)
open import Categories.Category.Unbundled.Utilities using (op)
open import Categories.Category.Unbundled.Properties using (unpack)

record Involution (C : Category o l e) : Set (o ⊔ l ⊔ e) where
  Cᴼ = Category.op C

  field
    I   : IdentityOnObjects (snd (unpack Cᴼ)) (snd (unpack C))
    -- one can refactor better and use Unbundled's "op"

  module FI = Functor (IOO⇒Functor I)
  𝐈 = IOO⇒Functor I

  field
    inv : WeakInverse 𝐈 (Functor.op 𝐈)

open Involution

record InvolutiveMonad : Set (o ⊔ l ⊔ e) where
  field
    M : Monad C
    klInvol : Involution (Kleisli M)

open InvolutiveMonad


Contra→Invol : Contramonad {𝓒 = C} → InvolutiveMonad
Contra→Invol R = {! !} -- record
  -- { M = 𝐏Monad {R = R}
  -- ; klInvol = record
  --   { I = record
  --     { F₀ = λ x → x
  --     ; F₁ = λ { {B} {A} f → F.F₁ f ∘ R.η̂ B }
  --     ; identity = MR.cancelˡ C C6
  --     ; homomorphism = λ { {Z} {Y} {X} {v} {r} → begin -- see p.28, d2
  --       -- B: F (((F (ι Z) ∘ F (δ Z) ∘ δ (F Z)) ∘ F (ι (F Z)) ∘ F (F v) ∘ δ Y) ∘ r) ∘ δ Z ∘ ι Z
  --       _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
  --       _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ C (Equiv.sym F.homomorphism))) ⟩∘⟨refl ⟩ -- (X ∘ Y) ∘ Z -> (X ∘ A) ∘ (B ∘ Z)
  --       _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
  --       _ ≈⟨ MR.pullʳ C (MR.pullʳ C (Equiv.sym C1)) ⟩
  --       _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
  --       _ ≈⟨ MR.center C (MR.pullʳ C (Equiv.sym F.homomorphism)) ⟩
  --       -- F r ∘ ((F (δ Y) ∘ F (F (F v))) ∘ F (δ (F Z) ∘ F (ι (F Z)))) ∘ (δ (F (F Z)) ∘ ι (F (F Z))) ∘ δ Z ∘ ι Z
  --       _ ≈⟨ {! !} ⟩
  --       -- (F r ∘ δ Y) ∘ F v ∘ δ Z ∘ ι Z
  --       _ ≈⟨ MR.intro-center C (F.F-resp-≈ (Equiv.sym C3) ○ F.identity) ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ C (Equiv.sym F.homomorphism)) ⟩∘⟨refl) ⟩∘⟨refl ⟩
  --       _ ≈⟨ Equiv.sym (MR.center C (Equiv.sym F.homomorphism)) ⟩∘⟨refl ⟩
  --       _ ≈⟨ Equiv.sym F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
  --       _ ≈⟨ F.F-resp-≈ (Monad.η.commute (F²Monad {R = R}) r) ⟩∘⟨refl ⟩∘⟨refl ⟩
  --       _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
  --       _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
  --       _ ≈⟨ MR.assoc²γδ C ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ Equiv.sym F².homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
  --       _ ≈⟨ (refl⟩∘⟨ C2) ⟩∘⟨refl ⟩
  --       _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
  --       _ ≈⟨ assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
  --       -- A: ((F (ι X) ∘ F (δ X) ∘ δ (F X)) ∘ F (ι (F X)) ∘ F (F (F r ∘ δ Y ∘ ι Y)) ∘ δ Y) ∘ F v ∘ δ Z ∘ ι Z
  --       _ ∎}
  --     ; F-resp-≈ = λ { x → F.F-resp-≈ x ⟩∘⟨refl }
  --     }
  --   ; inv = record 
  --     { F∘G≈id = record 
  --       { F⇒G = {! !} 
  --       ; F⇐G = {! !} 
  --       ; iso = {! !} 
  --       } 
  --     ; G∘F≈id = record 
  --       { F⇒G = {! !} 
  --       ; F⇐G = {! !} 
  --       ; iso = {! !} 
  --       } 
  --     }
  --   }
  -- } where open module R = Contramonad R


Invol→Contra : (IM : InvolutiveMonad) → Contramonad {𝓒 = C}
Invol→Contra IM = record
  { F = Forgetful (M IM) ∘F II ∘F Functor.op (Free (M IM))
  ; ι = record 
    { α = λ { X →  M.μ.η X ∘ 𝐈.F₁ id } -- ∘ 𝐈.F₁ id }
    ; commute = {! !} 
    ; op-commute = {! !} 
    }
  ; δ = record 
    { α = λ { X → M.μ.η (M.F.F₀ X) ∘ M.F.F₁ (𝐈.F₁ id) } -- ∘ M.F.F₁ (M.F.F₁ id ∘ M.η.η X) } 
    ; commute = {! !} 
    ; op-commute = {! !} 
    }
  ; C1 = {!   !}
  ; C2 = {!   !}
  ; C3 = {!   !}
  ; C4 = {!   !}
  } where II = IOO⇒Functor (I (klInvol IM))
          module M = Monad (M IM)
          module 𝐈 = Functor II
  

