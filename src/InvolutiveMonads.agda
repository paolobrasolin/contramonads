{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core

module InvolutiveMonads {o l e} {𝓒 : Category o l e} where

open import Level

open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation.Dinatural renaming (DinaturalTransformation to Dinat)
open import Categories.Category.Product
open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR
open MR 𝓒

open import BetterReasoning 𝓒
open Chain

open import Contramonads

open import Categories.Category.Equivalence using (WeakInverse)
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli

record Involution (C : Category o l e) : Set (o ⊔ l ⊔ e) where
  field
    I   : Functor (Category.op C) C
    inv : WeakInverse I (Functor.op I)

open Involution

record InvolutiveMonad : Set (o ⊔ l ⊔ e) where
  field
    M : Monad 𝓒
    klInvol : Involution (Kleisli M)

open InvolutiveMonad

Contra→Invol : Contramonad {𝓒 = 𝓒} → InvolutiveMonad
Contra→Invol R = record
  { M = 𝐏Monad {R = R}
  ; klInvol = record
    { I = record
      { F₀ = λ x → x
      ; F₁ = λ { {B} {A} f → F.F₁ f ∘ R.η̂ B }
      ; identity = MR.cancelˡ 𝓒 C6
      ; homomorphism = λ { {Z} {Y} {X} {v} {r} → begin -- see p.28, d2
        -- B: F (((F (ι Z) ∘ F (δ Z) ∘ δ (F Z)) ∘ F (ι (F Z)) ∘ F (F v) ∘ δ Y) ∘ r) ∘ δ Z ∘ ι Z
        _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ 𝓒 (Equiv.sym F.homomorphism))) ⟩∘⟨refl ⟩ -- (X ∘ Y) ∘ Z -> (X ∘ A) ∘ (B ∘ Z)
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ MR.pullʳ 𝓒 (MR.pullʳ 𝓒 (Equiv.sym C1)) ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ MR.center 𝓒 (MR.pullʳ 𝓒 (Equiv.sym F.homomorphism)) ⟩
        -- F r ∘ ((F (δ Y) ∘ F (F (F v))) ∘ F (δ (F Z) ∘ F (ι (F Z)))) ∘ (δ (F (F Z)) ∘ ι (F (F Z))) ∘ δ Z ∘ ι Z
        _ ≈⟨ {! !} ⟩
        -- (F r ∘ δ Y) ∘ F v ∘ δ Z ∘ ι Z
        _ ≈⟨ MR.intro-center 𝓒 (F.F-resp-≈ (Equiv.sym C3) ○ F.identity) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ 𝓒 (Equiv.sym F.homomorphism)) ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ Equiv.sym (MR.center 𝓒 (Equiv.sym F.homomorphism)) ⟩∘⟨refl ⟩
        _ ≈⟨ Equiv.sym F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ F.F-resp-≈ (Monad.η.commute (F²Monad {R = R}) r) ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ MR.assoc²γδ 𝓒 ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ Equiv.sym F².homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ C2) ⟩∘⟨refl ⟩
        _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        _ ≈⟨ assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
        -- A: ((F (ι X) ∘ F (δ X) ∘ δ (F X)) ∘ F (ι (F X)) ∘ F (F (F r ∘ δ Y ∘ ι Y)) ∘ δ Y) ∘ F v ∘ δ Z ∘ ι Z
        _ ∎}
      ; F-resp-≈ = λ { x → F.F-resp-≈ x ⟩∘⟨refl }
      }
    ; inv = record 
      { F∘G≈id = record { F⇒G = {! !} ; F⇐G = {! !} ; iso = {! !} } 
      ; G∘F≈id = record { F⇒G = {! !} ; F⇐G = {! !} ; iso = {! !} } 
      }
    }
  } where open module R = Contramonad R

Invol→Contra : (𝓘𝓥 : InvolutiveMonad) → Contramonad {𝓒 = 𝓒}
Invol→Contra 𝓘𝓥 = record
  { F = {!   !} -- Functor.op (Free (M 𝓘𝓥)) ∘F I klInvol 𝓘𝓥 ∘F Forgetful (M 𝓘𝓥)
  ; ι = {!   !}
  ; δ = {!   !}
  ; C1 = {!   !}
  ; C2 = {!   !}
  ; C3 = {!   !}
  ; C4 = {!   !}
  } where 𝐈 = Functor.op (I (klInvol 𝓘𝓥))

