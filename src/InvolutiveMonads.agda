{-# OPTIONS --without-K --allow-unsolved-metas #-}

-- see p.8 for statement and p.14 for proof

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Category.Core
open import Categories.Functor.IdentityOnObjects
open import Agda.Builtin.Sigma
open import Categories.Category.Unbundled renaming (Category to UCategory)
open import Categories.Morphism using (Iso)

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
open import Categories.Category.Unbundled.Properties using (pack′;unpack′)

record Involution (C : Category o l e) : Set (o ⊔ l ⊔ e) where
  Cᴼ = Category.op C

  field
    I   : IdentityOnObjects (unpack′ Cᴼ) (unpack′ C)
    -- one can refactor better and use Unbundled's "op"

  module FI = Functor (IOO⇒Functor I)
  𝐈 = IOO⇒Functor I

  field
    inv : WeakInverse 𝐈 (Functor.op 𝐈)

  open module inv = WeakInverse inv public

open Involution

record InvolutiveMonad : Set (o ⊔ l ⊔ e) where
  field
    M : Monad C
    klInvol : Involution (Kleisli M)

  open module Inv = Involution klInvol public

open InvolutiveMonad
open IdentityOnObjects

sblemma : (IM : InvolutiveMonad) → ∀ {X : Obj} → F₁ (I (klInvol IM)) (Monad.η.η (M IM) X ∘ id) ≈ Monad.η.η (M IM) X
sblemma IM = begin
      _ ≈⟨ F-resp-≈ (I (klInvol IM)) identityʳ ⟩
      _ ≈⟨ identity (I (klInvol IM)) ⟩
      _ ∎

Contra→Invol : Contramonad {𝓒 = C} → InvolutiveMonad
Contra→Invol R = record
  { M = 𝐏Monad {R = R}
  ; klInvol = record
    { I = record
      { F₁ = λ { {B} {A} f → F.F₁ f ∘ R.η̂ B }
      ; identity = MR.cancelˡ C C6
      ; homomorphism = {! !} -- λ { {Z} {Y} {X} {v} {r} → begin -- see p.28, d2
{-
        _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ C (Equiv.sym F.homomorphism))) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ MR.pullʳ C (MR.pullʳ C (Equiv.sym C1)) ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ MR.center C (MR.pullʳ C (Equiv.sym F.homomorphism)) ⟩
        -- F r ∘ ((F (δ Y) ∘ F (F (F v))) ∘ F (δ (F Z) ∘ F (ι (F Z)))) ∘ (δ (F (F Z)) ∘ ι (F (F Z))) ∘ δ Z ∘ ι Z
        _ ≈⟨ {! !} ⟩
        -- (F r ∘ δ Y) ∘ F v ∘ δ Z ∘ ι Z
        _ ≈⟨ MR.intro-center C (F.F-resp-≈ (Equiv.sym C3) ○ F.identity) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (MR.pullˡ C (Equiv.sym F.homomorphism)) ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ Equiv.sym (MR.center C (Equiv.sym F.homomorphism)) ⟩∘⟨refl ⟩
        _ ≈⟨ Equiv.sym F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ F.F-resp-≈ (Monad.η.commute (F²Monad {R = R}) r) ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl
_ ≈⟨ F.homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ≈⟨ MR.assoc²γδ C ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ Equiv.sym F².homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩
        _ ≈⟨ (refl⟩∘⟨ C2) ⟩∘⟨refl ⟩
        _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        _ ≈⟨ assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
        _ ∎}
-}
      ; F-resp-≈ = λ { x → F.F-resp-≈ x ⟩∘⟨refl }
      }
    ; inv = record
        -- CHEATSHEET
        -- C1 : (δ B ∘ ι B) ∘ f             ≈ F² f ∘ δ A ∘ ι A
        -- C2 : F² f ∘ δ A                  ≈ δ B ∘ F (ι B) ∘ F² f ∘ δ A
        -- C3 : id                          ≈ F (ι A) ∘ F (δ A) ∘ δ (F A) ∘ ι (F A)
        -- C4 : F (δ A) ∘ δ (F A)           ≈ δ A ∘ F (ι A) ∘ F (δ A) ∘ δ (F A)
        -- C5 : F (δ A) ∘ F (F² f)          ≈ F (δ A) ∘ F (F² f) ∘ F² (ι B) ∘ F (δ B)
        -- C6 : F (ι X) ∘ δ X               ≈ id
        -- C7 : F (δ X) ∘ δ (F X) ∘ ι (F X) ≈ δ X
        -- C8 : F (δ X)                     ≈ F (δ (F X) ∘ ι (F X)) ∘ F² (δ X)
      { F∘G≈id = niHelper (record 
        { η = ι.α
        ; η⁻¹ = ι.α
        ; commute = λ { f → begin
            _ ≈⟨ {! !} ⟩ 
            _ ≈⟨ {! !} ⟩ 
            _ ∎ }
          -- ((F (ι Y) ∘ F (δ Y) ∘ δ (F Y)) ∘ F (ι (F Y)) ∘ F (F (ι Y)) ∘ δ Y) ∘ F (F f ∘ δ Y ∘ ι Y) ∘ δ X ∘ ι X
          -- ≈
          -- ((F (ι Y) ∘ F (δ Y) ∘ δ (F Y)) ∘ F (ι (F Y)) ∘ F (F f) ∘ δ X) ∘ ι X
        ; iso = λ { X → record 
          { isoˡ = begin
            _ ≈⟨ {! !} ⟩ 
            _ ≈⟨ {! !} ⟩ 
            _ ∎
          --((F (ι X) ∘ F (δ X) ∘ δ (F X)) ∘ F (ι (F X)) ∘ F (F (ι X)) ∘ δ X) ∘ ι X 
          --≈ 
          --ι X
          ; isoʳ = begin
            _ ≈⟨ {! !} ⟩ 
            _ ≈⟨ {! !} ⟩ 
            _ ∎ }
          --((F (ι X) ∘ F (δ X) ∘ δ (F X)) ∘ F (ι (F X)) ∘ F (F (ι X)) ∘ δ X) ∘ ι X
          --≈ 
          --ι X
          }
        })
      ; G∘F≈id = niHelper (record 
        { η = ι.α
        ; η⁻¹ = ι.α
        ; commute = λ { f → {! !} }
          --((F (ι X) ∘ F (δ (F X)) ∘ F (ι (F X)) ∘ F (F (F (F f ∘ δ X ∘ ι X) ∘ δ Y ∘ ι Y)) ∘ δ Y) ∘ ι Y
          --≈
          --((F (ι X) ∘ F (δ X) ∘ δ (F X)) ∘ F (ι (F X)) ∘ F (F (ι X)) ∘ δ X) ∘ f
        ; iso = λ { X → record 
          { isoˡ = {! !} 
          ; isoʳ = {! !} } 
          }
        })
      }
    }
  } where open module R = Contramonad R


module _ {T : Monad C} where
  module T = Monad T
  lemma-lemmino : ∀ {X Y} {f : X ⇒ T.F.F₀ Y} → T.μ.η Y ∘ T.F.F₁ (T.μ.η Y ∘ T.F.F₁ f) ≈ T.μ.η Y ∘ T.F.F₁ f ∘ T.μ.η X
  lemma-lemmino {X} {Y} {f} = begin
      _ ≈˘⟨ MR.pullʳ C (Equiv.sym T.F.homomorphism) ⟩
      _ ≈⟨ T.assoc ⟩∘⟨refl ⟩
      _ ≈⟨ assoc ⟩
      _ ≈⟨ refl⟩∘⟨ T.μ.commute f ⟩
      _ ∎

Invol→Contra : (IM : InvolutiveMonad) → Contramonad {𝓒 = C}
Invol→Contra IM = let IOO = I (klInvol IM)
                      𝐈 = IOO⇒Functor IOO
                      module IOO = IdentityOnObjects IOO
                      module IM = InvolutiveMonad IM
                      module 𝐈 = Functor 𝐈 in record
  { F = Forgetful IM.M ∘F 𝐈 ∘F Functor.op (Free IM.M)
  ; ι = record
    { α = λ { X → M.μ.η X ∘ 𝐈.F₁ (M.F.F₁ (M.η.η X)) ∘ M.η.η X
    -- M.μ.η X ∘ 𝐈.F₁ (id {M.F.F₀ X}) }
    -- M.μ.η X ∘ 𝐈.F₁ id
    }
    ; commute = λ { {X} {Y} f → begin
      {! !} ≈⟨ refl⟩∘⟨ identityʳ ⟩
      {! !} ≈⟨ (refl⟩∘⟨ M.F.F-resp-≈ (IOO.F-resp-≈ identityʳ)) ⟩∘⟨refl ⟩
      {! !} ≈⟨ (refl⟩∘⟨ M.F.F-resp-≈ IOO.identity) ⟩∘⟨refl ⟩
      {! !} ≈⟨ M.identityˡ ⟩∘⟨refl ⟩
      {! !} ≈⟨ identityˡ ⟩
      --{! !} ≈⟨ {! lemma-lemmino !} ⟩∘⟨refl ⟩
      {! !} ≈⟨ {! !}  ⟩
      {! !} ∎ }
    {-
μ X ∘ I id
≈
(μ X ∘ M (I (η Y ∘ f))) ∘ (μ Y ∘ I id) ∘ f
-- dis : (M.μ.η Y ∘ M.F.F₁ (IM.F∘G≈id.⇒.η Y)) ∘ IM.F∘G≈id.⇐.η Y ≈ M.η.η Y
-- dat : (M.μ.η Y ∘ M.F.F₁ (IM.F∘G≈id.⇐.η Y)) ∘ IM.F∘G≈id.⇒.η Y ≈ M.η.η Y
     -}
    ; op-commute = λ { f → {! !} }
    }
  ; δ = record
    { α = λ { X → 𝐈.F₁ (M.F.F₁ (M.η.η X))
    -- M.F.F₁ (M.μ.η X ∘ 𝐈.F₁ (id {M.F.F₀ X})) }
    -- M.μ.η (M.F.F₀ X) ∘ M.F.F₁ ({! !} ∘ 𝐈.F₁ id) }
    --  M.F.F₁ (M.μ.η X ∘ 𝐈.F₁ id)
    }
    ; commute = λ { {X} {Y} f → begin
     {! !} ≈⟨ {!   !} ⟩
     --{! !} ≈⟨ {! !} ⟩ -- {! 𝐈.homomorphism {g = M.η.η Y ∘ f}  !} ⟩
     {! !} ≈˘⟨ MR.elimˡ C M.identityˡ ⟩
     {! !} ≈˘⟨ (refl⟩∘⟨ M.F.F-resp-≈ 𝐈.identity) ⟩∘⟨refl ⟩
     {! !} ≈˘⟨ (refl⟩∘⟨ M.F.F-resp-≈ (𝐈.F-resp-≈ (MR.elimʳ C M.identityˡ))) ⟩∘⟨refl ⟩
     {! !} ≈˘⟨ refl⟩∘⟨ MR.elimʳ C M.identityˡ ⟩
     {! !} ≈˘⟨ (refl⟩∘⟨ M.F.F-resp-≈ (𝐈.F-resp-≈ (skip-2 (M.F.F-resp-≈ (sblemma IM))))) ⟩∘⟨refl ⟩
     {! !} ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ∘-resp-≈ʳ (M.F.F-resp-≈ (sblemma IM)) ⟩
     {! !} ∎ }
    ; op-commute = λ { f → {! !} }
    }
  ; C1 = λ { {A} {B} {f} → {!  !} }
  ; C2 = λ { {A} {B} {f} → {! !} }
  ; C3 = λ { {A} → {! !} }
  ; C4 = λ { {A} → {! !} }
  } where module M = Monad (M IM)
          module 𝕚 X = Iso (F∘G≈id.iso IM X)

