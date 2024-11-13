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


record InvolutiveMonad≡ (A B : InvolutiveMonad {C = C}) : Set _ where
  module 𝐀 = InvolutiveMonad A
  module 𝐁 = InvolutiveMonad B
  module Mᴬ = Monad (𝐀.M)
  module Mᴮ = Monad (𝐁.M)
  field
    M≡ : NaturalIsomorphism Mᴬ.F Mᴮ.F



Theorem⇒ : (R : Contramonad {𝓒 = C}) → Contramonad≡ R (Invol→Contra (Contra→Invol R))
Theorem⇒ R = let open module R = Contramonad R in record 
  { F≡ = record 
    { F⇒G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → 
        begin _ ≈⟨ identityˡ ⟩
              _ ≈˘⟨ MR.cancelʳ C C6 ⟩ 
              _ ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ (F.F-resp-≈ (MR.elimˡ C C6)) ⟩∘⟨refl ⟩ 
              _ ≈⟨ (F.F-resp-≈ (MR.assoc²γδ C)) ⟩∘⟨refl ⟩ 
              _ ≈⟨ F.F-resp-≈ (refl⟩∘⟨ C1) ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ F.F-resp-≈ (MR.assoc²αε C) ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ F.F-resp-≈ (F.homomorphism ⟩∘⟨refl ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
              _ ≈⟨ homomorphism₃ F ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ sym-assoc ⟩ 
              _ ≈˘⟨ MR.assoc²γδ C ⟩ 
              _ ≈⟨ refl⟩∘⟨ C2 ⟩ 
              _ ≈⟨ sym-assoc ⟩ 
              _ ≈⟨ assoc ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ refl⟩∘⟨ MR.cancelˡ C C6 ⟩
              _ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ C2 ⟩
              _ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (MR.elim-center C Equiv.refl) ⟩∘⟨refl) ⟩ -- ugly
              _ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (MR.center C C6) ⟩∘⟨refl) ⟩ 
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (F².F-resp-≈ (Equiv.sym F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl) ⟩ 
              _ ≈˘⟨ identityʳ ⟩ 
              _ ∎ }
      }) 
    ; F⇐G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → 
        begin _ ≈⟨ identityˡ ⟩
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F².F-resp-≈ (F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F².F-resp-≈ (MR.assoc²γδ C) ⟩∘⟨refl ⟩ 
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F².F-resp-≈ (MR.elim-center C C6) ⟩∘⟨refl ⟩ 
              _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C2 ⟩ 
              _ ≈⟨ refl⟩∘⟨ MR.cancelˡ C C6 ⟩ 
              _ ≈⟨ sym-assoc ⟩∘⟨refl ⟩ 
              _ ≈⟨ assoc ⟩ 
              _ ≈˘⟨ refl⟩∘⟨ C2 ⟩ 
              _ ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ assoc ⟩ 
              _ ≈˘⟨ F.homomorphism ⟩∘⟨refl ⟩ 
              _ ≈⟨ F.F-resp-≈ (F.homomorphism ⟩∘⟨refl) ⟩∘⟨refl ⟩ 
              _ ≈⟨ F.F-resp-≈ assoc ⟩∘⟨refl ⟩ 
              _ ≈˘⟨ F.F-resp-≈ (refl⟩∘⟨ C1) ⟩∘⟨refl ⟩ 
              _ ≈⟨ F.F-resp-≈ (MR.assoc²δγ C) ⟩∘⟨refl ⟩ 
              _ ≈⟨ F.F-resp-≈ (MR.elimˡ C C6) ⟩∘⟨refl ⟩ 
              _ ≈⟨ ∘-resp-≈ˡ F.homomorphism  ⟩ 
              _ ≈⟨  MR.cancelʳ C C6  ⟩ 
              _ ≈˘⟨ identityʳ ⟩ 
              _ ∎ }
      }) 
    ; iso = λ { X → record 
      { isoˡ = identity² 
      ; isoʳ = identity² 
      } }
    } 
  } 


Theorem⇐ : (𝐀 : InvolutiveMonad {C = C}) → InvolutiveMonad≡ 𝐀 (Contra→Invol (Invol→Contra 𝐀))
Theorem⇐ 𝐀 = record 
  { M≡ = record
    { F⇒G = ntHelper (record 
      { η = λ { X → id } 
      ; commute = λ { f → 
        begin {! !} ≈⟨ identityˡ ⟩
              {! !} ≈⟨ {! !} ⟩ --1 
              {! !} ≈˘⟨ identityʳ ⟩
              {! !} ∎ }
      }) 
    ; F⇐G = ntHelper (record
      { η = λ { X → id } 
      ; commute = λ { f →
        begin {! !} ≈⟨ identityˡ ⟩
              {! !} ≈⟨ {! !} ⟩ --2
              {! !} ≈˘⟨ identityʳ ⟩
              {! !} ∎ }
      }) 
    -- these two are _exactly_ the same goals up to Equiv.sym.
    ; iso = λ { X → record 
      { isoˡ = identity² 
      ; isoʳ = identity² 
      } }
    } 
  } where module 𝐀 = InvolutiveMonad 𝐀
          module IOO = IdentityOnObjects 𝐀.Inv.I
          module M = Monad 𝐀.M
  
