{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_; Endofunctor) renaming (id to idF)
open import MyCategories.Functor.Properties using ([_]-elim)
-- open import Categories.Category.Core

module Contramonads {o l e} {𝓒 : Category o l e} where

open import Level

open import Categories.Monad using (Monad)
open import MyCategories.Monad using (monadMap)
open import Categories.NaturalTransformation.Dinatural renaming (DinaturalTransformation to Dinat)
open Dinat
open import Categories.Category.Product using (Product; πˡ; πʳ)
open import Categories.NaturalTransformation.Core renaming (id to idN)
-- open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism.Reasoning as MR
open MR 𝓒

open import BetterReasoning 𝓒
open Chain

private
  variable
    o' l' e' : Level
    𝓓 : Category o' l' e'

_ᵒ×_ : (𝓐 : Category o l e) → (𝓑 : Category o' l' e') → Category (o ⊔ o') (l ⊔ l') (e ⊔ e')
𝓐 ᵒ× 𝓑 = Product (Category.op 𝓐) 𝓑

liftF⁻ : Functor 𝓒 𝓓 → Functor (𝓒 ᵒ× 𝓒) 𝓓
liftF⁻ F = F ∘F πʳ

liftF⁺ : Functor (Category.op 𝓒) 𝓓 → Functor (𝓒 ᵒ× 𝓒) 𝓓
liftF⁺ F = F ∘F πˡ

module _ {H : Functor 𝓒 𝓒} {G : Functor (Category.op 𝓒) 𝓒} where
  open module H = Functor H
  open module G = Functor G

  antiCommute⁻⁺ : (θ : Dinat (liftF⁻ H) (liftF⁺ G)) → ∀ {A B} {f : A ⇒ B} → G.F₁ f ∘ α θ B ∘ H.F₁ f ≈ α θ A
  antiCommute⁻⁺ θ {A} {B} {f} = Equiv.sym (θ.commute f) ∙ elimˡ G.identity ∙ elimʳ H.identity
    where open module θ = Dinat θ

  antiCommute⁺⁻ : (θ : Dinat (liftF⁺ G) (liftF⁻ H)) → ∀ {A B} {f : A ⇒ B} → H.F₁ f ∘ α θ A ∘ G.F₁ f ≈ α θ B
  antiCommute⁺⁻ θ {A} {B} {f} = θ.commute f ∙ elimˡ H.identity ∙ elimʳ G.identity
    where open module θ = Dinat θ

record Contramonad : Set (o ⊔ l ⊔ e) where
  field
    F : Functor (Category.op 𝓒) 𝓒
    ι : Dinat (liftF⁻ idF) (liftF⁺ F)

  F² = F ∘F Functor.op F

  field
    δ : Dinat (liftF⁺ F) (liftF⁻ F²)

  module F = Functor F
  module ι = Dinat ι
  module δ = Dinat δ
  module F² = Functor F²

  -- AXIOMS CHEATSHEET
  -- C1 : (δ B ∘ ι B) ∘ f             ≈ F² f ∘ δ A ∘ ι A
  -- C2 : F² f ∘ δ A                  ≈ δ B ∘ F (ι B) ∘ F² f ∘ δ A
  -- C3 : id                          ≈ F (ι A) ∘ F (δ A) ∘ δ (F A) ∘ ι (F A)
  -- C4 : F (δ A) ∘ δ (F A)           ≈ δ A ∘ F (ι A) ∘ F (δ A) ∘ δ (F A)
  -- C5 : F (δ A) ∘ F (F² f)          ≈ F (δ A) ∘ F (F² f) ∘ F² (ι B) ∘ F (δ B)
  -- C6 : F (ι X) ∘ δ X               ≈ id
  -- C7 : F (δ X) ∘ δ (F X) ∘ ι (F X) ≈ δ X
  -- C8 : F (δ X)                     ≈ F (δ (F X) ∘ ι (F X)) ∘ F² (δ X)

  field
    C1 : ∀ {A B : Obj} {f : A ⇒ B} →
      (δ.α B ∘ ι.α B) ∘ f ≈ F².F₁ f ∘ δ.α A ∘ ι.α A
    C2 : ∀ {A B : Obj} {f : A ⇒ B} →
      F².F₁ f ∘ δ.α A ≈ δ.α B ∘ F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A
    C3 : ∀ {A : Obj} →
      id ≈ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
    C4 : ∀ {A : Obj} →
      F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ≈ δ.α A ∘ F.F₁ (ι.α A) ∘ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A)

  η̂ : ∀ (X : Obj) → X ⇒ F².F₀ X
  η̂ X = δ.α X ∘ ι.α X

  𝐏 : ∀ {A B : Obj} (f : A ⇒ B) → F.F₀ A ⇒ F.F₀ B
  𝐏 {A} {B} f = F.F₁ (ι.α B) ∘ F².F₁ f ∘ δ.α A

  μ̂ : ∀ {X : Obj} → F².F₀ X ⇒ F.F₀ X
  μ̂ {X} = F.F₁ (ι.α X) ∘ F.F₁ (δ.α X) ∘ δ.α (F.F₀ X)

  module _ where
    open Functor

    C5 : ∀ {A B : Obj} (f : A ⇒ B) →
      F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ≈ F.F₁ (δ.α A) ∘ F.F₁ (F².F₁ f) ∘ F².F₁ (ι.α B) ∘ F.F₁ (δ.α B)
    C5 f =
      Equiv.sym (homomorphism F) ∙
      F.F-resp-≈ C2 ∙
      F.F-resp-≈ (sym-assoc ∙ sym-assoc) ∙
      homomorphism₄ F

    𝐏-unit-lemma : ∀ {A : Obj} → δ.α A ≈ F.F₁ (δ.α A) ∘ δ.α (F.F₀ A) ∘ ι.α (F.F₀ A)
    𝐏-unit-lemma =
      begin
      _ ≈˘⟨ identityʳ ⟩
      _ ≈⟨ (refl⟩∘⟨ C3) ⟩
      _ ≈˘⟨ assoc ○ assoc ○ assoc ⟩
      _ ≈⟨ ((assoc ○ assoc ○ Equiv.sym C4 ) ⟩∘⟨refl) ⟩
      _ ≈⟨ assoc ⟩
      _ ∎ -- TODO: refactor

    C6 : ∀ {X : Obj} →
      F.F₁ (ι.α X) ∘ δ.α X ≈ id
    C6 {X} = (refl⟩∘⟨ 𝐏-unit-lemma) ○ Equiv.sym C3

    C7 : ∀ {X : Obj} →
      F.F₁ (δ.α X) ∘ η̂ (F.F₀ X) ≈ δ.α X
    C7 {X} = begin
      _ ≈⟨ pullˡ C4 ⟩
      _ ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ (refl⟩∘⟨ (refl⟩∘⟨ assoc)) ⟩ -- TODO: refactor ugly assoc.
      _ ≈⟨  elimʳ (Equiv.sym C3) ⟩
      _ ∎

    C8 : ∀ {X : Obj} →
      F.F₁ (δ.α X) ≈ F.F₁ (η̂ (F.F₀ X)) ∘ F².F₁ (δ.α X)
    C8 {X} = F-resp-≈ F (Equiv.sym C7) ○ homomorphism F

    𝐏Functor : Endofunctor 𝓒
    𝐏Functor = record
      { F₀ = λ X → F₀ F X
      ; F₁ = λ f → 𝐏 f
      ; identity = λ { {A} → elim-center (identity F²) ○ C6 }
      ; homomorphism = λ { {X} {Y} {Z} {f} {g} → Equiv.sym (
        assoc ∙ (refl⟩∘⟨ assoc) ∙
        (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym C2) ∙
        pull-center (Equiv.sym (homomorphism F²))
        )}
      ; F-resp-≈ = λ f≈g → refl⟩∘⟨ (F-resp-≈ F² f≈g ⟩∘⟨refl)
      } where open Functor

module _ {R : Contramonad} where

  open Contramonad R

  F²Monad : Monad 𝓒
  F²Monad = record
    { F = F²
    ; η = ntHelper (record
      { η = λ X → η̂ X
      ; commute = λ _ → C1
      })
    ; μ = ntHelper (record
      { η = λ X → F₁ F (δ.α (F₀ F X) ∘ ι.α (F₀ F X))
      ; commute = λ f → begin
        _ ≈˘⟨ homomorphism F ⟩
        _ ≈⟨ F-resp-≈ F (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym (antiCommute⁻⁺ ι {f = F.F₁ f}))) ⟩
        _ ≈⟨ F-resp-≈ F (sym-assoc ○ sym-assoc ○ sym-assoc) ⟩
        _ ≈⟨ F-resp-≈ F (assoc ○ assoc ⟩∘⟨refl) ⟩
        _ ≈⟨ F-resp-≈ F sym-assoc ⟩
        _ ≈⟨ F-resp-≈ F ((antiCommute⁺⁻ δ {f = F.F₁ f} ⟩∘⟨refl) ⟩∘⟨refl) ⟩
        _ ≈⟨ homomorphism F ⟩
        _ ∎
      })
    ; assoc = λ { {X} → begin
        _ ≈˘⟨ homomorphism F ⟩
        _ ≈˘⟨ F-resp-≈ F C1 ⟩
        _ ≈⟨ homomorphism F ⟩
        _ ∎
        }
    ; sym-assoc = λ { {X} → begin
        _ ≈˘⟨ homomorphism F ⟩
        _ ≈⟨ F-resp-≈ F C1 ⟩
        _ ≈⟨ homomorphism F ⟩
        _ ∎
        }
    ; identityˡ = λ { {X} →
      Equiv.sym (homomorphism F) ∙
      F-resp-≈ F (homomorphism F ⟩∘⟨refl) ∙
      F-resp-≈ F assoc ∙
      F-resp-≈ F (Equiv.sym C3) ∙
      identity F }
    ; identityʳ = λ {X} →
      (homomorphism F ⟩∘⟨refl) ∙
      assoc ∙
      Equiv.sym C3
    } where open Functor

  𝐏Monad : Monad 𝓒
  𝐏Monad = record
    { F = 𝐏Functor
    ; η = ntHelper (record
      { η = λ X → ι.α X
      ; commute = λ { {X} {Y} f →
        Equiv.sym (pullʳ (assoc ∙ Equiv.sym C1) ∙
        assoc²δγ ∙
        elimˡ C6)}
      })
    ; μ = ntHelper (record
      { η = λ X → μ̂ {X}
      ; commute = λ { {X} {Y} f → begin -- see p.26, b4
          _ ≈⟨ assoc²βγ ⟩
          _ ≈⟨ refl⟩∘⟨ Equiv.sym C2 ⟩
          _ ≈⟨ assoc²γδ ⟩
          _ ≈⟨ refl⟩∘⟨ Equiv.sym (pullˡ (Equiv.sym C8)) ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ ( refl⟩∘⟨ (Equiv.sym (homomorphism F²))) ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ ( refl⟩∘⟨ (F-resp-≈ F² (Equiv.sym C2) )) ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ ( refl⟩∘⟨ (homomorphism F²)) ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym (homomorphism F)) ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ F-resp-≈ F (Equiv.sym C1) ⟩∘⟨refl ⟩∘⟨refl ⟩
          _ ≈⟨ Equiv.sym (center (pullˡ (Equiv.sym (homomorphism F)))) ⟩
          _ ≈⟨ refl⟩∘⟨ Equiv.sym C8 ⟩∘⟨refl ⟩
          _ ≈⟨ refl⟩∘⟨ C4 ⟩
          _ ≈⟨ assoc²γβ ⟩
          _ ∎
          }
      })
    ; assoc = λ { {X} → begin
        _ ≈⟨ assoc²βγ ⟩
        _ ≈⟨ Equiv.sym (homomorphism F) ⟩∘⟨refl ⟩
        _ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ F-resp-≈ F² (pullˡ (Equiv.sym (homomorphism F))) ⟩∘⟨refl ⟩
        _ ≈⟨ refl⟩∘⟨ Equiv.sym C2 ⟩
        _ ≈⟨ push-center (Equiv.sym (homomorphism F²)) ⟩
        _ ≈⟨ pullˡ (Equiv.sym (homomorphism F)) ⟩
        _ ≈⟨ F-resp-≈ F (Equiv.sym C1) ⟩∘⟨refl ⟩
        _ ≈⟨ pushˡ (homomorphism F) ⟩
        _ ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym C8) ⟩
        _ ≈⟨ homomorphism F ⟩∘⟨ C4 ⟩
        _ ≈⟨ assoc²γβ ⟩
        _ ∎
        }
    ; sym-assoc = λ { {X} → begin
        _ ≈˘⟨ assoc²γβ ⟩
        _ ≈˘⟨ homomorphism F ⟩∘⟨ C4 ⟩
        _ ≈˘⟨ refl⟩∘⟨ pullˡ (Equiv.sym C8) ⟩
        _ ≈˘⟨ pushˡ (homomorphism F) ⟩
        _ ≈˘⟨ F-resp-≈ F (Equiv.sym C1) ⟩∘⟨refl ⟩
        _ ≈˘⟨ pullˡ (Equiv.sym (homomorphism F)) ⟩
        _ ≈˘⟨ push-center (Equiv.sym (homomorphism F²)) ⟩
        _ ≈˘⟨ refl⟩∘⟨ Equiv.sym C2 ⟩
        _ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ F-resp-≈ F² (pullˡ (Equiv.sym (homomorphism F))) ⟩∘⟨refl ⟩
        _ ≈˘⟨ Equiv.sym (homomorphism F) ⟩∘⟨refl ⟩
        _ ≈˘⟨ assoc²βγ ⟩
        _ ∎
        }
    ; identityˡ = λ { {X} →
      assoc ∙
      (refl⟩∘⟨ assoc) ∙
      (skip-2 (Equiv.sym C2)) ∙
      (refl⟩∘⟨ sym-assoc) ∙
      (elim-center (Equiv.sym (homomorphism F) ∙ [ F ]-elim C6)) ∙
      C6
      }
    ; identityʳ = λ { {X} → assoc²βε ∙ Equiv.sym C3}
    } where open Functor

  ζ : monadMap 𝐏Monad F²Monad
  ζ = record
    { α = ntHelper (record
      { η = δ.α
      ; commute = λ { {X} {Y} f → Equiv.sym C2 }
      })
    ; resp-id = Equiv.refl
    ; resp-mu = λ { {X} → Equiv.sym C4 ∙ (C8 ⟩∘⟨refl) ∙ assoc}
    }
