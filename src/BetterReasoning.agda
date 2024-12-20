{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Function using (flip)
open import Categories.Functor.Properties

module BetterReasoning {o ℓ e} (C : Category o ℓ e) where

open Category C public

open Equiv public

open module Chain = HomReasoning

assoc-2 = assoc

sym-assoc-2 = sym-assoc

infixr 7 _∙_
_∙_ = Equiv.trans

assoc-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ h ∘ i
assoc-3 = assoc ∙ ∘-resp-≈ʳ assoc

assoc-4 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {l : F ⇒ E} → (f ∘ g ∘ h ∘ i) ∘ l ≈ f ∘ g ∘ h ∘ i ∘ l
assoc-4 = assoc ∙ ∘-resp-≈ʳ assoc-3

sym-assoc-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} → f ∘ g ∘ h ∘ i ≈ (f ∘ g ∘ h) ∘ i
sym-assoc-3 = Equiv.sym assoc-3

sym-assoc-4 : ∀ {A B C D E F} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {i : E ⇒ D} {l : F ⇒ E} → f ∘ g ∘ h ∘ i ∘ l ≈ (f ∘ g ∘ h ∘ i) ∘ l
sym-assoc-4 = Equiv.sym assoc-4

skip-1 : ∀ {A B C} {f : B ⇒ A} {z z′ : C ⇒ B} → z ≈ z′ → f ∘ z ≈ f ∘ z′
skip-1 = ∘-resp-≈ʳ

skip = skip-1

skip-2 : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ B} {z z′ : D ⇒ C} → z ≈ z′ → f ∘ g ∘ z ≈ f ∘ g ∘ z′
skip-2 eq = skip-1 (skip-1 eq)

skip-3 : ∀ {A B C D E} {f : B ⇒ A} {g : C ⇒ B} {h : D ⇒ C} {z z′ : E ⇒ D} → z ≈ z′ → f ∘ g ∘ h ∘ z ≈ f ∘ g ∘ h ∘ z′
skip-3 eq = skip-1 (skip-2 eq)

rw : ∀ {A B C} {f f′ : B ⇒ A} {g : C ⇒ B} → f ≈ f′ → f ∘ g ≈ f′ ∘ g
rw = ∘-resp-≈ˡ

rw-2-1 : ∀ {A B C D} {f : B ⇒ A} {g : C ⇒ B} {fg : C ⇒ A} {z : D ⇒ C} → f ∘ g ≈ fg → f ∘ g ∘ z ≈ fg ∘ z
rw-2-1 eq = sym-assoc ∙ rw eq

rw-2 : ∀ {A B B′ C D} {f : B ⇒ A} {g : C ⇒ B} {f′ : B′ ⇒ A} {g′ : C ⇒ B′} {z : D ⇒ C} → f ∘ g ≈ f′ ∘ g′ → f ∘ g ∘ z ≈ f′ ∘ g′ ∘ z
rw-2 eq = sym-assoc-2 ∙ rw eq ∙ assoc-2

-- A B C     A B′ B C
rw-2-3 : ∀ {A B B′ C Z} {f : B ⇒ C} {g : A ⇒ B}   {h : B′ ⇒ C} {i : B ⇒ B′} {j : A ⇒ B}   {z : Z ⇒ A}
        → f ∘ g ≈ h ∘ i ∘ j
        → f ∘ g ∘ z ≈ h ∘ i ∘ j ∘ z
rw-2-3 eq = sym-assoc-2 ∙ rw eq ∙ assoc-3

id-0 = identityˡ

sym-id-0 : ∀ {A B} {f : A ⇒ B} → f ≈ id ∘ f
sym-id-0 = Equiv.sym identityˡ

id-1 = identityʳ

sym-id-1 : ∀ {A B} {f : A ⇒ B} → f ≈ f ∘ id
sym-id-1 = Equiv.sym id-1

id-2 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ∘ id ≈ f ∘ g
id-2 = skip identityʳ

sym-id-2 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ≈ f ∘ g ∘ id
sym-id-2 = Equiv.sym id-2

idm-1 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ id ∘ g ≈ f ∘ g
idm-1 = skip identityˡ

sym-idm-1 : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ g ≈ f ∘ id ∘ g
sym-idm-1 = Equiv.sym idm-1

id-2-1 : ∀ {A B} {f : A ⇒ B} → f ∘ id ∘ id ≈ f
id-2-1 = id-2 ∙ id-1

id-swap : ∀ {A B} {f : B ⇒ A} → f ∘ id ≈ id ∘ f
id-swap = identityʳ ∙ Equiv.sym identityˡ

id-swap-2 : ∀ {A B} {f : B ⇒ A} → f ∘ id ∘ id ≈ id ∘ id ∘ f
id-swap-2 = rw-2 id-swap ∙ skip id-swap

sym-id-swap : ∀ {A B} {f : B ⇒ A} → id ∘ f ≈ f ∘ id
sym-id-swap = identityˡ ∙ Equiv.sym identityʳ

sym-id-swap-2 : ∀ {A B} {f : B ⇒ A} → id ∘ id ∘ f ≈ f ∘ id ∘ id
sym-id-swap-2 = Equiv.sym id-swap-2

module _ {o ℓ e}
         {Z : Category o ℓ e}
         (F : Functor Z C) where
  private
    module F = Functor F
    module Z = Category Z

  homomorphism₃ : ∀ {A B C D}
            {f : B Z.⇒ A} {g : C Z.⇒ B} {h : D Z.⇒ C}
        → F.₁ (f Z.∘ g Z.∘ h) ≈ F.₁ f ∘ F.₁ g ∘ F.₁ h
  homomorphism₃ = F.homomorphism ∙ skip F.homomorphism

  homomorphism₄ : ∀ {A B C D E}
            {f : B Z.⇒ A} {g : C Z.⇒ B} {h : D Z.⇒ C} {i : E Z.⇒ D}
        → F.₁ (f Z.∘ g Z.∘ h Z.∘ i) ≈ F.₁ f ∘ F.₁ g ∘ F.₁ h ∘ F.₁ i
  homomorphism₄ = homomorphism₃ ∙ skip-2  F.homomorphism

  [_]-2 = [_]-resp-square

  [_]-3 : ∀ {A B C D}
            {f f′ : B Z.⇒ A} {g g′ : C Z.⇒ B} {h h′ : D Z.⇒ C}
        → f Z.∘ g Z.∘ h Z.≈ f′ Z.∘ g′ Z.∘ h′
        → F.₁ f ∘ F.₁ g ∘ F.₁ h
        ≈ F.₁ f′ ∘ F.₁ g′ ∘ F.₁ h′
  [_]-3 eq = Equiv.sym homomorphism₃ ∙ F.F-resp-≈ eq ∙ homomorphism₃

  [_]-3-1 : ∀ {A B C D}
            {f : B Z.⇒ A} {g : C Z.⇒ B} {h : D Z.⇒ C}
            {fgh : D Z.⇒ A}
        → f Z.∘ g Z.∘ h Z.≈ fgh
        → F.₁ f ∘ F.₁ g ∘ F.₁ h
        ≈ F.₁ fgh
  [_]-3-1 eq = Equiv.sym homomorphism₃ ∙ F.F-resp-≈ eq

  [_]-rw-2 : ∀ {A B C D}
            {f f′ : B Z.⇒ A} {g g′ : C Z.⇒ B} {h : F.₀ D ⇒ F.₀ C}
        → f Z.∘ g Z.≈ f′ Z.∘ g′
        → F.₁ f ∘ F.₁ g ∘ h
        ≈ F.₁ f′ ∘ F.₁ g′ ∘ h
  [_]-rw-2 eq = rw-2 ([ F ]-resp-square eq)
