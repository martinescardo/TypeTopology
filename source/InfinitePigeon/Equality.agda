-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Equality where

open import InfinitePigeon.Logic

data _≡_ {X : Set} : X → X → Ω where
  reflexivity : {x : X} → x ≡ x

infix  29 _≡_

two-things-equal-to-a-third-are-equal : {X : Set} →
             ∀{x y z : X} → x ≡ y → x ≡ z → y ≡ z

two-things-equal-to-a-third-are-equal reflexivity reflexivity = reflexivity


transitivity : {X : Set} → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
transitivity reflexivity reflexivity = reflexivity


symmetry : {X : Set} → {x y : X} → x ≡ y → y ≡ x
symmetry reflexivity = reflexivity


compositionality : {X Y : Set} → ∀(f : X → Y) → {x₀ x₁ : X} →

  x₀ ≡ x₁ →  f x₀ ≡ f x₁

compositionality f reflexivity = reflexivity


predicate-compositionality : {X : Set} (A : X → Ω) {x y : X} →

  x ≡ y → A x → A y

predicate-compositionality A reflexivity a = a


binary-predicate-compositionality :

   {X Y : Set} {A : X → Y → Ω} {x x' : X} {y y' : Y} →

   x ≡ x' → y ≡ y' → A x y → A x' y'

binary-predicate-compositionality reflexivity reflexivity a = a


set-compositionality : {I : Set} (X : I → Set) → {i j : I} → i ≡ j → X i → X j
set-compositionality X reflexivity x = x
