Properties of the disjoint sum _+_ of types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Plus-Properties where

open import Plus
open import Universes
open import Negation
open import Id
open import Empty

+-commutative : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A + B → B + A
+-commutative = cases inr inl

+disjoint : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → ¬(inl x ≡ inr y)
+disjoint ()

+disjoint' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → ¬(inr y ≡ inl x)
+disjoint' ()

inl-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} → inl {𝓤} {𝓥} {X} {Y} x ≡ inl x' → x ≡ x'
inl-lc refl = refl

inr-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {y y' : Y} → inr {𝓤} {𝓥} {X} {Y} y ≡ inr y' → y ≡ y'
inr-lc refl = refl

equality-cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (z : X + Y)
               → ((x : X) → z ≡ inl x → A) → ((y : Y) → z ≡ inr y → A) → A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

Cases-equality-l : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → A) (g : Y → A)
                 → (z : X + Y) (x : X) → z ≡ inl x → Cases z f g ≡ f x
Cases-equality-l f g .(inl x) x refl = refl

Cases-equality-r : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → A) (g : Y → A)
                 → (z : X + Y) (y : Y) → z ≡ inr y → Cases z f g ≡ g y
Cases-equality-r f g .(inr y) y refl = refl

Left-fails-then-right-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ P → Q
Left-fails-then-right-holds (inl p) u = 𝟘-elim (u p)
Left-fails-then-right-holds (inr q) u = q

Right-fails-then-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
Right-fails-then-left-holds (inl p) u = p
Right-fails-then-left-holds (inr q) u = 𝟘-elim (u q)

\end{code}
