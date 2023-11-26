Properties of the disjoint sum _+_ of types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Plus-Properties where

open import MLTT.Plus
open import MLTT.Universes
open import MLTT.Negation
open import MLTT.Id
open import MLTT.Empty
open import MLTT.Unit
open import MLTT.Unit-Properties

+-commutative : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A + B → B + A
+-commutative = cases inr inl

+disjoint : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → ¬ (inl x ＝ inr y)
+disjoint {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘

  q : 𝟙 ＝ 𝟘
  q = ap f p

+disjoint' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → ¬ (inr y ＝ inl x)
+disjoint' p = +disjoint (p ⁻¹)

inl-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} → inl {𝓤} {𝓥} {X} {Y} x ＝ inl x' → x ＝ x'
inl-lc refl = refl

inr-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {y y' : Y} → inr {𝓤} {𝓥} {X} {Y} y ＝ inr y' → y ＝ y'
inr-lc refl = refl

equality-cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (z : X + Y)
               → ((x : X) → z ＝ inl x → A) → ((y : Y) → z ＝ inr y → A) → A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

Cases-equality-l : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → A) (g : Y → A)
                 → (z : X + Y) (x : X) → z ＝ inl x → Cases z f g ＝ f x
Cases-equality-l f g .(inl x) x refl = refl

Cases-equality-r : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → A) (g : Y → A)
                 → (z : X + Y) (y : Y) → z ＝ inr y → Cases z f g ＝ g y
Cases-equality-r f g .(inr y) y refl = refl

Left-fails-gives-right-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ P → Q
Left-fails-gives-right-holds (inl p) u = 𝟘-elim (u p)
Left-fails-gives-right-holds (inr q) u = q

Right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
Right-fails-gives-left-holds (inl p) u = p
Right-fails-gives-left-holds (inr q) u = 𝟘-elim (u q)

open import MLTT.Unit
open import MLTT.Sigma
open import Notation.General

inl-preservation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X + 𝟙 {𝓦}  → Y + 𝟙 {𝓣})
                 → f (inr ⋆) ＝ inr ⋆
                 → left-cancellable f
                 → (x : X) → Σ y ꞉ Y , f (inl x) ＝ inl y
inl-preservation {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} f p l x = γ x (f (inl x)) refl
 where
  γ : (x : X) (z : Y + 𝟙) → f (inl x) ＝ z → Σ y ꞉ Y , z ＝ inl y
  γ x (inl y) q = y , refl
  γ x (inr ⋆) q = 𝟘-elim (+disjoint (l r))
   where
    r : f (inl x) ＝ f (inr ⋆)
    r = q ∙ p ⁻¹

+functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
         → (X → A) → (Y → B) → X + Y → A + B
+functor f g (inl x) = inl (f x)
+functor f g (inr y) = inr (g y)

\end{code}
