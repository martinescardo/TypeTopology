Properties of the disjoint sum _+_ of types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Plus-Properties where

open import MLTT.Plus
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

lni : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X → X + Y → X
lni x₀ (inl x) = x
lni x₀ (inr y) = x₀

inl-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} → inl {𝓤} {𝓥} {X} {Y} x ＝ inl x' → x ＝ x'
inl-lc {𝓤} {𝓥} {X} {Y} {x} = ap (lni x)

rni : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → X + Y → Y
rni y₀ (inl x) = y₀
rni y₀ (inr y) = y

inr-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {y y' : Y} → inr {𝓤} {𝓥} {X} {Y} y ＝ inr y' → y ＝ y'
inr-lc {𝓤} {𝓥} {X} {Y} {y} = ap (rni y)

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

+functor₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {X' : 𝓤' ̇ } {Y' : 𝓥' ̇ } {Z' : 𝓦' ̇ }
          → (X → X') → (Y → Y') → (Z → Z') → X + Y + Z → X' + Y' + Z'
+functor₂ f g h = +functor f (+functor g h)

\end{code}

Added 29 Sep 2026 by Tom de Jong.

Previously, inl-lc-is-section and inr-lc-is-section were in UF.Sets and relied
on injectivity of inl (resp. inr) which Agda silently uses when we pattern match
on a term of type inl x ＝ inl x'.

\begin{code}

module encode-decode-inl
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
        {x₀ : X}
       where

 private
  C : X + Y → 𝓤 ̇
  C (inl x) = x₀ ＝ x
  C (inr x) = 𝟘

  encode : (z : X + Y) → (inl x₀ ＝ z) → C z
  encode (inl _) = inl-lc
  encode (inr _) = λ p → 𝟘-elim (+disjoint p)

  decode : (z : X + Y) → C z → (inl x₀ ＝ z)
  decode (inl _) c = ap inl c
  decode (inr _) c = 𝟘-elim c

 encode-decode : (z : X + Y) (p : inl x₀ ＝ z)
               → decode z (encode z p) ＝ p
 encode-decode z refl = refl

 decode-encode : (z : X + Y) (c : C z) → encode z (decode z c) ＝ c
 decode-encode (inl _) refl = refl
 decode-encode (inr _) c = 𝟘-elim c

inl-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    {x x' : X}
                    (p : inl {𝓤} {𝓥} {X} {Y} x ＝ inl x')
                  → ap inl (inl-lc p) ＝ p
inl-lc-is-section = encode-decode-inl.encode-decode (inl _)

inl-lc-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       {x x' : X}
                       (p : x ＝ x')
                     → inl-lc {𝓤 } {𝓥} {X} {Y} (ap inl p) ＝ p
inl-lc-is-retraction = encode-decode-inl.decode-encode (inl _)

module encode-decode-inr
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
        {y₀ : Y}
       where

 private
  C : X + Y → 𝓥 ̇
  C (inl _) = 𝟘
  C (inr y) = y₀ ＝ y

  encode : (z : X + Y) → (inr y₀ ＝ z) → C z
  encode (inl _) = λ p → 𝟘-elim (+disjoint (p ⁻¹))
  encode (inr _) = inr-lc

  decode : (z : X + Y) → C z → (inr y₀ ＝ z)
  decode (inl _) c = 𝟘-elim c
  decode (inr _) c = ap inr c

 encode-decode : (z : X + Y) (p : inr y₀ ＝ z)
               → decode z (encode z p) ＝ p
 encode-decode z refl = refl

 decode-encode : (z : X + Y) (c : C z) → encode z (decode z c) ＝ c
 decode-encode (inl _) c = 𝟘-elim c
 decode-encode (inr _) refl = refl

inr-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    {y y' : Y}
                    (p : inr {𝓤} {𝓥} {X} {Y} y ＝ inr y')
                  → ap inr (inr-lc p) ＝ p
inr-lc-is-section = encode-decode-inr.encode-decode (inr _)

inr-lc-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       {y y' : Y}
                       (p : y ＝ y')
                     → inr-lc {𝓤} {𝓥} {X} {Y} (ap inr p) ＝ p
inr-lc-is-retraction = encode-decode-inr.decode-encode (inr _)

\end{code}