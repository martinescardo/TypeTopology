Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Spaces.Preliminaries.FunExt (fe : DN-funext 𝓤₀ 𝓤₀) where

fe² : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → (y : Y x) → Set} →
      {f g : (x : X) → (y : Y x) → Z x y}
    → (∀ x y → f x y ＝ g x y) → f ＝ g
fe² ex = fe (λ x → fe (ex x))

fe³ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → W x y z}
    → (∀ x y z → f x y z ＝ g x y z) → f ＝ g
fe³ ex = fe (λ x → fe² (ex x))

fe⁴ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {U : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w}
    → (∀ x y z w → f x y z w ＝ g x y z w) → f ＝ g
fe⁴ ex = fe (λ x → fe³ (ex x))

fe⁵ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {U : (x : X) → (y : Y x) → (z : Z x y) → W x y z → Set}
      {V : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → (u : U x y z w)
           → V x y z w u}
    → (∀ x y z w u → f x y z w u ＝ g x y z w u) → f ＝ g
fe⁵ ex = fe (λ x → fe⁴ (ex x))

\end{code}
