Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Spaces.Preliminaries.FunExt (fe : DN-funext 𝓤₀ 𝓤₀) where

fe² : {X : 𝓤₀ ̇ }
      {Y : X → 𝓤₀ ̇ }
      {Z : (x : X) → (y : Y x) → 𝓤₀ ̇ } →
      {f g : (x : X) → (y : Y x) → Z x y}
    → (∀ x y → f x y ＝ g x y) → f ＝ g
fe² ex = fe (λ x → fe (ex x))

fe³ : {X : 𝓤₀ ̇ }
      {Y : X → 𝓤₀ ̇ }
      {Z : (x : X) → Y x → 𝓤₀ ̇ }
      {W : (x : X) → (y : Y x) → Z x y → 𝓤₀ ̇ }
      {f g : (x : X) → (y : Y x) → (z : Z x y) → W x y z}
    → (∀ x y z → f x y z ＝ g x y z) → f ＝ g
fe³ ex = fe (λ x → fe² (ex x))

fe⁴ : {X : 𝓤₀ ̇ }
      {Y : X → 𝓤₀ ̇ }
      {Z : (x : X) → Y x → 𝓤₀ ̇ }
      {W : (x : X) → (y : Y x) → Z x y → 𝓤₀ ̇ }
      {U : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → 𝓤₀ ̇ }
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w}
    → (∀ x y z w → f x y z w ＝ g x y z w) → f ＝ g
fe⁴ ex = fe (λ x → fe³ (ex x))

fe⁵ : {X : 𝓤₀ ̇ }
      {Y : X → 𝓤₀ ̇ }
      {Z : (x : X) → Y x → 𝓤₀ ̇ }
      {W : (x : X) → (y : Y x) → Z x y → 𝓤₀ ̇ }
      {U : (x : X) → (y : Y x) → (z : Z x y) → W x y z → 𝓤₀ ̇ }
      {V : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w → 𝓤₀ ̇ }
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → (u : U x y z w)
           → V x y z w u}
    → (∀ x y z w u → f x y z w u ＝ g x y z w u) → f ＝ g
fe⁵ ex = fe (λ x → fe⁴ (ex x))

\end{code}
