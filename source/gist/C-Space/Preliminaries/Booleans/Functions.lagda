Chuangjie Xu 2015 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.C-Space.Preliminaries.Booleans.Functions where

open import MLTT.Spartan

if : {A : Set} → 𝟚 → A → A → A
if b a₀ a₁ = 𝟚-cases a₀ a₁ b

eq : 𝟚 → 𝟚 → 𝟚
eq b₀ b₁ = if b₀ (if b₁ ₁ ₀) b₁

Lemma[eq] : (b₀ b₁ : 𝟚) → eq b₀ b₁ ＝ ₁ → b₀ ＝ b₁
Lemma[eq] ₀ ₀ refl = refl
Lemma[eq] ₀ ₁ ()
Lemma[eq] ₁ ₀ ()
Lemma[eq] ₁ ₁ refl = refl

min : 𝟚 → 𝟚 → 𝟚
min b₀ b₁ = if b₀ ₀ b₁

Lemma[min] : (b₀ b₁ : 𝟚) → min b₀ b₁ ＝ ₁ → (b₀ ＝ ₁) × (b₁ ＝ ₁)
Lemma[min] ₀ ₀ ()
Lemma[min] ₀ ₁ ()
Lemma[min] ₁ ₀ ()
Lemma[min] ₁ ₁ refl = refl , refl

\end{code}