Tom de Jong
Reboot: 22 January 2021
Earlier version: 18 September 2020

We construct the type of integers with the aim of using them in
constructing the circle as the type of ℤ-torsors, as described in
"Construction of the circle in UniMath" by Marc Bezem, Ulrik
Buchholtz, Dan Grayson and Michael Shulman (doi:10.1016/j.jpaa.2021.106687).

See Integers-Properties and Integers-SymmetricInduction for (more) properties of
the type of integers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module SyntheticHomotopyTheory.Circle.Integers where

ℤ : 𝓤₀ ̇
ℤ = 𝟙 + ℕ + ℕ

pattern 𝟎     = inl ⋆
pattern pos i = inr (inl i)
pattern neg i = inr (inr i)

ℕ-to-ℤ₊ : ℕ → ℤ
ℕ-to-ℤ₊ 0        = 𝟎
ℕ-to-ℤ₊ (succ n) = pos n

ℕ-to-ℤ₋ : ℕ → ℤ
ℕ-to-ℤ₋ 0        = 𝟎
ℕ-to-ℤ₋ (succ n) = neg n

ℤ-induction : {𝓤 : Universe} (P : ℤ → 𝓤 ̇ )
            → P 𝟎
            → ((n : ℕ) → P (ℕ-to-ℤ₊ n) → P (ℕ-to-ℤ₊ (succ n)))
            → ((n : ℕ) → P (ℕ-to-ℤ₋ n) → P (ℕ-to-ℤ₋ (succ n)))
            → (z : ℤ) → P z
ℤ-induction {𝓤} P p₀ p₊ p₋ 𝟎       = p₀
ℤ-induction {𝓤} P p₀ p₊ p₋ (pos i) = h (succ i)
 where
  P₊ : ℕ → 𝓤 ̇
  P₊ = P ∘ ℕ-to-ℤ₊
  h : (n : ℕ) → P₊ n
  h = ℕ-induction p₀ p₊
ℤ-induction {𝓤} P p₀ p₊ p₋ (neg i) = h (succ i)
 where
  P₋ : ℕ → 𝓤 ̇
  P₋ = P ∘ ℕ-to-ℤ₋
  h : (n : ℕ) → P₋ n
  h = ℕ-induction p₀ p₋

\end{code}
