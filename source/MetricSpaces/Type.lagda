Andrew Sneap, 11 November 2021, Updated 3 May 2023

In this file I define the types of complete metric spaces, along with
Cauchy and convergent sequences.

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order
open import Notation.Order
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Rationals.Type
open import Rationals.Positive

module MetricSpaces.Type
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

m1a : (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m1a X B = (x y : X) → ((ε : ℚ₊) → B x y ε) → x ＝ y

m1b : (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m1b X B = (x : X) → (ε : ℚ₊) → B x x ε

m2 : (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m2 X B = (x y : X) → (ε : ℚ₊) → B x y ε → B y x ε

m3 : (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m3 X B = (x y : X) → (ε₁ ε₂ : ℚ₊)
                   → ε₁ < ε₂
                   → B x y ε₁
                   → B x y ε₂

m4 : (X : 𝓤 ̇) → (B : X → X → ℚ₊ → 𝓤₀ ̇) → 𝓤 ̇
m4 X B = (x y z : X) → (ε₁ ε₂ : ℚ₊)
                     → B x y ε₁
                     → B y z ε₂
                     → B x z (ε₁ + ε₂)

metric-space : (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X =
 Σ B ꞉ (X → X → ℚ₊ → 𝓤₀ ̇) , m1a X B × m1b X B × m2 X B × m3 X B × m4 X B

\end{code}

A space is a complete metric space if every cauchy sequence in a metric space is
also a convergent sequence. Convergent and Cauchy Sequences are also defined
below. In a metric space, all convergent sequences are cauchy sequences.

\begin{code}

bounded-sequence : (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
bounded-sequence X (B , _) S = ∃ K ꞉ ℚ₊ , ((x y : ℕ) → B (S x) (S y) K)

bounded-sequence-is-prop : (X : 𝓤 ̇)
                         → (m : metric-space X)
                         → (S : ℕ → X)
                         → is-prop (bounded-sequence X m S)
bounded-sequence-is-prop X m S = ∃-is-prop

convergent-sequence : (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
convergent-sequence X (B , _) S
 = ∃ x ꞉ X , ((ε : ℚ₊) → Σ N ꞉ ℕ , ((n : ℕ) → N < n → B x (S n) ε))

cauchy-sequence : (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
cauchy-sequence X (B , _) S
 = (ε : ℚ₊) → Σ N ꞉ ℕ , ((m n : ℕ) → N ≤ m → N ≤ n → B (S m) (S n) ε)

convergent→cauchy : (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → 𝓤 ̇
convergent→cauchy X m S = convergent-sequence X m S → cauchy-sequence X m S

cauchy→convergent : (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
cauchy→convergent X m S = cauchy-sequence X m S → convergent-sequence X m S

complete-metric-space : (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
complete-metric-space X
 = Σ m ꞉ metric-space X , ((S : ℕ → X) → cauchy→convergent X m S)

\end{code}
