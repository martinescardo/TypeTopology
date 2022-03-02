\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc
open import OrderNotation

open import Rationals
open import RationalsOrder


module ContinuousExtensionTheorem
 (fe : Fun-Ext)
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
  where

open PropositionalTruncation pt

open import DedekindReals pe pt fe
open import MetricSpaceAltDef pt fe pe
open import MetricSpaceDedekindReals pt fe pe
open import MetricSpaceRationals fe pt pe
open import RationalsLimits fe pt pe

\end{code}

The goal is to solve the following proof from Simmons Introduction to Topology and Modern Analysis:

Let X be a metric space, let Y be a complete metric space, and A be a dense subspace of X.
If f is a uniformly continuous mapping of A into Y, then f can be extended uniquely to a uniformly continuous mapping g of X into Y.

In order to prove this, it is first necessary to introduce the definitions in the proof.

First, we would like to know that every point in ℝ is a limit point for some cauchy sequence.

\begin{code}

open import OrderNotation
open import NaturalsOrder
{-
ℚ-converges-to-point-in-ℝ : (x : ℝ) → Σ S ꞉ (ℕ → ℚ) , (c : ?) → (embedding-ℚ-to-ℝ {!!} ≡ x)
ℚ-converges-to-point-in-ℝ S = {!!}
-}
continuous : {M₁ : 𝓤 ̇} {M₂ : 𝓥 ̇} → (m₁ : metric-space M₁) → (m₂ : metric-space M₂) → (f : M₁ → M₂) → 𝓤 ̇ 
continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , conditions) (B₂ , conditions') f = (c : M₁) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : M₁) → B₁ c x δ l₂ → B₂ (f c) (f x) ε l)

every-point-in-ℝ-limit-point : (x : ℝ) → {!Σ !}
every-point-in-ℝ-limit-point = {!!}

{-
continuous-extension-theorem : (f : ℚ → ℝ)
                             → continuous ℚ-metric-space ℝ-metric-space f
                             → ∃! g ꞉ (ℝ → ℝ) , (continuous ℝ-metric-space ℝ-metric-space g)
continuous-extension-theorem f f-continuous = (g , g-continuous) , g-unique
 where
  g : ℝ → ℝ
  g x = {!!}
  g-continuous : continuous ℝ-metric-space ℝ-metric-space g
  g-continuous = {!!}
  g-unique : is-central (Σ (continuous ℝ-metric-space ℝ-metric-space)) (g , g-continuous)
  g-unique (g' , g'-continuous) = {!!}
-}
open import RationalsAddition

ℚ-addition-to-ℝ : ℚ → ℚ → ℝ
ℚ-addition-to-ℝ p q = embedding-ℚ-to-ℝ (p + q)

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

ℚ-succ-to-ℝ : ℚ → ℝ
ℚ-succ-to-ℝ q = embedding-ℚ-to-ℝ (ℚ-succ q)
{-
ℚ-succ-to-ℝ-continuous : continuous ℚ-metric-space ℝ-metric-space ℚ-succ-to-ℝ
ℚ-succ-to-ℝ-continuous c ε = {!!}

rationals-extension : (ℚ → ℚ) → ℝ → ℝ
rationals-extension f = {!!}

ℝ-succ : ℝ → ℝ
ℝ-succ = rationals-extension ℚ-succ
 where
  this : {!!}
  this = {!!}
-}

\end{code}


{-
continuous-extension-theorem : {M₁ : 𝓤 ̇} → {M₂ : 𝓥 ̇}
                             → (m₁ : metric-space M₁) → (m₂ : complete-metric-space M₂) → {!!}
continuous-extension-theorem = {!!}
-}
