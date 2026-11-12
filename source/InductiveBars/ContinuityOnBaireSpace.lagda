Chuangjie Xu, November 2026

We collect results about bar continuity for functions from Baire space
to natural numbers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt using (Fun-Ext)

module InductiveBars.ContinuityOnBaireSpace (fe : Fun-Ext) where

open import MLTT.Spartan
open import MLTT.List
open import Naturals.Order
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import UF.Powerset-MultiUniverse

open import EffectfulForcing.MFPSAndVariations.SystemT
 using (T-definable)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS
 using (eloquence-theorem)

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe ℕ ℕ ℕ-is-set
open import InductiveBars.BrouwersThesis fe ℕ

\end{code}

Bar continuity on Baire space implies uniform continuity on every pointwise
bounded subset of Baire space.

\begin{code}

is-uniformly-continuous-on-bounded-subsets : ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
is-uniformly-continuous-on-bounded-subsets f
 = (δ : ℕ → ℕ)
 → Σ m ꞉ ℕ , ((α β : ℕ → ℕ) → α ≤¹ δ → β ≤¹ δ → α ＝⦅ m ⦆ β → f α ＝ f β)

bar-continuity-implies-uniform-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f → is-uniformly-continuous-on-bounded-subsets f
bar-continuity-implies-uniform-continuity f bc δ = m , correct
 where
  fact : Σ m ꞉ ℕ ,
          ((α : ℕ → ℕ) → α ≤¹ δ
           → Σ s ꞉ List ℕ , (length s ≤ℕ m) × (α extends s) × (s determines f))
  fact = inductive-bar-meets-bounded-sequences-uniformly
          (determining-prefixes f) bc δ
  m : ℕ
  m = pr₁ fact
  correct : (α β : ℕ → ℕ) → α ≤¹ δ → β ≤¹ δ → α ＝⦅ m ⦆ β → f α ＝ f β
  correct α β rα _ em
   using (s , rs , eαs , det) ← pr₂ fact α rα
   = det α β eαs eβs
   where
    es : α ＝⦅ length s ⦆ β
    es = ＝⦅⦆-≤ α β rs em
    eβs : β extends s
    eβs = agreement-preserves-extension α β s eαs es

\end{code}

Every System T-definable function of type (ℕ → ℕ) → ℕ is eloquent and
thus bar continuous.

\begin{code}

T-definable-functions-are-bar-continuous
 : (f : (ℕ → ℕ) → ℕ)
 → T-definable f
 → is-bar-continuous f
T-definable-functions-are-bar-continuous f t
 = eloquence-implies-bar-continuity f (eloquence-theorem f t)

\end{code}

Because T-definable functions are bar continuous, we recover Brouwer's thesis
for monotone bars with T-definable witnesses.

\begin{code}

brouwers-thesis-for-T-definable-witnesses
 : (V : 𝓟 {𝓥} (List ℕ)) → is-monotone V
 → (f : (ℕ → ℕ) → ℕ) → T-definable f
 → ((α : ℕ → ℕ) → prefix (f α) α ∈ V)
 → is-inductive-bar V
brouwers-thesis-for-T-definable-witnesses V m f t
 = brouwers-thesis-for-bar-continuous-witnesses V m f
    (T-definable-functions-are-bar-continuous f t)

\end{code}
