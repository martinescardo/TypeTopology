Chuangjie Xu, November 2026

We prove Brouwer’s thesis for monotone bars with bar-continuous witnesses.

This development is motivated by Jonathan Sterling's "Higher order functions
and Brouwer's thesis" (2021).  Because T-definable functions are bar continuous,
we recover the result for monotone bars with T-definable witnesses, proved in
Theorem 4.1 of the paper.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import UF.FunExt using (Fun-Ext)

module InductiveBars.BrouwersThesis (fe : Fun-Ext) where

open import MLTT.Spartan
open import MLTT.List
open import UF.Powerset
open import Naturals.Order

open import EffectfulForcing.MFPSAndVariations.SystemT
 using (T-definable)

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe

\end{code}

At an arbitrary root s, we transform a bar of determining prefixes into
a bar in V.

\begin{code}

brouwers-thesis-at-prefix
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (f : (ℕ → ℕ) → ℕ)
 → ((α : ℕ → ℕ) → prefix (f α) α ∈ V)
 → (s : List ℕ) → determining-prefixes f bars s → V bars s
brouwers-thesis-at-prefix V m f wit s (hit det)
 = bars-from-level V s (f (pad s)) claim
 where
  claim : (t : List ℕ) → length t ＝ f (pad s) → (s ++ t) ∈ V
  claim t e = transport (_∈ V) eq p
   where
    r : List ℕ
    r = s ++ t
    α : ℕ → ℕ
    α = pad r
    e' : f α ＝ f (pad s)
    e' = det α (pad s) (extends-++ α s t (pad-extends r)) (pad-extends s)
    q : f α ≤ℕ length r
    q = transport (_≤ℕ length r) (e ∙ e' ⁻¹) (length-++-right s t)
    decomposition : Σ u ꞉ List ℕ , prefix (f α) α ++ u ＝ r
    decomposition = extends-prefix-decomposition α r (f α) (pad-extends r) q
    u : List ℕ
    u = pr₁ decomposition
    eq : prefix (f α) α ++ u ＝ r
    eq = pr₂ decomposition
    p : (prefix (f α) α ++ u) ∈ V
    p = m (prefix (f α) α) u (wit α)
brouwers-thesis-at-prefix V m f wit s (step φ)
 = step (λ n → brouwers-thesis-at-prefix V m f wit (s ++ [ n ]) (φ n))

\end{code}

Then we obtain Brouwer’s thesis for monotone bars with bar-continuous witnesses.

\begin{code}

brouwers-thesis-for-bar-continuous-witnesses″
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (f : (ℕ → ℕ) → ℕ) → is-bar-continuous″ f
 → ((α : ℕ → ℕ) → prefix (f α) α ∈ V)
 → (s : List ℕ) → V bars s
brouwers-thesis-for-bar-continuous-witnesses″ V m f bc wit s
 = brouwers-thesis-at-prefix V m f wit s (bc s)

brouwers-thesis-for-bar-continuous-witnesses
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (f : (ℕ → ℕ) → ℕ) → is-bar-continuous f
 → ((α : ℕ → ℕ) → prefix (f α) α ∈ V)
 → is-inductive-bar V
brouwers-thesis-for-bar-continuous-witnesses V m f bc wit
 = bars-root-implies-inductive-bar V
    (brouwers-thesis-for-bar-continuous-witnesses″ V m f
      (bar-continuity-implies-bar-continuity″ f bc)
      wit [])

\end{code}

Because T-definable functions are bar continuous, we recover Brouwer's thesis
for monotone bars with T-definable witnesses.

\begin{code}

brouwers-thesis-for-T-definable-witnesses
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (f : (ℕ → ℕ) → ℕ) → T-definable f
 → ((α : ℕ → ℕ) → prefix (f α) α ∈ V)
 → is-inductive-bar V
brouwers-thesis-for-T-definable-witnesses V m f t
 = brouwers-thesis-for-bar-continuous-witnesses V m f
    (T-definable-functions-are-bar-continuous f t)

\end{code}
