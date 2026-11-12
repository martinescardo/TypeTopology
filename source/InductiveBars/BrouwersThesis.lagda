Chuangjie Xu, November 2026

We prove Brouwer’s thesis for monotone bars with bar-continuous witnesses.

This development is motivated by Jonathan Sterling's "Higher order functions
and Brouwer's thesis" (2021).

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan hiding (𝓤)
open import UF.FunExt using (Fun-Ext)

module InductiveBars.BrouwersThesis
 (fe : Fun-Ext)
 {𝓤 : Universe}
 (A : 𝓤 ̇)
 where

open import MLTT.List
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import UF.Powerset-MultiUniverse
open import Naturals.Order

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe A ℕ ℕ-is-set

\end{code}

At an arbitrary root s, we transform a bar of determining prefixes into
a bar in V.

\begin{code}

brouwers-thesis-at-prefix
 : (V : 𝓟 {𝓥} (List A)) → is-monotone V
 → (f : (ℕ → A) → ℕ)
 → ((α : ℕ → A) → prefix (f α) α ∈ V)
 → (s : List A) → (determining-prefixes f) bars s → V bars s
brouwers-thesis-at-prefix V m f wit s (hit det) = step φ
 where
  claim₀ : (a : A) → (t : List A) → length t ＝ f (pad-with a s) → (s ++ t) ∈ V
  claim₀ a t e = transport (_∈ V) eq p
   where
    r : List A
    r = s ++ t
    α : ℕ → A
    α = pad-with a r
    e' : f α ＝ f (pad-with a s)
    e' = det α (pad-with a s) (extends-++ α s t (pad-extends r)) (pad-extends s)
    q : f α ≤ℕ length r
    q = transport (_≤ℕ length r) (e ∙ e' ⁻¹) (length-++-right s t)
    decomposition : Σ u ꞉ List A , prefix (f α) α ++ u ＝ r
    decomposition = extends-prefix-decomposition α r (f α) (pad-extends r) q
    u : List A
    u = pr₁ decomposition
    eq : prefix (f α) α ++ u ＝ r
    eq = pr₂ decomposition
    p : (prefix (f α) α ++ u) ∈ V
    p = m (prefix (f α) α) u (wit α)
  claim₁ : A → V bars s
  claim₁ a = bars-from-level V s (f (pad-with a s)) (claim₀ a)
  φ : (a : A) → V bars (s ++ [ a ])
  φ a = monotone-bars-extend V m s a (claim₁ a)
brouwers-thesis-at-prefix V m f wit s (step φ)
 = step (λ a → brouwers-thesis-at-prefix V m f wit (s ++ [ a ]) (φ a))

\end{code}

Then we obtain Brouwer’s thesis for monotone bars with bar-continuous witnesses.

\begin{code}

brouwers-thesis-for-bar-continuous-witnesses″
 : (V : 𝓟 {𝓥} (List A)) → is-monotone V
 → (f : (ℕ → A) → ℕ) → is-bar-continuous″ f
 → ((α : ℕ → A) → prefix (f α) α ∈ V)
 → (s : List A) → V bars s
brouwers-thesis-for-bar-continuous-witnesses″ V m f bc wit s
 = brouwers-thesis-at-prefix V m f wit s (bc s)

brouwers-thesis-for-bar-continuous-witnesses
 : (V : 𝓟 {𝓥} (List A)) → is-monotone V
 → (f : (ℕ → A) → ℕ) → is-bar-continuous f
 → ((α : ℕ → A) → prefix (f α) α ∈ V)
 → is-inductive-bar V
brouwers-thesis-for-bar-continuous-witnesses V m f bc wit
 = bars-root-implies-inductive-bar V
    (brouwers-thesis-for-bar-continuous-witnesses″ V m f
      (bar-continuity-implies-bar-continuity″ f bc)
      wit [])

\end{code}
