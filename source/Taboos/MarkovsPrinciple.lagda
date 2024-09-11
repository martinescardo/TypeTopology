Martin Escardo 11th September 2024.

Markov's principle and the well-known fact that it and WLPO together
imply LPO.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

module Taboos.MarkovsPrinciple where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import NotionsOfDecidability.Complemented
open import Taboos.LPO
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import UF.DiscreteAndSeparated
open import UF.FunExt

MP : (𝓤 : Universe) → 𝓤 ⁺ ̇
MP 𝓤 = (A : ℕ → 𝓤 ̇ )
     → is-complemented A
     → ¬¬ (Σ n ꞉ ℕ , A n)
     → Σ n ꞉ ℕ , A n

MP-and-WLPO-give-LPO
 : funext 𝓤₀ 𝓤₀
 → MP 𝓤₀
 → WLPO → LPO
MP-and-WLPO-give-LPO fe mp wlpo = III
 where
  I : WLPO-traditional
  I = WLPO-gives-WLPO-traditional fe wlpo

  II : WLPO-traditional → is-compact ℕ
  II wlpot p = II₄
   where
    II₀ : ¬ (Σ n ꞉ ℕ , p n ＝ ₀) → (n : ℕ) → p n ＝ ₁
    II₀ ν n = Lemma[b≠₀→b＝₁] (λ (e : p n ＝ ₀) → ν (n , e))

    II₁ : ¬ ((n : ℕ) → p n ＝ ₁) → ¬¬ (Σ n ꞉ ℕ , p n ＝ ₀)
    II₁ = contrapositive II₀

    II₂ : ¬ ((n : ℕ) → p n ＝ ₁) → Σ n ꞉ ℕ , p n ＝ ₀
    II₂ ν = mp (λ n → p n ＝ ₀)
               (λ n → 𝟚-is-discrete (p n) ₀)
               (II₁ ν)

    II₃ : is-decidable ((n : ℕ) → p n ＝ ₁)
        → (Σ n ꞉ ℕ , p n ＝ ₀) + ((n : ℕ) → p n ＝ ₁)
    II₃ (inl a) = inr a
    II₃ (inr ν) = inl (II₂ ν)

    II₄ : (Σ n ꞉ ℕ , p n ＝ ₀) + ((n : ℕ) → p n ＝ ₁)
    II₄ = II₃ (wlpot p)

  III : LPO
  III = compact-ℕ-gives-LPO fe (II I)

\end{code}

TODO. It doesn't matter if we formulated MP with Σ or ∃, or for
𝟚-valued functions, so that we get four logically equivalent
formulations.
