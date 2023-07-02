Martin Escardo & Tom de Jong, June 2023.

Iterative multisets.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module Iterative.Multisets
        (𝓤 : Universe)
       where

open import UF.Base
open import UF.Equiv

\end{code}

The type of iterative multisets:

\begin{code}

data 𝕄 : 𝓤 ⁺ ̇ where
 lim : (X : 𝓤 ̇ ) (φ : X → 𝕄) → 𝕄

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root (lim X φ) = X

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest (lim X φ) = φ

\end{code}

A criterion for equality in 𝕄:

\begin{code}

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
        → (lim X φ) ＝ (lim Y γ)
to-𝕄-＝ {X} (refl , f) = ap (lim X) f

\end{code}

The induction principle for 𝕄:

\begin{code}

𝕄-induction : (P : 𝕄 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕄)
                  → ((x : X) → P (ϕ x))
                  → P (lim X ϕ))
            → (M : 𝕄) → P M
𝕄-induction P f = h
 where
  h : (M : 𝕄) → P M
  h (lim X φ) = f X φ (λ x → h (φ x))

\end{code}

TODO. 𝕄 is locally small.
