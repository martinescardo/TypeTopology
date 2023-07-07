Martin Escardo & Tom de Jong, June 2023.

Iterative multisets.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module Iterative.Multisets
        {𝓤 : Universe}
       where

open import UF.Base
open import UF.Equiv

\end{code}

The type of iterative multisets:

\begin{code}

data 𝕄 : 𝓤 ⁺ ̇ where
 ssup : (X : 𝓤 ̇ ) (φ : X → 𝕄) → 𝕄

open import Ordinals.Notions

\end{code}

In the case of ordinals, ssup stands for "strong supremum", "strict
supremum" or "supremum of successors.

\begin{code}

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root (ssup X φ) = X

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest (ssup X φ) = φ

\end{code}

The induction principle for 𝕄:

\begin{code}

𝕄-induction : (P : 𝕄 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕄)
                  → ((x : X) → P (ϕ x))
                  → P (ssup X ϕ))
            → (M : 𝕄) → P M
𝕄-induction P f = h
 where
  h : (M : 𝕄) → P M
  h (ssup X φ) = f X φ (λ x → h (φ x))

\end{code}

A criterion for equality in 𝕄:

\begin{code}

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
        → (ssup X φ) ＝ (ssup Y γ)
to-𝕄-＝ {X} (refl , f) = ap (ssup X) f

from-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
          → (ssup X φ) ＝ (ssup Y γ)
          → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
from-𝕄-＝ {X} refl = refl , refl

\end{code}

TODO. 𝕄 is locally small.
