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
 sup : (X : 𝓤 ̇ ) (φ : X → 𝕄) → 𝕄

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root (sup X φ) = X

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest (sup X φ) = φ

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
        → (sup X φ) ＝ (sup Y γ)
to-𝕄-＝ {X} (refl , f) = ap (sup X) f

\end{code}
