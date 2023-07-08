Martin Escardo & Tom de Jong, June 2023.

Iterative multisets.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

\end{code}

The following universe parameter needs to be implicit - don't to make
it explicit. See Agda issue #6719.

\begin{code}


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

𝕄-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → 𝕄) → (X → P) → P)
            → 𝕄 → P
𝕄-recursion P f = 𝕄-induction (λ _ → P) f

𝕄-iteration : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕄 → P
𝕄-iteration P f = 𝕄-recursion P (λ X ϕ → f X)

\end{code}

A criterion for equality in 𝕄:

\begin{code}

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          (φ : X → 𝕄)
          (γ : Y → 𝕄)
        → (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
        → ssup X φ ＝ ssup Y γ
to-𝕄-＝ {X} φ γ (refl , f) = ap (ssup X) f

from-𝕄-＝ : {X Y : 𝓤 ̇ }
            (φ : X → 𝕄)
            (γ : Y → 𝕄)
          → ssup X φ ＝ ssup Y γ
          → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
from-𝕄-＝ {X}  φ γ refl = refl , refl

from-to-𝕄 : {X Y : 𝓤 ̇ }
            (φ : X → 𝕄)
            (γ : Y → 𝕄)
            (σ : Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
          → from-𝕄-＝ φ γ (to-𝕄-＝  φ γ σ) ＝ σ
from-to-𝕄 φ φ (refl , refl) = refl

to-from-𝕄 : {X Y : 𝓤 ̇ }
            (φ : X → 𝕄)
            (γ : Y → 𝕄)
            (p : ssup X φ ＝ ssup Y γ)
          → to-𝕄-＝  φ γ (from-𝕄-＝ φ γ p) ＝ p
to-from-𝕄 φ φ refl = refl

𝕄-＝ : {X Y : 𝓤 ̇ }
       (φ : X → 𝕄)
       (γ : Y → 𝕄)
     → ((ssup X φ) ＝ (ssup Y γ))
     ≃ (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
𝕄-＝ φ γ = qinveq (from-𝕄-＝ φ γ) (to-𝕄-＝ φ γ , to-from-𝕄 φ γ , from-to-𝕄 φ γ)




\end{code}

TODO. 𝕄 is locally small.
