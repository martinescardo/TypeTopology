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

open import MLTT.W
open import UF.Base
open import UF.Equiv
-- open import Ordinals.Notions
open import Iterative.W-Properties

\end{code}

The type of iterative multisets:

\begin{code}

𝕄 : 𝓤 ⁺ ̇
𝕄 = W (𝓤 ̇ ) id

{-
data 𝕄 : 𝓤 ⁺ ̇ where
 ssup : (X : 𝓤 ̇ ) (φ : X → 𝕄) → 𝕄
-}

\end{code}

Every W-type can be mapped to 𝕄 as follows:

\begin{code}

W-to-𝕄 : {X : 𝓤 ̇ } {A : X → 𝓤 ̇ }
       → W X A → 𝕄
W-to-𝕄 {X} {A} (ssup x f) = ssup (A x) (λ a → W-to-𝕄 (f a))

\end{code}

In the case of ordinals, ssup stands for "strong supremum", "strict
supremum" or "supremum of successors.

\begin{code}

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root = W-root

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest = W-forest

\end{code}

The induction principle for 𝕄:

\begin{code}

𝕄-induction : (P : 𝕄 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕄)
                  → ((x : X) → P (ϕ x))
                  → P (ssup X ϕ))
            → (M : 𝕄) → P M
𝕄-induction = W-induction

𝕄-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → 𝕄) → (X → P) → P)
            → 𝕄 → P
𝕄-recursion = W-recursion

𝕄-iteration : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕄 → P
𝕄-iteration = W-iteration

\end{code}

A criterion for equality in 𝕄:

\begin{code}

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
        → ssup X φ ＝[ 𝕄 ] ssup Y γ
to-𝕄-＝ = to-W-＝ (𝓤 ̇ ) id

from-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
          → ssup X φ ＝[ 𝕄 ] ssup Y γ
          → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
from-𝕄-＝ = from-W-＝ _ _

from-to-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
            (σ : Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
          → from-𝕄-＝ {X} {Y} {φ} {γ} (to-𝕄-＝ σ) ＝[ type-of σ ] σ
from-to-𝕄-＝ = from-to-W-＝ _ _

to-from-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
            (p : ssup X φ ＝ ssup Y γ)
          → to-𝕄-＝ (from-𝕄-＝ p) ＝ p
to-from-𝕄-＝ = to-from-W-＝ _ _

𝕄-＝ : {X Y : 𝓤 ̇ }
       {φ : X → 𝕄}
       {γ : Y → 𝕄}
     → ((ssup X φ) ＝[ 𝕄 ] (ssup Y γ))
     ≃ (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
𝕄-＝ = W-＝ _ _

\end{code}

TODO. 𝕄 is locally small.
