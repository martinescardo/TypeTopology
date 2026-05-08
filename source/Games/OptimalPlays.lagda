Martin Escardo, Paulo Oliva, 27th November 2024 - 14th May 2025

We define optimal moves and optimal plays for sequential games.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝓤)

module Games.OptimalPlays
        {𝓥 𝓦₀  : Universe}
        (R : 𝓦₀ ̇ )
       where

private
 𝓤 : Universe
 𝓤 = 𝓥 ⊔ 𝓦₀

open import Games.FiniteHistoryDependent {𝓤} {𝓦₀} R
open import Games.TypeTrees {𝓤}
open import MonadOnTypes.K
open K-definitions R

\end{code}

The following are the main two notions considered in this file.

\begin{code}

is-optimal-move : {X : 𝓤 ̇ }
                  {Xf : X → 𝑻}
                  (q : (Σ x ꞉ X , Path (Xf x)) → R)
                  (ϕ : K X)
                  (ϕf : (x : X) → 𝓚 (Xf x))
                → X
                → 𝓦₀ ̇
is-optimal-move {X} {Xf} q ϕ ϕf x =
 optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))
 ＝ optimal-outcome (game (Xf x) (subpred q x) (ϕf x))

is-optimal-play : {Xt : 𝑻} → 𝓚 Xt → (Path Xt → R) → Path Xt → 𝓦₀ ̇
is-optimal-play {[]}     ⟨⟩        q ⟨⟩        = 𝟙
is-optimal-play {X ∷ Xf} (ϕ :: ϕf) q (x :: xs) =
   is-optimal-move {X} {Xf} q ϕ ϕf x
 × is-optimal-play {Xf x} (ϕf x) (subpred q x) xs

is-game-optimal-play : (G : Game) → Path (game-tree G) → 𝓦₀ ̇
is-game-optimal-play (game Xt q ϕt) = is-optimal-play {Xt} ϕt q

is-game-optimal-outcome : Game → R → 𝓦₀ ̇
is-game-optimal-outcome G r = (r ＝ optimal-outcome G)

\end{code}
