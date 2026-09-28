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
open K-definitions {𝓦₀} {R}

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

The strategic path of a strategy in subgame perfect equilibrium is an
optimal play.

\begin{code}

optimal-play-gives-optimal-outcome
 : {Xt : 𝑻}
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
   (xs : Path Xt)
 → is-optimal-play {Xt} ϕt q xs
 → q xs ＝ optimal-outcome (game Xt q ϕt)
optimal-play-gives-optimal-outcome {[]}     ⟨⟩        q ⟨⟩        ⟨⟩ = refl
optimal-play-gives-optimal-outcome {X ∷ Xf} (ϕ :: ϕf) q (x :: xs) (o :: os)
 = subpred q x xs                                     ＝⟨ IH ⟩
   optimal-outcome (game (Xf x) (subpred q x) (ϕf x)) ＝⟨ o ⁻¹ ⟩
   optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))        ∎
 where
  IH : subpred q x xs ＝ optimal-outcome (game (Xf x) (subpred q x) (ϕf x))
  IH = optimal-play-gives-optimal-outcome {Xf x} (ϕf x) (subpred q x) xs os

open import UF.FunExt

strategic-path-is-optimal-play
 : funext (𝓥 ⊔ 𝓦₀) 𝓦₀
 → {Xt : 𝑻}
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
   (σ : Strategy Xt)
 → is-in-sgpe ϕt q σ
 → is-optimal-play ϕt q (strategic-path σ)
strategic-path-is-optimal-play fe {[]} ⟨⟩ q ⟨⟩ ⟨⟩ = ⋆
strategic-path-is-optimal-play fe {X ∷ Xf} ϕt@(ϕ :: ϕf) q σ@(x₀ :: σf) ot@(o :: os)
 = I , IH x₀
 where
  IH : (x : X) → is-optimal-play (ϕf x) (subpred q x) (strategic-path (σf x))
  IH x = strategic-path-is-optimal-play fe {Xf x} (ϕf x) (subpred q x) (σf x) (os x)

  I : is-optimal-move q ϕ ϕf x₀
  I = optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))                  ＝⟨refl⟩
      sequenceᴷ {X ∷ Xf} (ϕ :: ϕf) q                               ＝⟨refl⟩
      ϕ (λ x → sequenceᴷ (ϕf x) (subpred q x))                     ＝⟨refl⟩
      ϕ (λ x → optimal-outcome (game (Xf x) (subpred q x) (ϕf x))) ＝⟨ I₁ ⟩
      ϕ (λ x → subpred q x (strategic-path (σf x)))                ＝⟨ o ⁻¹ ⟩
      q (strategic-path σ)                                         ＝⟨refl⟩
      subpred q x₀ (strategic-path (σf x₀))                        ＝⟨ I₂ ⟩
      optimal-outcome (game (Xf x₀) (subpred q x₀) (ϕf x₀))        ∎
       where
        I₀ : (x : X)
           → optimal-outcome (game (Xf x) (subpred q x) (ϕf x))
           ＝ subpred q x (strategic-path (σf x))
        I₀ x = (optimal-play-gives-optimal-outcome
                 (ϕf x) (subpred q x) (strategic-path (σf x)) (IH x))⁻¹

        I₁ = ap ϕ (dfunext fe I₀)
        I₂ = optimal-play-gives-optimal-outcome
              (ϕf x₀) (subpred q x₀) (strategic-path (σf x₀)) (IH x₀)

\end{code}
