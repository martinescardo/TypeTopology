Martin Escardo, Paulo Oliva, 2-27 July 2021

This module has functions to build games.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.Constructor
        {𝓤 𝓦₀ : Universe}
        (R : 𝓦₀ ̇ )
       where

open import UF.FunExt

open import Games.TypeTrees {𝓤}
open import Games.FiniteHistoryDependent {𝓤} {𝓦₀} R
open import MonadOnTypes.J
open import MonadOnTypes.JK R

open J-definitions R

\end{code}

We use the type GameJ to present games equipped with selection
functions, as in some examples, such as tic-tac-toe this is easier
than to give a game directly.

\begin{code}

data GameJ : 𝓤 ⁺ ⊔ 𝓦₀ ̇ where
 leaf   : R → GameJ
 branch : (X : 𝓤 ̇ ) (Xf : X → GameJ) (ε : J X) → GameJ

dtt : GameJ → 𝑻
dtt (leaf x)        = []
dtt (branch X Xf ε) = X ∷ λ x → dtt (Xf x)

predicate : (Γ : GameJ) → Path (dtt Γ) → R
predicate (leaf r)        ⟨⟩        = r
predicate (branch X Xf ε) (x :: xs) = predicate (Xf x) xs

selections : (Γ : GameJ) → 𝓙 (dtt Γ)
selections (leaf r)        = ⟨⟩
selections (branch X Xf ε) = ε :: (λ x → selections (Xf x))

quantifiers : (Γ : GameJ) → 𝓚 (dtt Γ)
quantifiers (leaf r)        = ⟨⟩
quantifiers (branch X Xf ε) = overline ε :: (λ x → quantifiers (Xf x))

Game-from-GameJ : GameJ → Game
Game-from-GameJ Γ = game (dtt Γ) (predicate Γ) (quantifiers Γ)

strategyJ : (Γ : GameJ) → Strategy (dtt Γ)
strategyJ Γ = selection-strategy (selections Γ) (predicate Γ)

Selection-Strategy-TheoremJ : Fun-Ext
                            → (Γ : GameJ)
                            → is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
Selection-Strategy-TheoremJ fe Γ = γ
 where
  δ : (Γ : GameJ) → (selections Γ) Attains (quantifiers Γ)
  δ (leaf r)        = ⟨⟩
  δ (branch X Xf ε) = (λ p → refl) , (λ x → δ (Xf x))

  γ : is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
  γ = Selection-Strategy-Theorem fe (Game-from-GameJ Γ) (selections Γ) (δ Γ)

\end{code}

The following is used in conjunction with GameJ to build certain games
in a convenient way.

\begin{code}

build-GameJ : (r     : R)
              (Board : 𝓥 ̇ )
              (τ     : Board → R + (Σ M ꞉ 𝓤 ̇ , (M → Board) × J M))
              (n     : ℕ)
              (b     : Board)
            → GameJ
build-GameJ r Board τ n b = h n b
 where
  h : ℕ → Board → GameJ
  h 0        b = leaf r
  h (succ n) b = g (τ b)
   where
    g : (f : R + (Σ M ꞉ 𝓤 ̇ , (M → Board) × J M)) → GameJ
    g (inl r)              = leaf r
    g (inr (M , play , ε)) = branch M Xf ε
     where
      Xf : M → GameJ
      Xf m = h n (play m)

build-Game : (r  : R)
             (Board : 𝓥 ̇ )
             (τ     : Board → R + (Σ M ꞉ 𝓤 ̇ , (M → Board) × J M))
             (n     : ℕ)
             (b     : Board)
           → Game
build-Game r Board τ n b = Game-from-GameJ (build-GameJ r Board τ n b)

\end{code}
