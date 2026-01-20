Martin Escardo, Paulo Oliva, 9th July 2024.

Alternative, equivalent, inductive definition of the type Game of
games, which may have some practical advantages, such as more modular
definitions of games.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module GamesLSU.Alternative (R : Type) where

open import UF.Equiv
open import UF.FunExt

open import GamesLSU.TypeTrees
open import GamesLSU.FiniteHistoryDependent R
             renaming (Game to Game' ;
                       game to game')

open import MonadOnTypesLSU.K

open K-definitions R

data Game : Type₁ where
 leaf   : R → Game
 branch : (X : Type) → K X → (X → Game) → Game

leaf' : R → Game'
leaf' r = game' [] (λ ⟨⟩ → r) ⟨⟩

branch' : (X : Type) → K X → (X → Game') → Game'
branch' X ϕ Gf = game' (X ∷ (game-tree ∘ Gf))
                       (λ (x :: xs) → payoff-function (Gf x) xs)
                       (ϕ :: (quantifier-tree ∘ Gf))

from-Game : Game → Game'
from-Game (leaf r)        = leaf' r
from-Game (branch X ϕ Gf) = branch' X ϕ (from-Game ∘ Gf)

\end{code}

We need the curried version h of the conversion function to-Game
defined below to convince the termination checker that the following
recursion does terminate.

\begin{code}

to-Game : Game' → Game
to-Game (game' Xt q ϕt) = h Xt q ϕt
 where
  h : (Xt : 𝑻) → (Path Xt → R) → 𝓚 Xt → Game
  h []       q ⟨⟩        = leaf (q ⟨⟩)
  h (X ∷ Xf) q (ϕ :: ϕf) = branch X ϕ (λ x → h (Xf x) (subpred q x) (ϕf x))

\end{code}

The equations we would have liked to use to define the function
to-Game are the following:

\begin{code}

to-Game-base
 : (q : Path [] → R)
 → to-Game (game' [] q ⟨⟩) ＝ leaf (q ⟨⟩)
to-Game-base q = refl

to-Game-step
 : (X : Type) (Xf : X → 𝑻) (ϕ : K X) (ϕf : (x : X) → 𝓚 (Xf x)) (q : Path (X ∷ Xf) → R)
 → to-Game (game' (X ∷ Xf) q (ϕ :: ϕf))
 ＝ branch X ϕ (λ x → to-Game (game' (Xf x) (subpred q x) (ϕf x)))
to-Game-step X Xf ϕ ϕf q = refl

\end{code}

We also have the following equivalent definitional equalities
expressed in terms of leaf' and branch':

\begin{code}

to-Game-base' : (r : R) → to-Game (leaf' r) ＝ leaf r
to-Game-base' r = refl

module _
         (X : Type)
         (Xf : X → 𝑻)
         (ϕ : K X)
         (ϕf : (x : X) → 𝓚 (Xf x))
         (q : Path (X ∷ Xf) → R)
       where

 subgame : X → Game'
 subgame x = game' (Xf x) (subpred q x) (ϕf x)

 to-Game-step' : to-Game (branch' X ϕ subgame) ＝ branch X ϕ (to-Game ∘ subgame)
 to-Game-step' = refl

\end{code}

The above conversion functions are mutually inverse and so the types
Game and Game' are equivalent, assuming function extensionality.

\begin{code}

module _ (fe : Fun-Ext) where

 from-to-Game : from-Game ∘ to-Game ∼ id
 from-to-Game (game' Xt q ϕt) = h Xt q ϕt
  where
   h : (Xt : 𝑻)
       (q : Path Xt → R)
       (ϕt : 𝓚 Xt)
     → from-Game (to-Game (game' Xt q ϕt)) ＝ game' Xt q ϕt
   h []       q ⟨⟩       = refl
   h (X ∷ Xf) q (ϕ :: ϕf) =
    from-Game (to-Game (game' (X ∷ Xf) q (ϕ :: ϕf))) ＝⟨refl⟩
    from-Game (branch X ϕ (to-Game ∘ Gf))            ＝⟨refl⟩
    branch' X ϕ Hf                                   ＝⟨ I ⟩
    branch' X ϕ Gf                                   ＝⟨refl⟩
    game' (X ∷ Xf) q (ϕ :: ϕf)                       ∎
    where
     Gf Hf : X → Game'
     Gf x = subgame X Xf ϕ ϕf q x
     Hf x = from-Game (to-Game (Gf x))

     IH : Hf ∼ Gf
     IH x = h (Xf x) (subpred q x) (ϕf x)

     I : branch' X ϕ Hf ＝ branch' X ϕ Gf
     I = ap (branch' X ϕ) (dfunext fe IH)

 to-from-Game : to-Game ∘ from-Game ∼ id
 to-from-Game (leaf x)        = refl
 to-from-Game (branch X ϕ Gf) =
  to-Game (from-Game (branch X ϕ Gf))    ＝⟨refl⟩
  to-Game (branch' X ϕ (from-Game ∘ Gf)) ＝⟨refl⟩
  branch X ϕ (to-Game ∘ from-Game ∘ Gf)  ＝⟨ I ⟩
  branch X ϕ Gf                          ∎
  where
   I = ap (branch X ϕ) (dfunext fe (to-from-Game ∘ Gf))

 Game-is-equiv-to-Game' : Game ≃ Game'
 Game-is-equiv-to-Game' = qinveq from-Game (to-Game , to-from-Game , from-to-Game)

\end{code}
