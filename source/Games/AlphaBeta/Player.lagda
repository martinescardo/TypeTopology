Martin Escardo and Paulo Oliva, November 2026.

Players, and the labels of the internal nodes of a game tree.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.AlphaBeta.Player where

open import MLTT.Spartan
open import MonadOnTypes.NonEmptyList using (List⁺)

data Player : 𝓤₀ ̇ where
 maximizer minimizer : Player

\end{code}

Each internal node of a game tree is labelled by the player who moves
at that node and by the non-empty list of the moves available there,
in the order in which the search considers them.

\begin{code}

Node : 𝓤 ̇ → 𝓤 ̇
Node X = Player × List⁺ X

\end{code}
