Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

In previous work [1, 2] we showed that minimax-type searches can be
performed using monadic programming, via the continuation monad for
calculating optimal outcomes, and the selection monad, with the
product of selection functions, for optimal plays and strategies. In
[3] we added game trees, in which the type of moves at a round, and
the number of rounds, may depend on the moves played so far, and
these are the games of this formalization.

Here we compute optimal plays with the product of quantifiers instead,
which is more efficient in practice, by extending the type of outcomes
to include the play that leads to the outcome. We then further improve
efficiency with alpha-beta pruning, by combining the continuation
monad with the reader monad, which records the alpha-beta bounds
within the outcomes, leaving the types of moves unchanged.

[1] Martin Escardo and Paulo Oliva. Selection functions, bar
    recursion and backward induction. Mathematical Structures in
    Computer Science, Volume 20, Issue 2, 2010, 127-168.
    https://doi.org/10.1017/S0960129509990351

[2] Martin Escardo and Paulo Oliva. What sequential games, the
    Tychonoff theorem and the double-negation shift have in common.
    Proceedings of the Third ACM SIGPLAN Workshop on Mathematically
    Structured Functional Programming (MSFP 2010), 21-32.
    https://doi.org/10.1145/1863597.1863605

[3] Martin Escardo and Paulo Oliva. Higher-order games with
    dependent types. Theoretical Computer Science, Volume 974, 29
    September 2023, 114111.
    https://doi.org/10.48550/arXiv.2212.07735
    https://doi.org/10.1016/j.tcs.2023.114111

The following imported Agda files are a formalization of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.

The paper, and the Haskell programs discussed in it, will be made
available soon and linked here.

This supersedes the file deprecated.alpha-beta of March - April 2023,
where the ideas originated, and where we got started writing the
proofs on 27th January 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.AlphaBeta.index where

import Games.AlphaBeta.Player                   -- (0)
import Games.AlphaBeta.Maximizer                -- (1)
import Games.AlphaBeta.Minimizer                -- (2)
import Games.AlphaBeta.ViaProductsOfQuantifiers -- (3)
import Games.AlphaBeta.OptimalPlays             -- (4)
import Games.AlphaBeta.Examples                 -- (5)
import Games.AlphaBeta.Summary                  -- (6)
import Games.AlphaBeta.Article                  -- (7)

\end{code}

0. Player.

   Players, and the labels of the internal nodes of a game tree.

1. Maximizer.

   The maximizing quantifier φmax and its alpha-beta version φ*max,
   whose outcomes are in the reader monad T, which records the pair
   (α , β) of bounds, of Sections 2.1, 3.1 and 4 of the paper, and
   Lemmas 1 and 2. Then the induction step, for the maximizing player,
   of the proof of Theorem 1 of the paper, which is in (3) below.

2. Minimizer.

   The minimizing quantifiers are the maximizing quantifiers for the
   opposite order. The induction step of the proof of Theorem 1 for
   the minimizing player follows from that for the maximizing player.

3. ViaProductsOfQuantifiers.

   This is the main file. The alpha-beta search is the product of
   quantifiers optimized via the reader monad, and it agrees with the
   product of the original quantifiers (Theorem 1 of the paper). Hence,
   with suitable initial bounds, it computes the optimal outcome of the
   game (Corollary 1).

4. OptimalPlays.

   Computing optimal plays (Section 5 of the paper). We show that the
   optimal outcome of the extended game is a pair of the optimal outcome
   of the original game and an optimal play of the original game, and
   the same is true of the outcome computed by the alpha-beta search
   (Corollary 2).

5. Examples.

   The example game of Sections 2 and 3 of the paper, which is the
   game tree of the Wikipedia article on alpha-beta pruning.

6. Summary.

   This file states the main theorems, Theorem 1 and Corollaries 1 and 2
   of the paper, and displays every definition that their statements use.

7. Article.

   This file follows the definitions, lemmas and theorems of the
   paper, in the same order and with the same numbering.
