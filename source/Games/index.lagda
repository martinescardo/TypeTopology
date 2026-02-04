Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with many
additions 2024-2025.


\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.index where

import Games.TypeTrees                             -- (0)
import Games.FiniteHistoryDependent                -- (1)
import Games.Discussion                            -- (2)
import Games.Examples                              -- (3)
import Games.FiniteHistoryDependentMonadic         -- (4)
import Games.FiniteHistoryDependentRelativeMonadic -- (5)
import Games.Constructor                           -- (6)
import Games.TicTacToe0                            -- (7)
import Games.TicTacToe1                            -- (7)
import Games.TicTacToe2                            -- (7)
import Games.alpha-beta                            -- (8)
import Games.OptimalPlays                          -- (9)
import Games.Alternative                           -- (10)
-- import Games.Main                               -- (11)

\end{code}

0. TypeTrees.

   We define and briefly study "dependent type trees", which are
   closely related to Peter Aczels W-type of CZF sets, and which we use
   to define games in (1) below.

   [0] Peter Aczel. "The Type Theoretic Interpretation of Constructive Set
       Theory". Studies in Logic and the Foundations of Mathematics, Volume
       96, 1978, Pages 55-66.  https://doi.org/10.1016/S0049-237X(08)71989-X

   More references are given in the file (2).

1. FiniteHistoryDependent.

   Theory of finite history dependent games, as presented in the paper

   [1] Martin Escardo and Paulo Oliva. Higher-order games with
       dependent types.  Theoretical Computer Science, Volume 974, 29
       September 2023, 114111.
       https://doi.org/10.48550/arXiv.2212.07735
       https://doi.org/10.1016/j.tcs.2023.114111

   We study finite, history dependent games of perfect information
   using selection functions and dependent-type trees.

   In particular, this file defines the type Game of such games, used
   in the following file.

2. Discussion.

   This has some discussion regarding (0) above, both in English
   prose and in Agda, as is part of the published paper [1].

3. Examples.

   This has miscelaneous small examples.

4. FiniteHistoryDependentMonadic.

   This is work in progress, where the idea is to eventually use this
   for considering rational players playing against irrational players.

5. FiniteHistoryDependentRelativeMonadic.

   It turns out that (4) needs affine monads on types, but we are able
   to construct examples of such monads on only certain types,
   e.g. types with decidable equality (for the affine monad of nonempty lists
   without repetitions). For this purpose, we rework (4) above using
   "relative monads on structured types".

6. Constructor.

   This is for simplifying the construction of games.

7. TicTacToe0-2.

   These have several variations of tic-tac-toe, for the sake of
   trying to find an efficient version.

   TicTacToe1 is like TicTacToe0 but using (6) above.

   TicTacToe2 is more efficient but less elegant.

8. alpha-beta.

   This implements alpha-beta and more for efficiency, as exemplified
   by e.g. tic-tac-toe.  However, it doesn't yet include correctness
   proofs, although what needs to be proved is indicated in the file.

9. OptimalPlays.

   This computes the list of all optimal plays of a game, in two ways,
   one using (4) above.

10. Alternative.

    This has an alternative, equivalent definition of game, which may
    be more convenient, but which we haven't used yet.

11. Main.

    This is a Haskell interface for compiling Agda and hence getting
    better run times than above.

    It is commented out because it isn't technically --safe, although
    it is safe in practice.

    It is imported from Unsafe.index, which in turn is imported by
    AllModulesIndex, to make sure it is always type checked by the
    github action.


The above files depend on the following:

\begin{code}

import DiscreteGraphicMonoids.index
import MonadOnTypes.index
import RelativeMonadOnStructuredTypes.index

\end{code}
