Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with many
additions 2024-2025.


\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.index where

import Games.Alternative
import Games.Constructor             -- For simplifying the construction of games.
import Games.Examples                -- Miscelaneous small examples.
import Games.FiniteHistoryDependent  -- Theory of finite history dependent games.
import Games.FiniteHistoryDependentMonadic
                                     -- With additional monad for irrational players.
import Games.FiniteHistoryDependentRelativeMonadic
                                     -- Same but with relative monad.
import Games.TicTacToe0
import Games.TicTacToe1              -- Like TicTacToe0 but using Games.Constructor.
import Games.TicTacToe2              -- More efficient and less elegant version.
import Games.TypeTrees               -- Dependent type trees.
import Games.alpha-beta              -- alpha-beta and more for efficiency.
import GamesLSU.OptimalPlays         -- Computes the list of all optimal plays of a game.
import Games.Discussion
-- import Games.Main


\end{code}
