Martin Escardo and Paulo Oliva, 2-27 July 2021,

Same as Games but with more general universes (MGU).

The main novelty here, for now, is FiniteHistoryDependentRelativeMonadic, which works with relative
monads on structured types, so that e.g. we can work with the affine
monad of non-empty lists without repetitions for some applications.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module GamesMGU.index where

import GamesMGU.Constructor             -- For simplifying the construction of games.
import GamesMGU.Examples                -- Miscelaneous small examples.
import GamesMGU.FiniteHistoryDependent  -- Theory of finite history dependent games.
import GamesMGU.FiniteHistoryDependentMonadic
                                        -- With additional monad for irrational players.
import GamesMGU.FiniteHistoryDependentRelativeMonadic
                                        -- Same but with relative monad.
import GamesMGU.TicTacToe0
import GamesMGU.TicTacToe1              -- Like TicTacToe0 but using GamesMGU.Constructor.
import GamesMGU.TicTacToe2              -- More efficient and less elegant version.
import GamesMGU.TypeTrees               -- Dependent type trees.
import GamesMGU.alpha-beta              -- Many new things for efficiency.
import GamesMGU.alpha-beta-examples
import GamesMGU.Discussion

\end{code}
