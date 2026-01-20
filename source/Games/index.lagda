Martin Escardo and Paulo Oliva, 2-27 July 2021,

Same as Games but with more general universes (MGU).

The main novelty here, for now, is FiniteHistoryDependentRelativeMonadic, which works with relative
monads on structured types, so that e.g. we can work with the affine
monad of non-empty lists without repetitions for some applications.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.index where

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
import Games.alpha-beta              -- Many new things for efficiency.
import Games.alpha-beta-examples
import Games.Discussion

\end{code}
