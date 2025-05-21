Martin Escardo and Paulo Oliva, 2-27 July 2021,

Same as Games but with more general universes (MGU), and also using the flag --no-level-universe.

We need this for considering more general monads, in particular.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

module GamesMGU.index where

import GamesMGU.Constructor             -- For simplifying the construction of games.
import GamesMGU.Examples                -- Miscelaneous small examples.
import GamesMGU.FiniteHistoryDependent  -- Theory of finite history dependent games.
import GamesMGU.FiniteHistoryDependentMonadic
                                        -- With additional monad for irrational players.
import GamesMGU.J                       -- Selection monad.
import GamesMGU.K                       -- Continuation (or quantifier) monad.
import GamesMGU.JK                      -- Relationship between the two mondas.
import GamesMGU.Monad                   -- (Automatically strong, wild) monads on suitable types.
import GamesMGU.Reader
import GamesMGU.NonEmptyList
import GamesMGU.TicTacToe0
import GamesMGU.TicTacToe1              -- Like TicTacToe0 but using GamesMGU.Constructor.
import GamesMGU.TicTacToe2              -- More efficient and less elegant version.
import GamesMGU.TypeTrees               -- Dependent type trees.
import GamesMGU.alpha-beta              -- Many new things for efficiency.
import GamesMGU.alpha-beta-examples
import GamesMGU.Discussion

\end{code}
