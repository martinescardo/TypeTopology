Martin Escardo and Paulo Oliva, 2-27 July 2021,

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

module GamesExperimental.index where

import GamesExperimental.Constructor             -- For simplifying the construction of games.
import GamesExperimental.Examples                -- Miscelaneous small examples.
import GamesExperimental.FiniteHistoryDependent  -- Theory of finite history dependent games.
import GamesExperimental.Transformer             -- With additional monad for irrational players.
import GamesExperimental.J                       -- Selection monad.
import GamesExperimental.K                       -- Continuation (or quantifier) monad.
import GamesExperimental.JK                      -- Relationship between the two mondas.
import GamesExperimental.Monad                   -- (Automatically strong, wild) monads on suitable types.
import GamesExperimental.Reader
import GamesExperimental.NonEmptyList
import GamesExperimental.TicTacToe0
import GamesExperimental.TicTacToe1              -- Like TicTacToe0 but using GamesExperimental.Constructor.
import GamesExperimental.TicTacToe2              -- More efficient and less elegant version.
import GamesExperimental.TypeTrees               -- Dependent type trees.
import GamesExperimental.alpha-beta              -- Many new things for efficiency.
import GamesExperimental.alpha-beta-examples
import GamesExperimental.Discussion

-- import GamesExperimental.Main                 -- To be able to compile for efficieny.
                                          -- Can't be imported here as it's not --safe.
                                          -- This is for Agda compilation to Haskell of
                                          -- examples to be able to run them more efficiently.

\end{code}
