Martin Escardo and Paulo Oliva, 2-27 July 2021,

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.index where

import Games.Constructor             -- For simplifying the construction of games.
import Games.Examples                -- Miscelaneous small examples.
import Games.FiniteHistoryDependent  -- Theory of finite history dependent games.
import Games.Transformer             -- With additional monad for irrational players.
import Games.J                       -- Selection monad.
import Games.K                       -- Continuation (or quantifier) monad.
import Games.JK                      -- Relationship between the two mondas.
import Games.Monad                   -- (Automatically strong, wild) monads on types.
import Games.Reader
import Games.NonEmptyList
import Games.TicTacToe0
import Games.TicTacToe1              -- Like TicTacToe0 but using Games.Constructor.
import Games.TicTacToe2              -- More efficient and less elegant version.
import Games.TypeTrees               -- Dependent type trees.
import Games.alpha-beta              -- Many new things for efficiency.
import Games.Discussion

-- import Games.Main                 -- To be able to compile for efficieny.
                                     -- Can't be imported here as it's not --safe.
                                     -- This is for Agda compilation to Haskell of
                                     -- examples to be able to run them more efficiently.

\end{code}
