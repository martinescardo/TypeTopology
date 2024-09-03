Martin Escardo and Paulo Oliva, 2-27 July 2021,

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

module GamesExperimental.index where

open import GamesExperimental.Constructor             -- For simplifying the construction of games.
open import GamesExperimental.Examples                -- Miscelaneous small examples.
open import GamesExperimental.FiniteHistoryDependent  -- Theory of finite history dependent games.
open import GamesExperimental.Transformer             -- With additional monad for irrational players.
open import GamesExperimental.J                       -- Selection monad.
open import GamesExperimental.K                       -- Continuation (or quantifier) monad.
open import GamesExperimental.JK                      -- Relationship between the two mondas.
open import GamesExperimental.Monad                   -- (Automatically strong, wild) monads on suitable types.
open import GamesExperimental.Reader
open import GamesExperimental.NonEmptyList
open import GamesExperimental.TicTacToe0
open import GamesExperimental.TicTacToe1              -- Like TicTacToe0 but using GamesExperimental.Constructor.
open import GamesExperimental.TicTacToe2              -- More efficient and less elegant version.
open import GamesExperimental.TypeTrees               -- Dependent type trees.
open import GamesExperimental.alpha-beta              -- Many new things for efficiency.
open import GamesExperimental.alpha-beta-examples
open import GamesExperimental.Discussion

-- open import GamesExperimental.Main                 -- To be able to compile for efficieny.
                                          -- Can't be imported here as it's not --safe.
                                          -- This is for Agda compilation to Haskell of
                                          -- examples to be able to run them more efficiently.

\end{code}
