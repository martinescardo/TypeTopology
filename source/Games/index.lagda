Martin Escardo and Paulo Oliva, 2-27 July 2021,

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Games.index where

open import Games.Constructor             -- For simplifying the construction of games.
open import Games.Examples                -- Miscelaneous small examples.
open import Games.FiniteHistoryDependent  -- Theory of finite history dependent games.
open import Games.FiniteHistoryDependentMonadic -- With additional monad for irrational players.
open import Games.J                       -- Selection monad.
open import Games.K                       -- Continuation (or quantifier) monad.
open import Games.Monad                   -- (Automaticall strong, wild) monads on types.
open import Games.Reader
open import Games.Structure               -- Equips game trees with structure.
open import Games.TicTacToe0
open import Games.TicTacToe1              -- Like TicTacToe0 but using Games.Constructor.
open import Games.TicTacToe2              -- More efficient and less elegant version.
open import Games.TypeTrees               -- Dependent type trees.
open import Games.alpha-beta              -- Many new things for efficiency.
-- open import Games.Main                 -- To be able to compile for efficieny.
                                          -- Can't ne imported here as it's not --safe.

\end{code}
