Martin Escardo and Paulo Oliva, 2-27 July 2021,
refactored and slightly improved October 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Games.index where

open import Games.TypeTrees               -- Dependent type trees.
open import Games.FiniteHistoryDependent  -- Theory of finite history dependent games.
open import Games.TicTacToe0              -- This version uses only the above two modules.
open import Games.Constructor             -- This is for simplifying the construction of games.
open import Games.TicTacToe1              -- This is like TicTacToe0 but using the previous module.
open import Games.TicTacToe2              -- This is a more efficient and less elegant version.
open import Games.Examples                -- These are miscelaneous small examples.

\end{code}
