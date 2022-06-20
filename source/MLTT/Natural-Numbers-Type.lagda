\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MLTT.Natural-Numbers-Type where

data ℕ : Set₀  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}
