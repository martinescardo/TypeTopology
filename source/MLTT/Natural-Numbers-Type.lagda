\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Natural-Numbers-Type where

data ℕ : Set₀  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}
