\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ℕ where

data ℕ : Set₀  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

\end{code}
