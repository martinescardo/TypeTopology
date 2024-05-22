--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import MLTT.Spartan
open import Ordinals.Brouwer

module Ordinals.BrouwerArithmetic where

\end{code}

Addition of Brouwer trees.

\begin{code}

_+B_ : B → B → B
u +B Z   = u
u +B S v = S (u +B v)
u +B L ϕ = L (λ i → u +B ϕ i)

\end{code}

Multiplication of Brouwer trees.

\begin{code}

_×B_ : B → B → B
u ×B Z   = Z
u ×B S v = (u ×B v) +B u
u ×B L ϕ = L (λ i → u ×B ϕ i)

\end{code}

Exponentiation of Brouwer trees.

\begin{code}

_^B_ : B → B → B
u ^B  Z     = S Z
u ^B  (S v) = (u ^B v) ×B u
u ^B  (L ϕ) = L (λ i → u ^B ϕ i)

\end{code}

Given a natural number `n : ℕ`, `B-finite n` denotes the finite ordinal
corresponding to `n`.

\begin{code}

finite : ℕ → B
finite = rec Z S

\end{code}

By taking the limit of all finite ordinals, we obtain `ω`.

\begin{code}

ω : B
ω = L finite

\end{code}

We now write down the sequence of iterating the operation of exponentiating `ω`
to itself.

\begin{code}

ω-tower : ℕ → B
ω-tower = rec ω (ω ^B_)

ω-tower-0 : ω-tower 0 ＝ ω
ω-tower-0 = refl

ω-tower-1 : ω-tower 1 ＝ (ω ^B ω)
ω-tower-1 = refl

\end{code}

and so on and so on...

When we take the limit of this sequence, we obtain `ε₀`.

\begin{code}

ε₀ : B
ε₀ = L ω-tower
