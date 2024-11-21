---
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
---

This module contains the definitions of basic arithmetic operations on Brouwer
ordinals as well as the definition of the first epsilon number.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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

infixr 6 _+B_

+B-respects-≈-left : (b c d : B)
                   → b ≈ d
                   → b +B c ≈ d +B c
+B-respects-≈-left b Z     d h = h
+B-respects-≈-left b (S c) d h = S≈ (+B-respects-≈-left b c d h)
+B-respects-≈-left b (L ϕ) d h = L≈ _ _ (λ n → +B-respects-≈-left b (ϕ n) d h)

+B-respects-≈-right : (b c d : B)
                    → c ≈ d
                    → b +B c ≈ b +B d
+B-respects-≈-right b Z     Z     Z≈         = ≈-refl b
+B-respects-≈-right b (S c) (S d) (S≈ h)     = S≈ (+B-respects-≈-right b c d h)
+B-respects-≈-right b (L ϕ) (L ψ) (L≈ ϕ ψ x) =
 L≈ _ _ (λ n → +B-respects-≈-right b (ϕ n) (ψ n) (x n))

+B-respects-≈ : {b c d e : B}
              → b ≈ c
              → d ≈ e
              → b +B d ≈ c +B e
+B-respects-≈ {b} {c} {d} {e} h l =
 ≈-trans (+B-respects-≈-left b d c h) (+B-respects-≈-right c d e l)

\end{code}

Multiplication of Brouwer trees.

\begin{code}

_×B_ : B → B → B
u ×B Z   = Z
u ×B S v = (u ×B v) +B u
u ×B L ϕ = L (λ i → u ×B ϕ i)

infixr 5 _×B_

×B-respects-≈-left : (b c d : B)
                   → b ≈ d
                   → b ×B c ≈ d ×B c
×B-respects-≈-left b Z     d h = Z≈
×B-respects-≈-left b (S c) d h = +B-respects-≈ (×B-respects-≈-left b c d h) h
×B-respects-≈-left b (L ϕ) d h = L≈ _ _ (λ n → ×B-respects-≈-left b (ϕ n) d h)

×B-respects-≈-right : (b c d : B)
                    → c ≈ d
                    → b ×B c ≈ b ×B d
×B-respects-≈-right b Z Z Z≈ = Z≈
×B-respects-≈-right b (S c) (S d) (S≈ h) =
 +B-respects-≈-left (b ×B c) b (b ×B d) (×B-respects-≈-right b c d h)
×B-respects-≈-right b (L ϕ) (L ψ) (L≈ ϕ ψ x) =
 L≈ _ _ (λ n → ×B-respects-≈-right b (ϕ n) (ψ n) (x n))

×B-respects-≈ : {b c d e : B}
              → b ≈ c
              → d ≈ e
              → b ×B d ≈ c ×B e
×B-respects-≈ {b} {c} {d} {e} h l =
 ≈-trans (×B-respects-≈-left b d c h) (×B-respects-≈-right c d e l)

\end{code}

Exponentiation of Brouwer trees.

\begin{code}

_^B_ : B → B → B
u ^B  Z     = S Z
u ^B  (S v) = (u ^B v) ×B u
u ^B  (L ϕ) = L (λ i → u ^B ϕ i)

^B-respects-≈-left : (b c d : B)
                   → b ≈ d
                   → b ^B c ≈ d ^B c
^B-respects-≈-left b Z     d h = S≈ Z≈
^B-respects-≈-left b (S c) d h = ×B-respects-≈ (^B-respects-≈-left b c d h) h
^B-respects-≈-left b (L ϕ) d h = L≈ _ _ (λ n → ^B-respects-≈-left b (ϕ n) d h)

^B-respects-≈-right : (b c d : B)
                    → c ≈ d
                    → b ^B c ≈ b ^B d
^B-respects-≈-right b Z Z Z≈ = S≈ Z≈
^B-respects-≈-right b (S c) (S d) (S≈ h) =
 ×B-respects-≈-left (b ^B c) b (b ^B d) (^B-respects-≈-right b c d h)
^B-respects-≈-right b (L ϕ) (L ψ) (L≈ ϕ ψ x) =
 L≈ _ _ (λ n → ^B-respects-≈-right b (ϕ n) (ψ n) (x n))

^B-respects-≈ : {b c d e : B}
              → b ≈ c
              → d ≈ e
              → b ^B d ≈ c ^B e
^B-respects-≈ {b} {c} {d} {e} h l =
 ≈-trans (^B-respects-≈-left b d c h) (^B-respects-≈-right c d e l)

infixr 4 _^B_

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

\end{code}
