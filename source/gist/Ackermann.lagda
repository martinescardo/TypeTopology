Martin Escardo, 2nd February 2026.

This is regarding the discussion thread [1]. We give a definition of the
Ackermann function by induction on the ordinal ω².

[1] https://mathstodon.xyz/deck/@cxandru@types.pl/115984233527105134

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.Ackermann where

\end{code}

We first recall the version attributed to Péter and Robison in [2],
which is also popularly known as "the" Ackermann function.

[2] https://en.wikipedia.org/wiki/Ackermann_function#Definition

This can be defined in system T and hence in MLTT.

\begin{code}

open import MLTT.Spartan

A : ℕ → ℕ → ℕ
A 0        n        = succ n
A (succ m) 0        = A m 1
A (succ m) (succ n) = A m (A (succ m) n)

\end{code}

We want to show, because somebody asked [1], that such a function can
be defined by transfinite induction on ω². We will define a function B
of the same type as A that satisfies the same equations.

We assume function extensionality.

\begin{code}

open import UF.FunExt

module _ (fe : FunExt) where

\end{code}

We work with ordinals as defined in [3].

[3] https://homotopytypetheory.org/book/

\begin{code}

 open import Ordinals.Type
 open import Ordinals.Underlying
 open import Ordinals.Arithmetic fe
 open import Naturals.Order

\end{code}

But see also the following link, which is not used here, which works
with an encoding of ordinals similar to the von Neumann encoding
(check the references there).

\begin{code}

 import Iterative.index

\end{code}

Multiplication _×ₒ_ of ordinals is given by lexicographic order of the
cartesian product of the underlying types. In particular, the
underlying set of ω² is the following, by construction.

\begin{code}

 _ : ⟨ ω² ⟩ ＝ (ℕ × ℕ)
 _ = refl

\end{code}

Abbreviation for the underlying order of ω².

\begin{code}

 _<_ : ⟨ ω² ⟩ →  ⟨ ω² ⟩ → 𝓤₀ ̇
 s < t = s ≺⟨ ω² ⟩ t

\end{code}

Because this is the lexicographic order (with the right component as
the most significant one, which is what causes the swapping phenomenon
below), the following two properties hold.

\begin{code}

 increase-left : (m n : ℕ) → (m , n) < (succ m , n)
 increase-left m n = inr (refl , <-succ m)

 increases-right : (m n m' : ℕ) → (m , n) < (m' , succ n)
 increases-right m n m' = inl (<-succ n)

\end{code}

The following is the step function for the recursion.

\begin{code}

 σ : (s : ℕ × ℕ) → ((t : ℕ × ℕ) → t < s → ℕ) → ℕ
 σ (n      , 0)      f = succ n
 σ (0      , succ m) f = f (1 , m) I
  where
   I : (1 , m) < (0 , succ m)
   I = increases-right 1 m 0
 σ (succ n , succ m) f = f (f (n , succ m) II , m) III
  where
   II : (n , succ m) < (succ n , succ m)
   II = increase-left n (succ m)

   III : (f (n , succ m) II , m) < (succ n , succ m)
   III = increases-right (f (n , succ m) II) m (succ n)

\end{code}

Notice that σ is *not* recursively defined. We now define B by
transfinite induction on ω². Notice also the swapping of the
arguments.

\begin{code}

 B : ℕ → ℕ → ℕ
 B m n = Transfinite-recursion ω² σ (n , m)

\end{code}

Finally, we show that B satisfies the same equations as A. This
follows directly by the unfolding behaviour of transfinite recursion.

\begin{code}

 unfold : (m n : ℕ) → B m n ＝ σ (n , m) (λ (n' , m') _ → B m' n')
 unfold m n = Transfinite-recursion-behaviour fe ω² σ (n , m)

 Ackermann-equation₀ : (n : ℕ) → B 0 n ＝ succ n
 Ackermann-equation₀ n = unfold 0 n

 Ackermann-equation₁ : (m : ℕ) → B (succ m) 0 ＝ B m 1
 Ackermann-equation₁ m = unfold (succ m) 0

 Ackermann-equation₂ : (m n : ℕ) → B (succ m) (succ n) ＝ B m (B (succ m) n)
 Ackermann-equation₂ m n = unfold (succ m) (succ n)

\end{code}
