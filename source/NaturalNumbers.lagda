Natural numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module NaturalNumbers where

open import Universes
open import Natural-Numbers-Type public

rec : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)

_^_ : {X : 𝓤 ̇ } → (X → X) → ℕ → (X → X)
(f ^ n) x = rec x f n

induction : {A : ℕ → 𝓤 ̇ } → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
induction base step 0 = base
induction base step (succ n) = step n (induction base step n)

\end{code}
