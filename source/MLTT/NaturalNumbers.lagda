Natural numbers

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.NaturalNumbers where

open import MLTT.Universes
open import MLTT.Id
open import MLTT.Natural-Numbers-Type public

rec : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
rec x f 0 = x
rec x f (succ n) = f (rec x f n)

_^_ : {X : 𝓤 ̇ } → (X → X) → ℕ → (X → X)
(f ^ n) x = rec x f n

^-succ : {X : 𝓤 ̇ } → (f : X → X) (n : ℕ) (x : X)
        → (f ^ succ n) x ＝ (f ^ n) (f x)
^-succ f 0 x = refl
^-succ f (succ n) x = ap f (^-succ f n x)

ℕ-induction : {A : ℕ → 𝓤 ̇ } → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
ℕ-induction base step 0 = base
ℕ-induction base step (succ n) = step n (ℕ-induction base step n)

\end{code}
