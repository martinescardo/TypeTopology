Martin Escardo, 2014, 21 March 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Fin  where

Fin : ℕ → 𝓤₀ ̇
Fin zero     = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

fzero : {n : ℕ} → Fin(succ n)
fzero = inr *

fsucc : {n : ℕ} → Fin n → Fin(succ n)
fsucc = inl

\end{code}

The left cancellability of Fin uses the non-trivial construction
+𝟙-cancellable defined in the module PlusOneLC.lagda.

\begin{code}

open import UF-FunExt

module _ (fe : FunExt) where

 open import PlusOneLC
 open import UF-Equiv

 Fin-lc : (m n : ℕ) → Fin m ≃ Fin n → m ≡ n
 Fin-lc zero zero p = refl
 Fin-lc (succ m) zero p = 𝟘-elim (⌜ p ⌝ fzero)
 Fin-lc zero (succ n) p = 𝟘-elim (⌜ ≃-sym p ⌝ fzero)
 Fin-lc (succ m) (succ n) p = ap succ r
  where
   IH : Fin m ≃ Fin n → m ≡ n
   IH = Fin-lc m n
   remark : Fin m + 𝟙 ≃ Fin n + 𝟙
   remark = p
   q : Fin m ≃ Fin n
   q = +𝟙-cancellable fe p
   r : m ≡ n
   r = IH q

open import DiscreteAndSeparated

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete zero     = 𝟘-is-discrete
Fin-is-discrete (succ n) = +discrete (Fin-is-discrete n) 𝟙-is-discrete

\end{code}
