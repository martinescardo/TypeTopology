Martin Escardo, sometime between 2014 and 2021

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Properties where

open import UF.Subsingletons

open import Factorial.PlusOneLC
open import Fin.Type
open import MLTT.Spartan
open import MLTT.Unit-Properties
open import UF.Equiv

\end{code}

The largest element of Fin (succ n) is ⟪ n ⟫ (TODO: formulate and prove this).

\begin{code}

⟪_⟫ : (n : ℕ) → Fin (succ n)
⟪ 0 ⟫      = fzero
⟪ succ n ⟫ = fsucc ⟪ n ⟫

Fin0-is-empty : is-empty (Fin 0)
Fin0-is-empty i = i

Fin1-is-singleton : is-singleton (Fin 1)
Fin1-is-singleton = 𝟎 , γ
 where
  γ : (i : Fin 1) → 𝟎 ＝ i
  γ 𝟎       = refl
  γ (suc x) = 𝟘-elim x

Fin0-is-prop : is-prop (Fin 0)
Fin0-is-prop i = 𝟘-elim i

Fin1-is-prop : is-prop (Fin 1)
Fin1-is-prop 𝟎       𝟎       = refl
Fin1-is-prop 𝟎       (suc x) = 𝟘-elim x
Fin1-is-prop (suc x) y       = 𝟘-elim x

positive-not-𝟎 : {n : ℕ} {x : Fin n} → fsucc x ≠ 𝟎
positive-not-𝟎 {0}      {x} p = 𝟘-elim x
positive-not-𝟎 {succ n} {x} p = 𝟙-is-not-𝟘 (g p)
 where
  f : Fin (succ (succ n)) → 𝓤₀ ̇
  f 𝟎       = 𝟘
  f (suc x) = 𝟙

  g : suc x ＝ 𝟎 → 𝟙 ＝ 𝟘
  g = ap f

when-Fin-is-prop : (n : ℕ) → is-prop (Fin n) → (n ＝ 0) + (n ＝ 1)
when-Fin-is-prop 0               i = inl refl
when-Fin-is-prop 1               i = inr refl
when-Fin-is-prop (succ (succ n)) i = 𝟘-elim (positive-not-𝟎 (i 𝟏 𝟎))

when-Fin-is-singleton : (n : ℕ) → is-singleton (Fin n) → n ＝ 1
when-Fin-is-singleton 0               (x , c)     = 𝟘-elim x
when-Fin-is-singleton (succ 0)        _           = refl
when-Fin-is-singleton (succ (succ n)) (𝟎 , c)     =
 𝟘-elim (positive-not-𝟎 ((c 𝟏)⁻¹))
when-Fin-is-singleton (succ (succ n)) (suc k , c) =
 𝟘-elim (positive-not-𝟎 (c 𝟎))

\end{code}

The left cancellability of Fin uses the construction +𝟙-cancellable
defined in the module PlusOneLC.lagda.

\begin{code}

Fin-lc : (m n : ℕ) → Fin m ≃ Fin n → m ＝ n
Fin-lc 0           0       p = refl
Fin-lc (succ m)    0       p = 𝟘-elim (⌜ p ⌝ 𝟎)
Fin-lc 0          (succ n) p = 𝟘-elim (⌜ p ⌝⁻¹ 𝟎)
Fin-lc (succ m)   (succ n) p = ap succ r
 where
  IH : Fin m ≃ Fin n → m ＝ n
  IH = Fin-lc m n

  remark : Fin m + 𝟙 ≃ Fin n + 𝟙
  remark = p

  q : Fin m ≃ Fin n
  q = +𝟙-cancellable p

  r : m ＝ n
  r = IH q

\end{code}

Notice that Fin is an example of a map that is left-cancellable but
not an embedding in the sense of univalent mathematics.
