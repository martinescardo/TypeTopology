Andrew Sneap, 26 November 2011
Updated 18 May 2022
        18 July 2022


This file defines Integers using existing natural numbers, the
successor and predecessor functions, induction on integers and the
canonical inclusion of natural numbers in the integers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.Unit-Properties
open import Naturals.Properties
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

module Integers.Type where

\end{code}

In order to avoid having positive and negative 0, a standard solution is to have
the negative constructor denote λ n → - (n + 1).

For example, negsucc 0 = -1, negsucc 4 = -5.

\begin{code}

data ℤ : 𝓤₀ ̇ where
 pos     : ℕ → ℤ
 negsucc : ℕ → ℤ

{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    pos     #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}

\end{code}

Now we have the predecessor and successor functions on integers.
By case analysis and reflexivity, these functions are inverses.

\begin{code}

predℤ : ℤ → ℤ
predℤ (pos 0)        = negsucc 0
predℤ (pos (succ x)) = pos x
predℤ (negsucc x)    = negsucc (succ x)

succℤ : ℤ → ℤ
succℤ (pos x)            = pos (succ x)
succℤ (negsucc 0)        = pos 0
succℤ (negsucc (succ x)) = negsucc x

succpredℤ : (x : ℤ) → succℤ (predℤ x) ＝ x
succpredℤ (pos 0)        = refl
succpredℤ (pos (succ x)) = refl
succpredℤ (negsucc x)    = refl

predsuccℤ : (x : ℤ) → predℤ (succℤ x) ＝ x
predsuccℤ (pos x)            = refl
predsuccℤ (negsucc 0)        = refl
predsuccℤ (negsucc (succ x)) = refl

\end{code}

We can construct proofs about integers by considering cases, or by a
standard induction principle.

\begin{code}

ℤ-cases : {A : ℤ → 𝓤 ̇ } → (x : ℤ)
                        → ((y : ℤ) → x ＝ succℤ y → A x)
                        → ((y : ℤ) → x ＝ predℤ y → A x)
                        → A x
ℤ-cases (pos x)     cₛ cₚ = cₚ (pos (succ x)) refl
ℤ-cases (negsucc x) cₛ cₚ = cₛ (negsucc (succ x)) refl

ℤ-induction : {A : ℤ → 𝓤 ̇ } → A (pos 0)
                            → ((k : ℤ) → A k → A (succℤ k))
                            → ((k : ℤ) → A (succℤ k) → A k)
                            → (x : ℤ)
                            → A x
ℤ-induction c₀ cₛ cₙ (pos 0)            = c₀
ℤ-induction c₀ cₛ cₙ (pos (succ x))     = cₛ (pos x) (ℤ-induction c₀ cₛ cₙ (pos x))
ℤ-induction c₀ cₛ cₙ (negsucc 0)        = cₙ (negsucc 0) c₀
ℤ-induction c₀ cₛ cₙ (negsucc (succ x)) = cₙ (negsucc (succ x)) (ℤ-induction c₀ cₛ cₙ (negsucc x))

ℤ-induction' : {A : ℤ → 𝓤 ̇ } → A (pos 0)
                            → ((k : ℤ) → A k → A (succℤ k))
                            → ((k : ℤ) → A k → A (predℤ k))
                            → (x : ℤ)
                            → A x
ℤ-induction' {𝓤} {A} c₀ cₛ cₙ =
 ℤ-induction c₀ cₛ (λ k k-holds → transport A (predsuccℤ k) (cₙ (succℤ k) k-holds))


\end{code}

By introducing the abs function which take integers to natural
numbers, we can prove that pos and negsucc are left-cancellable.

\begin{code}

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

pos-lc : {x y : ℕ} → pos x ＝ pos y → x ＝ y
pos-lc {x} {y} = ap abs

negsucc-lc : {x y : ℕ} → negsucc x ＝ negsucc y → x ＝ y
negsucc-lc {x} {y} p = succ-lc (ap abs p)

\end{code}

Now we can introduce five integer propositions , which are first used
to produce easy proofs of properties of integers, for example that
positive integers and never equal to negative integers.

\begin{code}

positive : ℤ → 𝓤₀ ̇
positive (pos x)     = 𝟙
positive (negsucc x) = 𝟘

negative : ℤ → 𝓤₀ ̇
negative (pos x)     = 𝟘
negative (negsucc x) = 𝟙

is-zero : ℤ → 𝓤₀ ̇
is-zero (pos 0)        = 𝟙
is-zero (pos (succ x)) = 𝟘
is-zero (negsucc x)    = 𝟘

not-zero : ℤ → 𝓤₀ ̇
not-zero z = ¬ (is-zero z)

is-pos-succ : ℤ → 𝓤₀ ̇
is-pos-succ (pos 0)        = 𝟘
is-pos-succ (pos (succ z)) = 𝟙
is-pos-succ (negsucc z)    = 𝟘

pos-not-negsucc : {x y : ℕ} → pos x ≠ negsucc y
pos-not-negsucc {x} p = 𝟙-is-not-𝟘 (ap positive p)

negsucc-not-pos : {x y : ℕ} → negsucc x ≠ pos y
negsucc-not-pos p = 𝟙-is-not-𝟘 (ap negative p)

pos-succ-not-zero : (x : ℕ) → pos (succ x) ≠ pos 0
pos-succ-not-zero x p = positive-not-zero x (pos-lc p)

negsucc-not-zero : (x : ℕ) → negsucc x ≠ pos 0
negsucc-not-zero x p = pos-not-negsucc (p ⁻¹)

succℤ-no-fp : (x : ℤ) → ¬ (x ＝ succℤ x)
succℤ-no-fp (pos x)            e = succ-no-fp x (pos-lc e)
succℤ-no-fp (negsucc 0)        e = negsucc-not-pos e
succℤ-no-fp (negsucc (succ x)) e = succ-no-fp x (negsucc-lc (e ⁻¹))

is-pos-succ-succℤ : (x : ℤ) → is-pos-succ x → is-pos-succ (succℤ x)
is-pos-succ-succℤ (pos 0)        g = 𝟘-elim g
is-pos-succ-succℤ (pos (succ x)) g = g
is-pos-succ-succℤ (negsucc x)    g = 𝟘-elim g

from-is-zero : (z : ℤ) → is-zero z → z ＝ pos 0
from-is-zero (negsucc x)    iz = 𝟘-elim iz
from-is-zero (pos 0)        iz = refl
from-is-zero (pos (succ m)) iz = 𝟘-elim iz

\end{code}

Some of the above properties can be used to prove that integers are
discrete, i.e that equality of integers is a proposition. When the
sign of the integers are equal, we simply check the equality of the
underlying natural number. Otherwise, two integers are not equal,
since positives are not negatives.

As a corollary, it follows that proofs of equality of two integers are
always equal.

\begin{code}

ℤ-is-discrete : is-discrete ℤ
ℤ-is-discrete (pos x) (pos y) = f (ℕ-is-discrete x y)
 where
  f : (x ＝ y) ∔ ¬ (x ＝ y) → is-decidable (pos x ＝ pos y)
  f (inl e)  = inl (ap pos e)
  f (inr ne) = inr (λ e → ne (pos-lc e))
ℤ-is-discrete (pos x) (negsucc y) = inr pos-not-negsucc
ℤ-is-discrete (negsucc x) (pos y) = inr negsucc-not-pos
ℤ-is-discrete (negsucc x) (negsucc y) = f (ℕ-is-discrete x y)
 where
  f : (x ＝ y) ∔ ¬ (x ＝ y) → is-decidable (negsucc x ＝ negsucc y)
  f (inl e)  = inl (ap negsucc e)
  f (inr ne) = inr (λ e → ne (negsucc-lc e))

ℤ-is-set : is-set ℤ
ℤ-is-set = discrete-types-are-sets ℤ-is-discrete

succℤ-lc : {x y : ℤ} → succℤ x ＝ succℤ y → x ＝ y
succℤ-lc {x} {y} p = x               ＝⟨ predsuccℤ x ⁻¹ ⟩
                     predℤ (succℤ x) ＝⟨ ap predℤ p     ⟩
                     predℤ (succℤ y) ＝⟨ predsuccℤ y    ⟩
                     y               ∎

predℤ-lc : {x y : ℤ} →  predℤ x ＝ predℤ y → x ＝ y
predℤ-lc {x} {y} p = x               ＝⟨ succpredℤ x ⁻¹ ⟩
                     succℤ (predℤ x) ＝⟨ ap succℤ p     ⟩
                     succℤ (predℤ y) ＝⟨ succpredℤ y    ⟩
                     y               ∎

\end{code}

We define here some shorthand notation for (pos ∘ succ) and negsucc.

\begin{code}

ps ns : ℕ → ℤ
ps = pos ∘ succ
ns = negsucc

\end{code}

There is a natural injection of natural numbers to integers by mapping
any natural number n to pos n. As with other canonical inclusions in
this development, ι is used.

\begin{code}

open import Notation.CanonicalMap

instance
 canonical-map-ℕ-to-ℤ : Canonical-Map ℕ ℤ
 ι {{canonical-map-ℕ-to-ℤ}} = λ x → pos x

\end{code}
