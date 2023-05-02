--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

---------------------------------------
This is a playground where i try things 
---------------------------------------

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan hiding (_+_)
open import Naturals.Addition
open import Notation.Order
open import Naturals.Order
open import UF.Base
--open import PathSequences.Base
--open import PathSequences.Concat

module PathSequences.BaseAlternative where

\end{code}

Pathsequences with a built-in length.

\begin{code}

data PathSeq {X : 𝓤 ̇ } : ℕ → X → X → 𝓤 ̇ where
  [] : {x : X} → PathSeq zero x x
  _∙▹_ : {n : ℕ}{x y z : X} → PathSeq n x y → y ＝ z → PathSeq (succ n) x z

syntax PathSeq n x y = x ≡[ n ] y

-- Convenience: to have a more practical and visible Path Sequence
-- termination
∎▹_ : {X : 𝓤 ̇ } {x y : X} → x ＝ y → x ≡[ 1 ] y
∎▹ p = [] ∙▹ p

length : {X : 𝓤 ̇ } {x y : X} {n : ℕ} → x ≡[ n ] y → ℕ
length {x = x} {.x} [] = 0
length {x = x} {y} (s ∙▹ p) = length s + 1

\end{code}

Convert to identity type and normalize.  The resulting
concatenation of identity types is normalized.

We then use the conversion to establish a criterion for equality,
which intentionally ignores the length parameter.

\begin{code}
≡-to-＝ : {X : 𝓤 ̇ } {x y : X} {n : ℕ}
        → x ≡[ n ] y → x ＝ y
≡-to-＝ [] = refl
≡-to-＝ (s ∙▹ p) = (≡-to-＝ s) ∙ p

syntax ≡-to-＝ s = [ s ↓]

-- Equality of path sequences. Very important: we ignore the lengths!
-- Two path-sequences are equal precisely when their resulting
-- identity types are.

record _＝ₛ_ {X : 𝓤 ̇ }{x y : X}{m n : ℕ}
            (s : x ≡[ m ] y) (t : x ≡[ n ] y) : 𝓤 ̇ where
  constructor ＝ₛ-in
  field
    ＝ₛ-out : (≡-to-＝ s) ＝ (≡-to-＝ t)
open _＝ₛ_


\end{code}

Operations
----------

1. Concatenation

Concatenation is defined in the usual way as it is for (dependent) vectors.

Since path sequences are dependent on the naturals, to prove
associativity relative to propositional equality will run into the
usual difficulties that `PathSeq (l + m + n) x y` and `PathSeq (l + (m + n)) x y`
are different, though isomorphic, types.

Associativity with respect to `＝ₛ` is not problematic, since that
kind of equality ignores the dependece on the natural numbers.

\begin{code}

_∙ₛ_ : {X : 𝓤 ̇ } {x y z : X} {m n : ℕ}
     → x ≡[ m ] y → y ≡[ n ] z → x ≡[ m + n ] z
s ∙ₛ [] = s
s ∙ₛ (t ∙▹ p) = (s ∙ₛ t) ∙▹ p

-- ∙ₛ-assoc : {X : 𝓤 ̇ } {x y z w : X} {l m n : ℕ}
--          → (s : x ≡[ l ] y) (t : y ≡[ m ] z) (u : z ≡[ n ] w)
--          → (s ∙ₛ t) ∙ₛ u ＝ s ∙ₛ (t ∙ₛ u) -- <-- Problem!
-- ∙ₛ-assoc s t u = ?

∙ₛ-assoc-＝ₛ : {X : 𝓤 ̇ } {x y z w : X} {l m n : ℕ}
            → (s : x ≡[ l ] y) (t : y ≡[ m ] z) (u : z ≡[ n ] w)
            → (s ∙ₛ t) ∙ₛ u ＝ₛ s ∙ₛ (t ∙ₛ u)
∙ₛ-assoc-＝ₛ s t [] = ＝ₛ-in refl
∙ₛ-assoc-＝ₛ s t (u ∙▹ p) = ＝ₛ-in (ap (_∙ p) (＝ₛ-out (∙ₛ-assoc-＝ₛ s t u)) )

_◃∙_ : {X : 𝓤 ̇ } {x y z : X}{n : ℕ}
     → x ＝ y → y ≡[ n ] z → x ≡[ 1 + n ] z
p ◃∙ s = ∎▹ p ∙ₛ s

\end{code}

2. Extraction

\begin{code}

point-from-end : {X : 𝓤 ̇ } {x y : X} {m : ℕ}
               → (n : ℕ) → n ≤ m → x ≡[ m ] y → X
point-from-end {y = y} zero _ _ = y
point-from-end (succ n) () []
point-from-end (succ n) l (s ∙▹ p) = point-from-end n l s

_ : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q : y ＝ z} 
  → point-from-end 0 _ (∎▹ p ∙▹ q) ＝ z
_ = refl

_ : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q : y ＝ z} 
  → point-from-end 1 _ (∎▹ p ∙▹ q) ＝ y
_ = refl

_ : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q : y ＝ z} 
  → point-from-end 2 _ (∎▹ p ∙▹ q) ＝ x
_ = refl

_ : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q : y ＝ z} (l : 𝟘)
  → point-from-end 3 l (∎▹ p ∙▹ q) ＝ z
_ = λ ()

-- something does not work here
point-from-start : {X : 𝓤 ̇ } {x y : X} {m : ℕ}
                 → (n : ℕ) → n ≤ m → x ≡[ m ] y → X
point-from-start {x = x} {y} zero ⋆ _ = x
point-from-start (succ n) () []
point-from-start (succ n) l ([] ∙▹ p) = lhs p
point-from-start (succ n) l (s ∙▹ q ∙▹ p) = point-from-start n l (s ∙▹ q)

\end{code}

Fixities

\begin{code}

infixl 80 _∙▹_
infixl 80 _∙ₛ_
infixl 90 ∎▹_
\end{code}
 
