Tom de Jong, 3 - 5 March 2020

As suggested by Martin Escardo.

Dyadic rationals (https://en.wikipedia.org/wiki/Dyadic_rational)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DyadicsInductive.Dyadics where

open import MLTT.Spartan
open import MLTT.Unit-Properties
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

\end{code}

We inductively construct dyadic rationals in (-1,1), as follows.
Start with the point 0 in the middle (represented by middle below).
Define two functions (represented by left and right below):

l : (-1,1) → (-1,1)
l x = (x-1)/2

r : (-1,1) → (-1,1)
r x = (x+1)/2

Some values (ordered) to give an impression:

                   0                  -- just 0
        -1/2                1/2       -- l 0 = -1/2 and r 0 = 1/2
   -3/4      -1/4      1/4       3/4  -- l (l 0), l (r 0), r (l 0) and r (r 0)

In this module we just define the type and prove that it has decidable
equality. The order on 𝔻 is defined in the separate module Dyadic-Order.

\begin{code}

data 𝔻 : 𝓤₀ ̇ where
  middle : 𝔻
  left   : 𝔻 → 𝔻
  right  : 𝔻 → 𝔻

\end{code}

Using the well-known encode-decode method (cf. Section 2.13 of the HoTT book),
we can show that right and left are injective and that 𝔻 is discrete (i.e. it
has decidable equality).

By Hedberg's Theorem, 𝔻 is a set.

\begin{code}

middle-is-not-left : {x : 𝔻} → middle ≠ left x
middle-is-not-left p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f middle    = 𝟙
  f (left _)  = 𝟘
  f (right _) = 𝟘

middle-is-not-right : {x : 𝔻} → middle ≠ right x
middle-is-not-right p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f middle    = 𝟙
  f (left _)  = 𝟘
  f (right _) = 𝟘

left-is-not-right : {x y : 𝔻} → left x ≠ right y
left-is-not-right p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f middle    = 𝟙
  f (left x)  = 𝟙
  f (right x) = 𝟘

left-lc : {x y : 𝔻} → left x ＝ left y → x ＝ y
left-lc = ap f
 where
  f : 𝔻 → 𝔻
  f middle    = middle
  f (left x)  = x
  f (right x) = right x

right-lc : {x y : 𝔻} → right x ＝ right y → x ＝ y
right-lc = ap f
 where
  f : 𝔻 → 𝔻
  f middle    = middle
  f (left x)  = left x
  f (right x) = x

𝔻-is-discrete : is-discrete 𝔻
𝔻-is-discrete middle    middle    = inl refl
𝔻-is-discrete middle    (left y)  = inr middle-is-not-left
𝔻-is-discrete middle    (right y) = inr middle-is-not-right
𝔻-is-discrete (left x)  middle    = inr (λ p → middle-is-not-left (p ⁻¹))
𝔻-is-discrete (left x)  (left y)  = cases a b (𝔻-is-discrete x y)
 where
  a : x ＝ y → is-decidable (left x ＝ left y)
  a = inl ∘ ap left
  b : ¬ (x ＝ y) → is-decidable (left x ＝ left y)
  b = inr ∘ contrapositive left-lc
𝔻-is-discrete (left x)  (right y) = inr left-is-not-right
𝔻-is-discrete (right x) middle    = inr (λ p → middle-is-not-right (p ⁻¹))
𝔻-is-discrete (right x) (left y)  = inr (λ p → left-is-not-right (p ⁻¹))
𝔻-is-discrete (right x) (right y) = cases a b (𝔻-is-discrete x y)
 where
  a : x ＝ y → is-decidable (right x ＝ right y)
  a = inl ∘ ap right
  b : ¬ (x ＝ y) → is-decidable (right x ＝ right y)
  b = inr ∘ contrapositive right-lc

𝔻-is-set : is-set 𝔻
𝔻-is-set = discrete-types-are-sets 𝔻-is-discrete

\end{code}
