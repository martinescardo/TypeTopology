```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import MLTT.Spartan
open import Naturals.Order
open import DedekindReals.IntegersOrder
open import DedekindReals.IntegersB
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import DedekindReals.IntegersAddition renaming (_+_ to _+ℤ_)
open import Notation.Order
open import UF.PropTrunc
open import UF.Quotient

module Todd.TernaryBoehmReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
  where

open import Todd.TernaryBoehmRealsPrelude fe

_≤_≤_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
a ≤ b ≤ c = (a ≤ b) × (b ≤ c)

```

# Part I - Motivation and Definition

## Idea and Illustration

We encode real numbers using the data type for ternary Boehm reals `𝕋`.

Each `𝕋` is a function `x ꞉ ℤ → ℤ` with a condition that ensures we only have
our encodings of real numbers inside `𝕋`, and not just any function of type
`ℤ → ℤ`.

The idea is that a function `x : ℤ → ℤ` takes a "precision-level" `δ : ℤ` and
gives back an encoding `x(δ) : ℤ` of a real interval.

The idea is that each precision-level `δ : ℤ` represents a "layer" in the
following illustrative "brick pattern".

Level `δ+1` has bricks half the size of those on level `δ`. Here, segments of
levels `0` and `1` are shown.

```code
-1        0         1         2
__________ _________ _________ ____
|___-2____|____0____|____2____|____
 ____|___-1____|____1____|____3____|
 ____ ____ ____ ____ ____ ____ ____
|-4__|-2__|_0__|_2__|_4__|_6__|_8__|
 _|_-3_|_-1_|__1_|__3_|__5_|__7_|__
```

Then, `x(δ) : ℤ` refers to a precise labelled "brick" in the brick pattern.

Each brick encodes a real interval; specifically the interval `⟪ x(δ) , δ ⟫` as
defined below.

```code
⟪_⟫ : ℤ × ℤ → ℚ × ℚ
⟪ k , δ ⟫ = (k / 2^{δ + 1}) , ((k + 2) / 2^{δ + 1})
```

## Below and above

Therefore, an encoding of a real number is a sequence of encodings of real
intervals -- the condition we add is that each brick `x(δ)` is "below" the brick
-- `x(δ-1)`; meaning `⟪ x(δ+1) , δ+1 ⟫ ⊂ ⟪ x(δ) , δ ⟫`.

Each brick on level `δ` has exactly three bricks below it on level `δ+1` -- i.e.
brick `δ` has bricks `2δ`, `2δ+1` and `2δ+2` below it.

```
downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k +ℤ k)
downMid   k = (k +ℤ k) +pos 1
downRight k = (k +ℤ k) +pos 2
```

Furthermore, Each brick on level `n` also has either one or two bricks "above" it
on level `δ-1` -- i.e. even-numbered brick `δ` has bricks `δ/2` and `δ/2-1`,
whereas odd-numbered brick `m` only has brick `δ/2`, above it.

```
upRight upLeft : ℤ → ℤ
upRight k = sign k (num k /2)
upLeft  k = upRight (predℤ k)
```

As shown above, the integer `a` is below `b` if `downLeft b ≤ a ≤ downRight b`.

```
_below_ : ℤ → ℤ → 𝓤₀ ̇
a below b = downLeft b ≤ a ≤ downRight b
```

The integer `a` is above `b` if `upLeft b ≤ a ≤ upRight b`.

```
_above_ : ℤ → ℤ → 𝓤₀ ̇
a above b = upLeft b ≤ a ≤ upLeft b
```

Of course, `a below b` implies `b above a`, and vice versa, though the proof is
tedious. It, along with other proofs about `below` and `above` and their
relationship to each other, are outsourced to the following file.

```
open import Todd.BelowAndAbove fe
  hiding (downLeft ; downMid ; downRight ; upLeft ; upRight ; _below_ ; _above_)
```

## Formal definition of `𝕋`

We now define `𝕋` as functions where each "brick" on "precision-level" `n+1` is
below that on `n`.

```
𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , ((δ : ℤ) → x (succℤ δ) below x δ)

⟨_⟩ : 𝕋 → (ℤ → ℤ)
⟨ x , _ ⟩ = x
```

# Part II - Constructing Ternary Boehm Encodings

## Building elements of `𝕋`

We can build simple elements of `𝕋` that go 'via' a given interval encoding, and
use `upRight` and `downLeft` to construct all other precision-levels.

```
build-via' : ((k , i) : ℤ × ℤ) (δ : ℤ) → trich-locate δ i → ℤ
build-via' (k , i) δ (inl      (n , sδ+n＝i))
 = rec k upRight  (succ n)
build-via' (k , i) δ (inr (inl         δ＝i))
 = k
build-via' (k , i) δ (inr (inr (n , sδ+n＝δ)))
 = rec k downLeft (succ n)

build-via'-below
 : ((k , i) : ℤ × ℤ) (δ : ℤ)
 → (η : trich-locate δ i)
 → build-via' (k , i) (succℤ δ) (ℤ-trich-succ δ i η) below build-via' (k , i) δ η
build-via'-below (k , i) δ (inl (0           , sδ+n＝i))
 = above-implies-below _ _ (upRight-above k)
build-via'-below (k , i) δ (inl (succ n      , sδ+n＝i))
 = above-implies-below _ _ (upRight-above (rec k upRight (succ n)))
build-via'-below (k , i) δ (inr (inl              δ＝i))
 = downLeft-below k
build-via'-below (k , i) δ (inr (inr (n      , sδ+n＝i)))
 = downLeft-below (rec k downLeft (succ n))

build-via : ℤ × ℤ → 𝕋
build-via (k , i)
 = (λ n → build-via' (k , i) n (ℤ-trichotomous n i))
 , (λ n → transport (λ - → build-via' (k , i) (succℤ n) -
                           below
                           build-via' (k , i)        n (ℤ-trichotomous n i))
            (ℤ-trichotomous-is-prop (succℤ n) i
               (ℤ-trich-succ n i (ℤ-trichotomous n i))
               (ℤ-trichotomous (succℤ n) i))
            (build-via'-below (k , i) n (ℤ-trichotomous n i)))
```

Given that the lower bound of the interval encoded as `(k , -1) : ℤ × ℤ` is the
integer `k : ℤ` itself, we can build a representation of any integer like so.

```
κ : ℤ → 𝕋
κ k = build-via (k , negsucc 0)
```

## Representing closed intervals

Given any specific brick on a specific level, i.e. `(k , δ) : ℤ × ℤ` representing
`⟪ k , δ ⟫`, we can define the type of real numbers in the closed interval
`⟪ k , δ ⟫`.

```
CompactInterval : ℤ × ℤ → 𝓤₀ ̇
CompactInterval (k , δ) = Σ (x , _) ꞉ 𝕋 , x(δ) ＝ k
```

Any encoding of a real in a compact interval is an encoding of a real, and any
encoding of a real is an encoding of a real in any compact interval it can be
approximated to.

```
ι : {i : ℤ × ℤ} → CompactInterval i → 𝕋
ι = pr₁

ρ : (x : 𝕋) (δ : ℤ) → CompactInterval (⟨ x ⟩ δ , δ)
ρ x δ = x , refl
```

We can easily build a trivial element of any closed interval using `build-via`.

```
build-via'-correct : ((k , i) : ℤ × ℤ)
                   → (ζ : trich-locate i i)
                   → build-via' (k , i) i ζ ＝ k
build-via'-correct (k , i) ζ
 = ap (build-via' (k , i) i) (ℤ-trichotomous-is-prop i i ζ (inr (inl refl)))

build-via-ci : ((k , i) : ℤ × ℤ) → CompactInterval (k , i)
build-via-ci (k , i) = build-via (k , i)
                     , build-via'-correct (k , i) (ℤ-trichotomous i i)
```

## Replacement functions

Given any `x : 𝕋` and `i : ℤ`, we can replace all precision levels `δ < i` with
`(upRight ^ (i - δ)) (⟨ x ⟩ i)` (or `upLeft`) and still represent the same real
number.

```
replace-right' : (ℤ → ℤ) → (i : ℤ) → (δ : ℤ) → trich-locate δ i → ℤ
replace-right' x i δ (inl (n , δ+sn＝i)) = (upRight ^ succ n) (x i) 
replace-right' x i δ (inr         i≤δ ) = x δ

replace-right'-correct
 : (x : 𝕋) → (i : ℤ) → (δ : ℤ)
 → (η : trich-locate δ i)
 →       replace-right' ⟨ x ⟩ i (succℤ δ) (ℤ-trich-succ δ i η)
   below replace-right' ⟨ x ⟩ i δ η
replace-right'-correct (x , γx) i δ (inl (0      , refl))
 = above-implies-below _ _ (upRight-above _)
replace-right'-correct (x , γx) i δ (inl (succ n , refl))
 = above-implies-below _ _ (upRight-above _)
replace-right'-correct (x , γx) i δ (inr (inl _))
 = γx δ
replace-right'-correct (x , γx) i δ (inr (inr _))
 = γx δ

replace-right : 𝕋 → ℤ → 𝕋
replace-right x i
 = (λ δ → r δ (ℤ-trichotomous δ i))
 , (λ δ → transport (λ - → r (succℤ δ) - below r δ (ℤ-trichotomous δ i))
            (ℤ-trichotomous-is-prop (succℤ δ) i
              (ℤ-trich-succ δ i (ℤ-trichotomous δ i))
              (ℤ-trichotomous (succℤ δ) i))
            (replace-right'-correct x i δ (ℤ-trichotomous δ i))) 
 where r = replace-right' ⟨ x ⟩ i
```

It is the case that for all `α : 𝕋` and `i : ℤ`, `⟦ α ⟧ ＝ ⟦ replace-right α i ⟧`.

What this means is that all information held at `x(δ)` about locating `⟦ x ⟧` is
also held at `x(δ+1)` -- once you consider a level, levels higher than that can
be trivially reconstructed.

This will be further seen in the next section.

# Part III - Relationship between Ternary Boehm Encodings and Real Numbers

The real number represented by x : 𝕋 is defined as ⟦ x ⟧ : ℝ. Intuitively, ⟦ x ⟧
is the infinite intersection ⋂ᵢ ⟪ ⟨ x ⟩ i ⟫.

## Signed-digits are isomorphic to Ternary Boehm reals

Recall that we previously represented numbers in the closed interval `[-1,1]`
using signed-digit functions of type `ℕ → 𝟛`.

```code
⦉_⦊ : (ℕ → 𝟛) → ℝ
⦉ α ⦊ = Σᵢ (α i / 2^{i+1})
```

This interval is represented by the Boehm "brick" `(-1 , -1) : ℤ × ℤ`.

```
[−1,1]-code : ℤ × ℤ
[−1,1]-code = (negsucc 0 , negsucc 0)
```

The location structure of the signed-digit approach is actually
isomorphic to the ternary Boehm approach.

For example, the signed digit function

`α ≔     { −1            ,  O           , +1             , ...} : ℕ → 𝟛`

follows the same location structure as

`x ≔ {-1 , downLeft x(0) , downMid x(1) , downRight x(2) , ...} : ℕ → ℤ`

```
𝟛-to-down : 𝟛 → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

signed-to-boehm' : (ℕ → 𝟛) → (ℕ → ℤ)
signed-to-boehm' α 0 = negsucc 0
signed-to-boehm' α (succ n) = 𝟛-to-down (α n) (signed-to-boehm' α n)

𝟛-to-down-below : (t : 𝟛) (a : ℤ) → 𝟛-to-down t a below a
𝟛-to-down-below −1 a = downLeft-below  a
𝟛-to-down-below  O a = downMid-below   a
𝟛-to-down-below +1 a = downRight-below a

signed-to-boehm'-below
  : (α : ℕ → 𝟛) → (n : ℕ)
  → (signed-to-boehm' α (succ n)) below (signed-to-boehm' α n)
signed-to-boehm'-below α n = 𝟛-to-down-below (α n) (signed-to-boehm' α n)

signed-to-boehm : (ℕ → 𝟛) → CompactInterval [−1,1]-code
signed-to-boehm α
 = {!!}
```

Therefore, it should be the case that, for all `x : ℕ → 𝟛`,
`⦉ x ⦊ = ⟦ signed-to-boehm x ⟧`.

Recall that we used an interval object specification of the real numbers `𝕀`.

We already defined the following realisability map,

```code
q : 𝟛 → 𝕀
q −1 = −1
q  O =  O
q +1 = +1

𝕢 : (ℕ → 𝟛) → 𝕀
𝕢 = M ∘ map ⟨_⟩
```

We also want to define the realisability map `𝕣 : CompactInterval [−1,1]-code →
𝕀` such that for all `x : ℕ → 𝟛`, `𝕢 x = 𝕣 (signed-to-boehm x)`.

We will do this by defining, `boehm-to-signed : CompactInterval [−1,1]-code
→ (ℕ → 𝟛)` such that `boehm-to-signed ∘ signed-to-boehm ≃ id` and
`signed-to-boehm ∘ boehm-to-signed ≃ id`.

Then, by setting `𝕣 = 𝕢 ∘ boehm-to-signed`, we get that for all `x : ℕ → 𝟛`,
`𝕢 x = (𝕢 ∘ boehm-to-signed) (signed-to-boehm x)`.

## Using Dedekind reals instead

Myself and Andrew Sneap define `⟦ x ⟧`, and are developing a version of the above
relationship using Dedekind reals rather than the interval object.

## The key difference

The key difference between the signed digit approach and the Boehm approach is
that,
 * With signed digit, the information kept in `x(n)` *depends on*
                      the information in all `x(i)` such that `i < n`,
 * With Boehm codes,  the information kept in `x(n)` *includes*
                      the information in all `x(i)` such that `i < n`.

# Part IV - Recursive below/above and lower/upper bounds of compact intervals

## Lower and upper

At every precision level `n` of a ternary Boehm encoding `x` of an element of a
closed interval `⟪ k , i ⟫`, the brick `x(n)` lies in an interval of connected
integers with a lower and upper bound.

What we mean is that for all `(k , i) : ℤ × ℤ` and `n : ℤ`, there are some
integers `lower (k , i) n` and `upper (k , i) n` such that for all
`x : CompactInterval (x , i)`, `lower (k , i) n ≤ x n ≤ upper (k , i) n`.

At level `n < i`, the lower bound is `(downLeft  ^ (i − n)) k`
              and the upper bound is `(downRight ^ (i − n)) k`.
At level `n = i`, the lower and upper bounds are exactly `k`.
At level `n > i`, the lower bound is `(upLeft    ^ (i − n)) k`
              and the upper bound is `(upRight   ^ (i − n)) k`.

```
lower upper : ℤ × ℤ → ℤ → ℤ
lower (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n＝δ)  = rec k downLeft (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n＝i)) = rec k   upLeft (succ n)
upper (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n＝δ)  = rec k downRight (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n＝i)) = rec k   upRight (succ n)

lower≤upper : ((k , i) : ℤ × ℤ) (δ : ℤ) → lower (k , i) δ ≤ upper (k , i) δ
lower≤upper (k , i) δ with ℤ-trichotomous i δ
... | inl      i<δ   = downLeft≤downRight k (succ (pr₁ i<δ))
... | inr (inl refl) = ℤ≤-refl k
... | inr (inr i>δ)  = upLeft≤upRightⁿ    k (succ (pr₁ i>δ))
```

We now prove that these are in fact the lower and upper bounds.

```
ci-lower-upper-<' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ i +pos n ＝ δ
                  → rec k downLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k downRight (succ n) 
ci-lower-upper-<' (k , i) ((x , γx) , refl) δ 0        refl
 = γx i
ci-lower-upper-<' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _ (downLeft-monotone _ _ IHl) (pr₁ (γx (succℤ i +ℤ pos n)))
 , ℤ≤-trans _ _ _ (pr₂ (γx (succℤ i +pos n))) (downRight-monotone _ _ IHr)
 where
   IH = ci-lower-upper-<' (x i , i) ((x , γx) , refl)
          (predℤ δ) n (predsuccℤ _ ⁻¹)
   IHl : rec (x i) downLeft (succ n) ≤ x (succℤ i +ℤ pos n)
   IHl = transport (λ - → rec (x i) downLeft (succ n) ≤ x -)
          (predsuccℤ _)
          (pr₁ IH)
   IHr : x (succℤ i +pos n) ≤ rec (x i) downRight (succ n)
   IHr = transport (λ - → x - ≤ rec (x i) downRight (succ n))
           (predsuccℤ _)
           (pr₂ IH)

ci-lower-upper-< : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                 → (δ : ℤ)
                 → ((n , _) : i <ℤ δ)
                 → rec k downLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k downRight (succ n) 
ci-lower-upper-< (k , i) x δ (n , i<δ) = ci-lower-upper-<' (k , i) x δ n i<δ

ci-lower-upper->' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ δ +pos n ＝ i
                  → rec k upLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k upRight (succ n) 
ci-lower-upper->' (k , i) ((x , γx) , refl) δ 0        refl
 = below-implies-above _ _ (γx δ)
ci-lower-upper->' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _ (upLeft-monotone _ _ IHl) (pr₁ (below-implies-above _ _ (γx δ)))
 , ℤ≤-trans _ _ _ (pr₂ (below-implies-above _ _ (γx δ))) (upRight-monotone _ _ IHr)
 where
   IH = ci-lower-upper->' (x i , i) ((x , γx) , refl)
          (succℤ δ) n (ℤ-left-succ-pos (succℤ δ) n)
   IHl : rec (x i) upLeft (succ n) ≤ x (succℤ δ)
   IHl = pr₁ IH
   IHr : x (succℤ δ) ≤ rec (x i) upRight (succ n)
   IHr = pr₂ IH

ci-lower-upper-> : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                 → (δ : ℤ)
                 → ((n , _) : δ <ℤ i)
                 → rec k   upLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k   upRight (succ n) 
ci-lower-upper-> (k , i) x δ (n , δ<i) = ci-lower-upper->' (k , i) x δ n δ<i

ci-lower-upper : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
               → (δ : ℤ)
               → lower (k , i) δ ≤ ⟨ ι x ⟩ δ ≤ upper (k , i) δ 
ci-lower-upper (k , i) ((x , γx) , refl) δ with ℤ-trichotomous i δ
... | inl      i<δ   = ci-lower-upper-< (k , i) ((x , γx) , refl) δ i<δ
... | inr (inl refl) = (0 , refl) , (0 , refl)
... | inr (inr i>δ)  = ci-lower-upper-> (k , i) ((x , γx) , refl) δ i>δ
```

## Recursively below/above

We now define what it means for an integer to be recursively below (`belowⁿ`)
another integer.

```code
_belowⁿ_ : ℤ → ℤ → ℕ → 𝓤₀ ̇
(a belowⁿ b) 0        =           a below b
(a belowⁿ c) (succ n) = Σ b ꞉ ℤ , a below b × (b belowⁿ c) n
```

Recursively above (`aboveⁿ`) is defined similarly.

Note that most of the properties and proof techniques required for recursively
below and above are relegated to the file `BelowAndAbove.lagda.md`.

We define a property on interval encodings `(k , i) , (c , δ) : ℤ × ℤ`
called "recursively below or above" (`below/above`), which holds if either:
  * `i + n ＝ δ` and `(c belowⁿ k) n`,
  * `i ＝ δ` and `k ＝ c`,
  * `i ＝ δ + n` and `(c aboveⁿ k) n`.

```
_below/above_ : ℤ × ℤ → ℤ × ℤ → 𝓤₀ ̇
((c , δ) below/above (k , i)) with ℤ-trichotomous i δ
... | inl      (n , i<δ)  = (c belowⁿ k) n
... | inr (inl      i＝δ)  = k ＝ c
... | inr (inr (n , i>δ)) = (c aboveⁿ k) n
```

We will use this property, along with the previously defined lower/upper bounds
to construct encodings of reals in compact intervals that "go via" a specific
interval encodings.

## Relationship between below/above and lower/upper

An interval encoding `(c , δ) : ℤ × ℤ`, where `c` is between the lower and upper
bounds of the interval encoding `(k , i) : ℤ × ℤ` at precision-level `δ : ℤ` if
and only if `c` is either (1) below `k` if `i < δ`, (2) above `k` if `i > δ`, or
(3) equal to `k` if `i ＝ δ`.

First, we show that left implies right:

```
lower-upper-below : (k c : ℤ) (n : ℕ)
                  → rec k downLeft (succ n) ≤ c ≤ rec k downRight (succ n)
                  → (c belowⁿ k) n

lower-upper-above : (k c : ℤ) (n : ℕ)
                  → rec k upLeft   (succ n) ≤ c ≤ rec k upRight   (succ n)
                  → (c aboveⁿ k) n

lower/upper-implies-below/above : ((k , i) (c , δ) : ℤ × ℤ)
                                → lower (k , i) δ ≤ c ≤ upper (k , i) δ
                                → (c , δ) below/above (k , i)
lower/upper-implies-below/above (k , i) (c , δ) with ℤ-trichotomous i δ
... | inl (n , _)       = lower-upper-below k c n
... | inr (inl refl)    = ≤ℤ-antisym        k c  
... | inr (inr (n , _)) = lower-upper-above k c n
```

Formalising the lemmas `lower-upper-below` and `lower-upper-above` is tedious.
The work is shown below:

```
upLeft-or-upRight' : (k₁ k₂ c : ℤ) (n m : ℕ)
                   → k₁ +pos n ＝ c
                   → c +pos m ＝ k₂
                   → k₁ <ℤ k₂
                   → (upRight k₁ ≤ upLeft  c ≤ upLeft k₂)
                   + (upRight k₁ ≤ upRight c ≤ upLeft k₂)
upLeft-or-upRight' k₁ k₂ c 0 0        p q f
 = 𝟘-elim (b<a→a≢b _ _ f ((p ∙ q) ⁻¹))
upLeft-or-upRight'
 k₁ .((k₁ +pos zero) +pos succ m) .(k₁ +pos zero) 0 (succ m) refl refl f
 = inr (ℤ≤-refl _ , upRight≤upLeft _ _ (m , ℤ-left-succ-pos k₁ m))
upLeft-or-upRight'
 k₁ .((k₁ +pos succ n) +pos m) .(k₁ +pos succ n) (succ n) m refl refl f
 = inl (upRight≤upLeft _ _ (n , ℤ-left-succ-pos k₁ n)
     , upLeft-monotone _ _ (m , refl))

upLeft-or-upRight : (k₁ k₂ c : ℤ)
                  → k₁ ≤ k₂
                  → downLeft k₁ ≤         c ≤ downRight k₂
                  →         (k₁ ≤ upLeft  c ≤           k₂)
                  +         (k₁ ≤ upRight c ≤           k₂)
upLeft-or-upRight k₁ k₂ c k₁≤k₂ ((m₁ , η₁) , (m₂ , η₂))
 = Cases (upLeft-or-upRight' (downLeft k₁) (downRight k₂) c m₁ m₂ η₁ η₂
           (downLeft≤<downRight k₁ k₂ k₁≤k₂))
     (λ l → inl (transport (_≤ upLeft c ≤ k₂) (upRight-downLeft k₁ ⁻¹)
       (transport (upRight (downLeft k₁) ≤ upLeft c ≤_) (upLeft-downRight k₂) l)))
     (λ r → inr (transport (_≤ upRight c ≤ k₂) (upRight-downLeft k₁ ⁻¹)
       (transport (upRight (downLeft k₁) ≤ upRight c ≤_) (upLeft-downRight k₂) r)))

lower-upper-below k c 0 = id
lower-upper-below k c (succ n) l≤c≤u  
 = Cases (upLeft-or-upRight _ _ _ (downLeft≤downRight k (succ n)) l≤c≤u)
     (λ η → upLeft  c , above-implies-below _ _ (upLeft-above  c) , IH-l η)
     (λ η → upRight c , above-implies-below _ _ (upRight-above c) , IH-r η)
 where
   IH-l = lower-upper-below k (upLeft  c) n 
   IH-r = lower-upper-below k (upRight c) n

down-choices' : (k₁ k₂ c : ℤ) (n m : ℕ)
              → k₁ +pos n ＝ c
              → c +pos m ＝ k₂
              → k₁ <ℤ k₂
              → (downRight k₁ ≤ downLeft  c ≤ downLeft k₂)
              + (downRight k₁ ≤ downRight c ≤ downLeft k₂)
down-choices' k₁ .((k₁ +pos zero) +pos zero) .(k₁ +pos zero) 0 0 refl refl f
 = 𝟘-elim (b<a→a≢b _ _ f refl)
down-choices'
 k₁ .((k₁ +pos zero) +pos succ m) .(k₁ +pos zero) 0 (succ m) refl refl f
 = inr ((zero , refl)
       , transport (downRight k₁ ≤_) (downRight＝downLeft (k₁ +pos m))
           (downRight-monotone _ _ (m , refl)))
down-choices'
 k₁ .((k₁ +pos succ n) +pos m) .(k₁ +pos succ n) (succ n) m refl refl f
 = inl (transport (downRight k₁ ≤_) (downRight＝downLeft (k₁ +pos n))
          (downRight-monotone _ _ (n , refl))
      , downLeft-monotone _ _ (m , refl))

down-choices : (k₁ k₂ c : ℤ)
             → k₁ ≤ k₂
             → upLeft k₁ ≤           c ≤ upRight k₂
             →       (k₁ ≤ downLeft  c ≤ k₂)
             +       (k₁ ≤ downMid   c ≤ k₂)
             +       (k₁ ≤ downRight c ≤ k₂)
down-choices k₁ k₂ c k₁≤k₂ ((m₁ , η₁) , (m₂ , η₂)) with ℤ≤-split k₁ k₂ k₁≤k₂
... | inl k₁<k₂
 = Cases (down-choices' (upLeft k₁) (upRight k₂) c
           m₁ m₂ η₁ η₂ (upLeft-<< k₁ k₂ k₁<k₂))
     (λ l → inl         (apparently _ _ _ l))
     (λ r → (inr ∘ inr) (apparently _ _ _ r))
... | inr refl
 = Cases (below-implies-below' k₁ c
           (above-implies-below c k₁ ((m₁ , η₁) , (m₂ , η₂))))
     (inl ∘ l) (cases (inr ∘ inl ∘ m) (inr ∘ inr ∘ r))
 where
   l : k₁ ＝ downLeft  c → k₁ ≤ℤ downLeft  c ≤ℤ k₁ 
   l refl = ℤ≤²-refl (downLeft  c)
   m : k₁ ＝ downMid   c → k₁ ≤ℤ downMid   c ≤ℤ k₁
   m refl = ℤ≤²-refl (downMid   c)
   r : k₁ ＝ downRight c → k₁ ≤ℤ downRight c ≤ℤ k₁
   r refl = ℤ≤²-refl (downRight c)

lower-upper-above k c 0 = id
lower-upper-above k c (succ n) l≤c≤u
 = Cases (down-choices _ _ _ (upLeft≤upRightⁿ k (succ n)) l≤c≤u)
      (λ η → downLeft  c , below-implies-above _ _ (downLeft-below  c) , IH-l η)
     (cases
      (λ η → downMid   c , below-implies-above _ _ (downMid-below   c) , IH-m η)
      (λ η → downRight c , below-implies-above _ _ (downRight-below c) , IH-r η))
 where
   IH-l = lower-upper-above k (downLeft  c) n
   IH-m = lower-upper-above k (downMid   c) n
   IH-r = lower-upper-above k (downRight c) n
```

Next, we show that right implies left:

```
below-lower-upper : (k c : ℤ) (n : ℕ)
                  → (c belowⁿ k) n
                  → rec k downLeft (succ n) ≤ c ≤ rec k downRight (succ n)

equal-lower-upper : (k c : ℤ)
                  → k ＝ c
                  → k ≤ c ≤ k
equal-lower-upper k c refl = ℤ≤-refl k , ℤ≤-refl k

above-lower-upper : (k c : ℤ) (n : ℕ)
                  → (c aboveⁿ k) n
                  → rec k upLeft   (succ n) ≤ c ≤ rec k upRight   (succ n)

below/above-implies-lower/upper : ((k , i) (c , δ) : ℤ × ℤ)
                                → (c , δ) below/above (k , i)
                                → lower (k , i) δ ≤ c ≤ upper (k , i) δ
below/above-implies-lower/upper (k , i) (c , δ) with ℤ-trichotomous i δ
... | inl (n , _)       = below-lower-upper k c n
... | inr (inl refl)    = equal-lower-upper k c  
... | inr (inr (n , _)) = above-lower-upper k c n
```

Formalising the lemmas `below-lower-upper` and `above-lower-upper` is tedious.

The work is shown below:

```
below-lower-upper k c zero = id
below-lower-upper k c (succ n) (b , η , θ)
 = ℤ≤-trans _ _ _ (transport (_≤ rec k* downLeft (succ n))
                    (rec-f-＝ downLeft k (succ n))
                      (downLeftⁿ-monotone (downLeft k) k* n dLk≤k*))
                    (pr₁ IH₂)
 , ℤ≤-trans _ _ _ (pr₂ IH₂)
                  (transport (rec k* downRight (succ n) ≤_)
                    (rec-f-＝ downRight k (succ n))
                    (downRightⁿ-monotone k* (downRight k) n k*≤dRk))
 where
   k* = (below-vec c k (succ n) (b , η , θ) !! succ n) _
   bel : k* below k
   bel = transport (k* below_)
           (below-vec-!!sn c k (succ n) (b , η , θ) (<-succ (succ n)))
           (pairwise-below-vec c k (succ n) (b , η , θ) (succ n) _ _)
   dLk≤k* : downLeft k ≤ k*
   dLk≤k* = pr₁ (below-lower-upper k k* 0 bel)
   k*≤dRk : k* ≤ downRight k
   k*≤dRk = pr₂ (below-lower-upper k k* 0 bel)
   IH : rec k downLeft (succ n) ≤ b ≤ rec k downRight (succ n)
   IH = below-lower-upper k b n θ
   γ : (c belowⁿ k*) n
   γ = below-everything-in-vec c k (succ n) (b , η , θ) n
         (<-trans n (succ n) (succ (succ n)) (<-succ n) (<-succ (succ n)))
   IH₂ : rec k* downLeft (succ n) ≤ c ≤ rec k* downRight (succ n)
   IH₂ = below-lower-upper k* c n γ

above-lower-upper = {!!}
```

## Replacement function

Given two interval encodings `(k , i), (c , δ) : ℤ × ℤ` where `c below/above k`,
then we can construct a real encoding `x : CompactInterval (k , i)` that "goes
via" `(c , δ) : ℤ × ℤ`.

```
replace-below
         : ((k , i) (c , δ) : ℤ × ℤ)
         → ((n , _) : i < δ) → (c belowⁿ k) n
         → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c

replace-equal
         : ((k , i) (c , δ) : ℤ × ℤ)
         → (i ＝ δ) → (k ＝ c)
         → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c
replace-equal (k , i) (c , δ) refl refl = x , pr₂ x
 where x = build-via-ci (k , i)

replace-above
         : ((k , i) (c , δ) : ℤ × ℤ)
         → ((n , _) : δ < i) → (c aboveⁿ k) n
         → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c

replace' : ((k , i) (c , δ) : ℤ × ℤ)
         → (c , δ) below/above (k , i)
         → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c
replace' (k , i) (c , δ) with ℤ-trichotomous i δ
... | inl      i<δ  = replace-below (k , i) (c , δ) i<δ
... | inr (inl i＝δ) = replace-equal (k , i) (c , δ) i＝δ
... | inr (inr i>δ) = replace-above (k , i) (c , δ) i>δ
```

Using the relationship between lower/upper bounds and below/above we can further
determine that, given two interval encodings `(k , i), (c , δ) : ℤ × ℤ` where
`lower (k , i) δ ≤ c ≤ upper (k , i) δ`, then we can construct a real encoding
`x : CompactInterval (k , i)` that "goes via" `(c , δ) : ℤ × ℤ`. 

```
replace : ((k , i) (c , δ) : ℤ × ℤ)
        → lower (k , i) δ ≤ c ≤ upper (k , i) δ
        → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c
replace (k , i) (c , δ)
 = replace' (k , i) (c , δ) ∘ (lower/upper-implies-below/above (k , i) (c , δ))
```

Formalising the lemma `replace-below` is tedious (`replace-above` is a
consequence).

The work is shown below:

```
replace-below (k , i) (c , j) (n , i<j') b with build-via-ci (k , i)
... | ((x , u) , refl) = α
 where
  i<j = n , i<j'
  i≤j = <-is-≤ i j i<j
  vert-trich-ij         = λ z → ℤ-vert-trich-locate  z i j
  vert-trich-ij-succ    = λ z → ℤ-vert-trich-succ    z i j
  vert-trich-ij-all     = λ z → ℤ-vert-trich-all     z i j
  vert-trich-ij-is-prop = λ z → ℤ-vert-trich-is-prop z i j
  vert-trich-ij-i : vert-trich-ij i
  vert-trich-ij-i = inr (inl ((0 , refl) , i≤j))
  vert-trich-ij-j : vert-trich-ij j
  vert-trich-ij-j = inr (inl (i≤j , (0 , refl)))
  α = (((λ z → y  z (vert-trich-ij-all z))
    , (  λ z → γ* z (vert-trich-ij-all z) (vert-trich-ij-all (succℤ z))))
    , (ζ* (vert-trich-ij-all i)))
    , (θ* (vert-trich-ij-all j))
   where
    y : (z : ℤ) → vert-trich-ij z → ℤ
    y z (inl      _ )
     = x z
    y z (inr (inl ((n₁ , ε₁) , n₂ , ε₂)))
     = ((below-vec c k n b) !! n₂) (ye i z j i≤j (n₁ , ε₁) (n₂ , ε₂))
    y z (inr (inr (n , ε)))
     = rec c downLeft (succ n)
    γ : (z : ℤ) → (η : vert-trich-ij z)
      → y (succℤ z) (vert-trich-ij-succ z i<j η) below y z η
    γ z (inl (succ n , ε))
     = u z
    γ z (inl (0      , refl))
     = transport (_below x z) (below-vec-!!sn c k n b _ ⁻¹) (u z)
    γ z (inr (inl ((n₁ , ε₁) , succ n₂ , ε₂)))
     = pairwise-below-vec c k n b n₂ _ _
    γ z (inr (inl ((n₁ , ε₁) , zero , ε₂)))
     = transport (downLeft c below_)
         (below-vec-!!0 c k n b ⁻¹) (downLeft-below c)
    γ z (inr (inr (n , refl)))
     = downLeft-below (rec c downLeft (succ n))
    ζ : y i vert-trich-ij-i ＝ k
    ζ = below-vec-!!sn c k n b _
    θ : y j vert-trich-ij-j ＝ c
    θ = below-vec-!!0 c k n b
    θ* : (η : vert-trich-ij j) → y j η ＝ c
    θ* η = transport (λ - → y j - ＝ c)
             (vert-trich-ij-is-prop j i<j vert-trich-ij-j η) θ
    ζ* : (η : vert-trich-ij i) → y i η ＝ k
    ζ* η = transport (λ - → y i - ＝ k)
             (vert-trich-ij-is-prop i i<j vert-trich-ij-i η) ζ
    γ* : (z : ℤ) → (η : vert-trich-ij z) (η' : vert-trich-ij (succℤ z))
       → y (succℤ z) η' below y z η
    γ* z η η' = transport (λ - → y (succℤ z) - below y z η)
                  (vert-trich-ij-is-prop (succℤ z) i<j
                    (vert-trich-ij-succ z i<j η) η') (γ z η)

replace-above (k , i) (c , j) j<i b 
 = ((pr₁ (pr₁ γ)) , (pr₂ γ)) , (pr₂ (pr₁ γ))
 where
   γ = replace-below (c , j) (k , i) j<i (aboveⁿ-implies-belowⁿ k c (pr₁ j<i) b)
```

# Part V - Searching Ternary Boehm Encodings

## Searchable types

Recall that in our general regression framework, we define searchable types as
follows:

```agda
decidable-predicate : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
decidable-predicate {𝓤} {𝓥} X
 = Σ p ꞉ (X → Ω 𝓥) , ((x : X) → decidable (pr₁ (p x)))

searchable : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → 𝓤 ⊔ 𝓥 ⁺ ̇ 
searchable {𝓤} {𝓥} X
 = Π (p , _) ꞉ decidable-predicate {𝓤} {𝓥} X
 , Σ x₀ ꞉ X , (Σ (pr₁ ∘ p) → pr₁ (p x₀))
```

We often search only uniformly continuous predicates, which are defined by using
closeness functions and then quotienting the type up to a certain closeness
function.

## Closeness function on 𝕋

For every discrete-sequence type `ℕ → X` (where `X` is discrete), we have a
canonical closeness function `c : (ℕ → X) × (ℕ → X) → ℕ∞`.

Recall that for `x,y : ℕ → X` and any `δ : ℕ`,

`c (x , y) ≼ ι δ ⇔ (x ≈ y) δ`,

where `c(x , y) : ℕ∞` is the value of the discrete-sequence closeness function
for `x` and `y`.

```
_≈'_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈' β) n = (i : ℕ) → i < n → α n ＝ β n
```

From the canonical closeness function on `ℕ → ℤ`, we can define one on `𝕋`:

```code
c : 𝕋 × 𝕋 → ℕ∞
c ((α , _) , (β , _)) = c (α ∘ pos , β ∘ pos)
```

Note that we only take into account positive precision-levels of  `x : 𝕋`; but,
as we already said, for our purposes of encoding real numbers, the information
kept in any `⟨ x ⟩ (pos n₁) : ℤ` includes the information kept in any
`⟨ x ⟩ (negsucc n₂) : ℤ`.

This closeness function, like that on signed-digits, gives the closeness of
*encodings* of real numbers; not the real numbers themselves.

## Predicates we wish to search

The above closeness function will give us a way to search uniformly continuous
decidable predicates on `𝕋`. These are those decidable predicates that can be
decided by only examining a finite portion of the location information held in
`𝕋`. We call the point `δ : ℤ` that we need to examine up to the "modulus of
continuity" of the predicate.

We could use the isomorphism between `𝕋` and `ℕ → 𝟛` to immediately give us a
searcher on such unifoormly continuous predicates using the below properties:

```agda
decidable-predicate⌜_,_⌝⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓤} {𝓦} X
                         → decidable-predicate {𝓥} {𝓦} Y
decidable-predicate⌜ e , (p , d) ⌝⁻¹ = (p ∘ ⌜ e ⌝⁻¹) , (d ∘ ⌜ e ⌝⁻¹)

decidable-predicate⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                         → decidable-predicate {𝓥} {𝓦} Y
                         → decidable-predicate {𝓤} {𝓦} X
decidable-predicate⌜ e , (p , d) ⌝ = (p ∘ ⌜ e ⌝) , (d ∘ ⌜ e ⌝)

decidable-predicate⌜_,_⌝-correct
  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (e : X ≃ Y)
  → ((p , d) : decidable-predicate {𝓥} {𝓦} Y)
  → (y : Y) → pr₁ (p y)
  → pr₁ (pr₁ (decidable-predicate⌜ e , (p , d) ⌝) (⌜ e ⌝⁻¹ y))
decidable-predicate⌜ e , (p , d) ⌝-correct y
 = transport (λ - → pr₁ (p -)) (≃-sym-is-rinv e _ ⁻¹)
              
searchable⌜_,_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y
                → searchable {𝓤} {𝓦} X
                → searchable {𝓥} {𝓦} Y
searchable⌜ e , 𝓔 ⌝ (p , d)
 = ⌜ e ⌝ (pr₁ p')
 , λ (y₀ , py₀) → pr₂ p' ((⌜ e ⌝⁻¹ y₀)
                , decidable-predicate⌜ e , (p , d) ⌝-correct y₀ py₀)
 where p' = 𝓔 (decidable-predicate⌜ e , (p , d) ⌝)
```

However, the searcher given by this isomorphism (like that on signed-digits)
would search the *entire* prefix of the stream from point `pos 0` to point
`pos δ`; despite the fact that the location information at `pos δ` *includes*
all of the location information previous to that.

Therefore, we prefer to use a different isomorphism: the one induced by the
`replace` function in Section IV.

## Searching quotiented encodings of compact intervals

First, we define the equivalence relation needed to determine uniformly
continuous decidable predicates on Ternary Boehm encodings of any compact
interval `⟪ k , i ⟫`.

This equivalence relation simply takes a modulus of continuity `δ : ℤ` and asks
if `⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ` given `x,y : CompactInterval (k , i)`.

```
open set-quotients-exist sq

CompEqRel : (δ : ℤ) ((k , i) : ℤ × ℤ) → EqRel {𝓤₀} {𝓤₀} (CompactInterval (k , i))
CompEqRel δ (k , i) = _≣≣_ , u , r , s , t
 where
   _≣≣_ : CompactInterval (k , i) → CompactInterval (k , i) → 𝓤₀ ̇ 
   (x ≣≣ y) = ⟨ ι x ⟩ δ ＝ ⟨ ι y ⟩ δ
   u : is-prop-valued _≣≣_
   u x y = ℤ-is-set
   r : reflexive _≣≣_
   r x = refl
   s : symmetric _≣≣_
   s x y = _⁻¹
   t : transitive _≣≣_
   t x y z = _∙_
```

Seen as we only need to look at level `δ : ℤ`, we can isolate the bricks on that
level into the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`.

Indeed, the quotient type `CompactInterval (k , i) / CompEqRel δ (k , i)` is
*equivalent* to the type `ℤ[ lower (k , i) δ , upper (k , i) δ ]`

```
Conv→ : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → CompactInterval (k , i) → ℤ[ lower (k , i) δ , upper (k , i) δ ]
Conv→ δ (k , i) x = ⟨ ι x ⟩ δ , ci-lower-upper (k , i) x δ

Conv← : (δ : ℤ) → ((k , i) : ℤ × ℤ)
      → ℤ[ lower (k , i) δ , upper (k , i) δ ] → CompactInterval (k , i)
Conv← δ (k , i) (z , l≤z≤u) = pr₁ (replace (k , i) (z , δ) l≤z≤u)

CompReplace : (δ : ℤ) ((k , i) : ℤ × ℤ)
            → (x : CompactInterval (k , i))
            → x ≈[ CompEqRel δ (k , i) ] (Conv← δ (k , i) ∘ Conv→ δ (k , i)) x
CompReplace δ (k , i) x = pr₂ (replace (k , i) (z , δ) l≤z≤u) ⁻¹
 where
   γ     = Conv→ δ (k , i) x
   z     = pr₁ γ
   l≤z≤u = pr₂ γ

Conv→-identifies-related-points
  : (δ : ℤ) → ((k , i) : ℤ × ℤ)
  → identifies-related-points {𝓤₀} {𝓤₀} {𝓤₀} {CompactInterval (k , i)}
      (CompEqRel δ (k , i)) (Conv→ δ (k , i))
Conv→-identifies-related-points δ (k , i)
 = to-subtype-＝ {𝓤₀} {𝓤₀} {ℤ} {λ z → lower (k , i) δ ≤ℤ z ≤ℤ upper (k , i) δ}
     (λ z → ≤ℤ²-is-prop {lower (k , i) δ} {upper (k , i) δ} z)

ℤ[_,_]-is-set : (a b : ℤ) → is-set (ℤ[ a , b ])
ℤ[ a , b ]-is-set = subsets-of-sets-are-sets ℤ (λ z → a ≤ℤ z ≤ℤ b)
                      ℤ-is-set (≤ℤ²-is-prop _)

med-map/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → is-set A
         → (f : CompactInterval (k , i) → A)
         → identifies-related-points (CompEqRel δ (k , i)) f
         → CompactInterval (k , i) / CompEqRel δ (k , i) → A
med-map/ δ (k , i) s = mediating-map/ (CompEqRel δ (k , i)) s

uni-tri/ : {A : 𝓤 ̇ } (δ : ℤ) ((k , i) : ℤ × ℤ)
         → (s : is-set A)
         → (f : CompactInterval (k , i) → A)
         → (p : identifies-related-points (CompEqRel δ (k , i)) f)
         → med-map/ δ (k , i) s f p ∘ η/ (CompEqRel δ (k , i)) ∼ f
uni-tri/ δ (k , i) s f p = universality-triangle/ (CompEqRel δ (k , i)) s f p

med-map : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → CompactInterval (k , i) / CompEqRel δ (k , i)
        → ℤ[ lower (k , i) δ , upper (k , i) δ ]
med-map δ (k , i) = med-map/ δ (k , i)
                      (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set)
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)

uni-tri : (δ : ℤ) ((k , i) : ℤ × ℤ)
        → (med-map δ (k , i) ∘ η/ (CompEqRel δ (k , i))) ∼ Conv→ δ (k , i)
uni-tri δ (k , i) = uni-tri/ δ (k , i)
                      (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-is-set)
                      (Conv→ δ (k , i))
                      (to-subtype-＝ ≤ℤ²-is-prop)
           
compact-equiv : (δ : ℤ) ((k , i) : ℤ × ℤ)
              → CompactInterval (k , i) / CompEqRel δ (k , i)
              ≃ ℤ[ lower (k , i) δ , upper (k , i) δ ]
compact-equiv δ (k , i) = f' , ((g' , fg) , (g' , gf))
 where
  f' : CompactInterval (k , i) / CompEqRel δ (k , i)
     → ℤ[ lower (k , i) δ , upper (k , i) δ ]
  f' = med-map δ (k , i)
  g' : ℤ[ lower (k , i) δ , upper (k , i) δ ]
     → CompactInterval (k , i) / CompEqRel δ (k , i)
  g' = η/ (CompEqRel δ (k , i)) ∘ Conv← δ (k , i)
  fg : f' ∘ g' ∼ id
  fg (z , l≤z≤u)
   = uni-tri δ (k , i) (Conv← δ (k , i) (z , l≤z≤u))
   ∙ to-subtype-＝ ≤ℤ²-is-prop (pr₂ (replace (k , i) (z , δ) l≤z≤u)) 
  gf : g' ∘ f' ∼ id
  gf = /-induction (CompEqRel δ (k , i)) (λ _ → /-is-set (CompEqRel δ (k , i)))
         (λ y → η/-identifies-related-points (CompEqRel δ (k , i))
           (ap (λ - → ⟨ ι (Conv← δ (k , i) -) ⟩ δ)
             (uni-tri δ (k , i) y)
           ∙ CompReplace δ (k , i) y ⁻¹))
```

This gives us a much more efficient searcher for Ternary Boehm reals in compact
intervals, because the searcher on finite subsets of `ℤ` does not need to check
every element of the `𝕋` sequence.

```
ℤ[_,_]-searchable' : (l u : ℤ) → (n : ℕ) → l +pos n ＝ u
                  → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , l ]-searchable' 0 refl (p , d)
 = ((l , ℤ≤-refl l , ℤ≤-refl l))
 , λ ((z , l≤z≤u) , pz)
   → transport (pr₁ ∘ p) (to-subtype-＝ ≤ℤ²-is-prop ((≤ℤ-antisym l z l≤z≤u) ⁻¹)) pz
ℤ[ l , .(succℤ (l +pos n)) ]-searchable' (succ n) refl (p , d)
 = Cases (d u*) (λ pu → u* , (λ _ → pu))
    (λ ¬pu → ans ,
      (λ ((z , l≤z , z≤u) , pz)
        → Cases (ℤ≤-split z u z≤u)
            (λ z<u → sol ((z , l≤z
                   , transport (z ≤_) (predsuccℤ _) (≤ℤ-back z u z<u))
                   , transport (pr₁ ∘ p) (to-subtype-＝ ≤ℤ²-is-prop refl) pz))
            (λ z＝u → 𝟘-elim (¬pu (transport (pr₁ ∘ p)
                                   (to-subtype-＝ ≤ℤ²-is-prop z＝u) pz)))))
 where
   u = succℤ (l +pos n)
   u* = u , (succ n , refl) , ℤ≤-refl u
   γ : ℤ[ l , l +pos n ] → ℤ[ l , u ]
   γ = ℤ[ l , l +pos n ]-succ
   IH = ℤ[ l , l +pos n ]-searchable' n refl ((p ∘ γ) , (d ∘ γ))
   ans = γ (pr₁ IH)
   sol = pr₂ IH

ℤ[_,_]-searchable : (l u : ℤ) → l ≤ u → searchable {𝓤₀} {𝓦} (ℤ[ l , u ])
ℤ[ l , u ]-searchable (n , p) = ℤ[ l , u ]-searchable' n p

𝕋-compact-searchable
  : ((k , i) : ℤ × ℤ) (δ : ℤ)
  → searchable {𝓤₀} {𝓦} (CompactInterval (k , i) / CompEqRel δ (k , i))
𝕋-compact-searchable (k , i) δ
 = searchable⌜ (≃-sym (compact-equiv δ (k , i)))
 , (ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ]-searchable
     (lower≤upper (k , i) δ)) ⌝
```
