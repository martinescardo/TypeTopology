```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.FunExt
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons

open import Thesis.Prelude

module Thesis.1-TernaryBoehmReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
  where
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

```agda
downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k ℤ+ k)
downMid   k = (k ℤ+ k) +pos 1
downRight k = (k ℤ+ k) +pos 2
```

Furthermore, Each brick on level `n` also has either one or two bricks "above"
it on level `δ-1` -- i.e. even-numbered brick `δ` has bricks `δ/2` and `δ/2-1`,
whereas odd-numbered brick `m` only has brick `δ/2`, above it.

```agda
upRight upLeft : ℤ → ℤ
upRight k = sign k (num k /2)
upLeft  k = upRight (predℤ k)
```

As shown above, the integer `a` is below `b` if `downLeft b ≤ a ≤ downRight b`.

```agda
_below_ : ℤ → ℤ → 𝓤₀ ̇
a below b = downLeft b ≤ a ≤ downRight b
```

The integer `a` is above `b` if `upLeft b ≤ a ≤ upRight b`.

```agda
_above_ : ℤ → ℤ → 𝓤₀ ̇
a above b = upLeft b ≤ a ≤ upLeft b
```

Of course, `a below b` implies `b above a`, and vice versa, though the proof is
tedious. It, along with other proofs about `below` and `above` and their
relationship to each other, are outsourced to the following file.

```agda
open import Thesis.BelowAndAbove
  hiding (downLeft ; downMid ; downRight ; upLeft ; upRight ; _below_ ; _above_)
```

## Formal definition of `𝕋`

We now define `𝕋` as functions where each "brick" on "precision-level" `n+1` is
below that on `n`.

```agda
𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , ((δ : ℤ) → x (succℤ δ) below x δ)

⟨_⟩ : 𝕋 → (ℤ → ℤ)
⟨ x , _ ⟩ = x
```

# Part II - Constructing Ternary Boehm Encodings

## Building elements of `𝕋`

We can build simple elements of `𝕋` that go 'via' a given interval encoding, and
use `upRight` and `downLeft` to construct all other precision-levels.

```agda
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
 →       build-via' (k , i) (succℤ δ) (ℤ-trich-succ δ i η)
   below build-via' (k , i) δ η
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

```agda
fromInt : ℤ → 𝕋
fromInt k = build-via (k , negsucc 0)
```

## Representing closed intervals

Given any specific brick on a specific level, i.e. `(k , δ) : ℤ × ℤ`
representing `⟪ k , δ ⟫`, we can define the type of real numbers in the closed
interval `⟪ k , δ ⟫`.

```agda
CompactInterval : ℤ × ℤ → 𝓤₀ ̇
CompactInterval (k , δ) = Σ (x , _) ꞉ 𝕋 , x(δ) ＝ k
```

Any encoding of a real in a compact interval is an encoding of a real, and any
encoding of a real is an encoding of a real in any compact interval it can be
approximated to.

```agda
ι : {i : ℤ × ℤ} → CompactInterval i → 𝕋
ι = pr₁

ρ : (x : 𝕋) (δ : ℤ) → CompactInterval (⟨ x ⟩ δ , δ)
ρ x δ = x , refl
```

We can easily build a trivial element of any closed interval using `build-via`.

```agda
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

```agda
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

It is the case that for all `α : 𝕋` and `i : ℤ`,
`⟦ α ⟧ ＝ ⟦ replace-right α i ⟧`.

What this means is that all information held at `x(δ)` about locating `⟦ x ⟧` is
also held at `x(δ+1)` -- once you consider a level, levels higher than that can
be trivially reconstructed.

# Part III - Recursive below/above and lower/upper bounds of compact intervals

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

```agda
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

```agda
ci-lower-upper-<' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ i +pos n ＝ δ
                  → rec k downLeft (succ n) ≤ ⟨ ι x ⟩ δ
                  ≤ rec k downRight (succ n) 
ci-lower-upper-<' (k , i) ((x , γx) , refl) δ 0        refl
 = γx i
ci-lower-upper-<' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _ (downLeft-monotone _ _ IHl) (pr₁ (γx (succℤ i ℤ+ pos n)))
 , ℤ≤-trans _ _ _ (pr₂ (γx (succℤ i +pos n))) (downRight-monotone _ _ IHr)
 where
   IH = ci-lower-upper-<' (x i , i) ((x , γx) , refl)
          (predℤ δ) n (predsuccℤ _ ⁻¹)
   IHl : rec (x i) downLeft (succ n) ≤ x (succℤ i ℤ+ pos n)
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
                 → rec k downLeft  (succ n)
                 ≤ ⟨ ι x ⟩ δ
                 ≤ rec k downRight (succ n) 
ci-lower-upper-< (k , i) x δ (n , i<δ) = ci-lower-upper-<' (k , i) x δ n i<δ

ci-lower-upper->' : ((k , i) : ℤ × ℤ) → (x : CompactInterval (k , i))
                  → (δ : ℤ)
                  → (n : ℕ) → succℤ δ +pos n ＝ i
                  → rec k upLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k upRight (succ n) 
ci-lower-upper->' (k , i) ((x , γx) , refl) δ 0        refl
 = below-implies-above _ _ (γx δ)
ci-lower-upper->' (k , i) ((x , γx) , refl) δ (succ n) refl
 = ℤ≤-trans _ _ _
     (upLeft-monotone _ _ IHl)
     (pr₁ (below-implies-above _ _ (γx δ)))
 , ℤ≤-trans _ _ _
     (pr₂ (below-implies-above _ _ (γx δ)))
     (upRight-monotone _ _ IHr)
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
                 → rec k upLeft (succ n) ≤ ⟨ ι x ⟩ δ ≤ rec k upRight (succ n) 
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

```agda
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

```agda
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

```agda
upLeft-or-upRight' : (k₁ k₂ c : ℤ) (n m : ℕ)
                   → k₁ +pos n ＝ c
                   → c +pos m ＝ k₂
                   → k₁ <ℤ k₂
                   → (upRight k₁ ≤ upLeft  c ≤ upLeft k₂)
                   + (upRight k₁ ≤ upRight c ≤ upLeft k₂)
upLeft-or-upRight' k₁ k₂ c 0 0        p q f
 = 𝟘-elim (ℤ-less-not-equal _ _ f (p ∙ q))
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
       (transport (upRight (downLeft k₁) ≤ upLeft c ≤_)
         (upLeft-downRight k₂) l)))
     (λ r → inr (transport (_≤ upRight c ≤ k₂) (upRight-downLeft k₁ ⁻¹)
       (transport (upRight (downLeft k₁) ≤ upRight c ≤_)
         (upLeft-downRight k₂) r)))

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
 = 𝟘-elim (ℤ-less-not-equal _ _ f refl) 
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

```agda
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

```agda
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

above-lower-upper = {!!} -- Similar proof method
```

## Replacement function

Given two interval encodings `(k , i), (c , δ) : ℤ × ℤ` where `c below/above k`,
then we can construct a real encoding `x : CompactInterval (k , i)` that "goes
via" `(c , δ) : ℤ × ℤ`.

```agda
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

```agda
replace : ((k , i) (c , δ) : ℤ × ℤ)
        → lower (k , i) δ ≤ c ≤ upper (k , i) δ
        → Σ ((x , _) , _) ꞉ CompactInterval (k , i) , x δ ＝ c
replace (k , i) (c , δ)
 = replace' (k , i) (c , δ) ∘ (lower/upper-implies-below/above (k , i) (c , δ))
```

Formalising the lemma `replace-below` is tedious (`replace-above` is a
consequence).

The work is shown below:

```agda
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
     = ((below-vec c k n b) !! n₂) (ℤ≤-progress i z j i≤j (n₁ , ε₁) (n₂ , ε₂))
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

Next, we define functions from the mathematical real space in
[`FunctionEncodings`](2-FunctionEncodings.lagda.md)

Then, we combine our work for the purpose of searchability in
[`TernaryBoehmRealsSearch`](3-TernaryBoehmRealsSearch.lagda.md).

