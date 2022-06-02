```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import SpartanMLTT
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import IntegersOrder
open import IntegersB
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersNegation renaming (-_  to  −ℤ_)
open import UF-Subsingletons
open import NaturalsOrder
open import DecidableAndDetachable
open import OrderNotation

module Todd.TernaryBoehmReals (fe : FunExt) (pe : PropExt) where

open import Todd.SearchableTypes fe pe
open import Todd.TernaryBoehmRealsPrelude fe

_≤_≤_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
a ≤ b ≤ c = (a ≤ b) × (b ≤ c)

```

## Idea and Illustration

We encode real numbers using the data type for ternary Boehm reals 𝕋.

Each 𝕋 is a function x ꞉ ℤ → ℤ with a condition that ensures we only have
our encodings of real numbers inside 𝕋, and not just any function of type ℤ → ℤ.

The idea is that a function x : ℤ → ℤ takes a "precision-level" δ : ℤ and gives
back an encoding x(δ) : ℤ of a real interval.

The idea is that each precision-level δ : ℤ represents a "layer" in the
following illustrative "brick pattern".

Level δ+1 has bricks half the size of those on level δ.
Here, segments of levels 0 and 1 are shown.

-1        0         1         2
__________ _________ _________ ____
|___-2____|____0____|____2____|____
 ____|___-1____|____1____|____3____|
 ____ ____ ____ ____ ____ ____ ____
|-4__|-2__|_0__|_2__|_4__|_6__|_8__|
 _|_-3_|_-1_|__1_|__3_|__5_|__7_|__

Then, x(δ) : ℤ refers to a precise labelled "brick" in the brick pattern.

Each brick encodes a real interval; specifically the interval ⟪ x(δ) , δ ⟫ as
defined below.

⟪_⟫ : ℤ × ℤ → ℚ × ℚ
⟪ k , δ ⟫ = (k / 2^{δ - 1}) , ((k + 2) / 2^{δ - 1})

## Below and above

Therefore, an encoding of a real number is a sequence of encodings of real
intervals -- the condition we add is that each brick x(δ) is "below" the brick
-- x(δ−1); meaning ⟪ x(δ+1) , δ+1 ⟫ ⊂ ⟪ x(δ) , δ ⟫.

Each brick on level δ has exactly three bricks below it on level δ+1 --
i.e. brick δ has bricks 2δ, 2δ+1 and 2δ+2 below it.

```
downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k +ℤ k)
downMid   k = (k +ℤ k) +pos 1
downRight k = (k +ℤ k) +pos 2
```

Furthermore, Each brick on level n also has either one or two bricks "above" it
on level δ−1 -- i.e. even-numbered brick δ has bricks δ/2 and δ/2−1, whereas
odd-numbered brick m only has brick δ/2, above it.

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

## Formal definition of 𝕋

We now define 𝕋 as functions where each "brick" on "precision-level" n+1 is
below that on n.

```
𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , ((δ : ℤ) → x (succℤ δ) below x δ)

⟨_⟩ : 𝕋 → (ℤ → ℤ)
⟨ x , _ ⟩ = x
```

The real number represented by x : 𝕋 is defined as ⟦ x ⟧ : ℝ. Intuitively, ⟦ x ⟧
is the infinite intersection ⋂ᵢ ⟪ ⟨ x ⟩ i ⟫. Specifically, Andrew Sneap and I
define ⟦ x ⟧ using the Dedekind Reals.

open import TBRDedekindReals

## Replacement functions

Given any x : 𝕋 and i : ℤ, we can replace all precision levels δ <ℤ i
with (upRight ^ (i - δ)) (⟨ x ⟩ i) (or upLeft) and still represent the same
real number.

```
replace-right' : (ℤ → ℤ) → (i : ℤ) → (δ : ℤ) → trich-locate δ i → ℤ
replace-right' x i δ (inl (n , δ+sn≡i)) = (upRight ^ succ n) (x i) 
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

It is the case that for all α : 𝕋 and i : ℤ, ⟦ α ⟧ ≡ ⟦ replace-right α i ⟧.

What this means is that all information held at x(δ) about locating ⟦ x ⟧ is
also held at x(δ+1) -- once you consider a level, levels higher than that can be
trivially reconstructed.

Using a similar method, we can also build elements of 𝕋 that go 'via' one given
interval encoding, and use `upRight` and `downLeft` to construct all other
precision-levels.

```
build-via' : ((k , i) : ℤ × ℤ) (δ : ℤ) → trich-locate δ i → ℤ
build-via' (k , i) δ (inl      (n , sδ+n≡i))
 = rec k upRight  (succ n)
build-via' (k , i) δ (inr (inl         δ≡i))
 = k
build-via' (k , i) δ (inr (inr (n , sδ+n≡δ)))
 = rec k downLeft (succ n)

build-via'-below
 : ((k , i) : ℤ × ℤ) (δ : ℤ)
 → (η : trich-locate δ i)
 → build-via' (k , i) (succℤ δ) (ℤ-trich-succ δ i η) below build-via' (k , i) δ η
build-via'-below (k , i) δ (inl (0           , sδ+n≡i))
 = above-implies-below _ _ (upRight-above k)
build-via'-below (k , i) δ (inl (succ n      , sδ+n≡i))
 = above-implies-below _ _ (upRight-above (rec k upRight (succ n)))
build-via'-below (k , i) δ (inr (inl              δ≡i))
 = downLeft-below k
build-via'-below (k , i) δ (inr (inr (n      , sδ+n≡i)))
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

## Representing closed intervals

Given any specific brick on a specific level, i.e. (k , δ) : ℤ × ℤ representing
⟪ k , δ ⟫, we can define the type of real numbers in the closed interval
⟪ k , δ ⟫.

```
CompactInterval : ℤ × ℤ → 𝓤₀ ̇
CompactInterval (k , δ) = Σ (x , _) ꞉ 𝕋 , x(δ) ≡ k
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
                   → build-via' (k , i) i ζ ≡ k
build-via'-correct (k , i) ζ
 = ap (build-via' (k , i) i) (ℤ-trichotomous-is-prop i i ζ (inr (inl refl)))

build-via-ci : ((k , i) : ℤ × ℤ) → CompactInterval (k , i)
build-via-ci (k , i) = build-via (k , i)
                     , build-via'-correct (k , i) (ℤ-trichotomous i i)
```

## Lower and upper

At every precision level `n` of a ternary Boehm encoding `x` of an element of a
closed interval `⟪ k , i ⟫`, the brick `x(n)` lies in an interval of connected
integers with a lower and upper bound.

What we mean is that for all `(k , i) : ℤ × ℤ` and `n : ℤ`, there are some
integers `lower (k , i) n` and `upper (k , i) n` such that for all
`x : CompactInterval (x , i)`, `lower (k , i) n ≤ x n ≤ upper (k , i) n`.

At level n < i, the lower bound is (downLeft  ^ (i − n)) k
            and the upper bound is (downRight ^ (i − n)) k.
At level n = i, the lower and upper bounds are exactly k.
At level n > i, the lower bound is (upLeft    ^ (i − n)) k
            and the upper bound is (upRight   ^ (i − n)) k.

```
lower upper : ℤ × ℤ → ℤ → ℤ
lower (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n≡δ)  = rec k downLeft (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n≡i)) = rec k   upLeft (succ n)
upper (k , i) δ with ℤ-trichotomous i δ
... | inl      (n , si+n≡δ)  = rec k downRight (succ n)
... | inr (inl refl)         = k
... | inr (inr (n , sδ+n≡i)) = rec k   upRight (succ n)

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
                  → (n : ℕ) → succℤ i +pos n ≡ δ
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
                  → (n : ℕ) → succℤ δ +pos n ≡ i
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

## Relationship between below/above and lower/upper


```
replace : ((k , i) (c , δ) : ℤ × ℤ)
        → lower (k , i) δ ≤ c ≤ upper (k , i) δ
        → Σ ((x , _) , _) ꞉ CompactInterval (k , i)
        , x δ ≡ c
```

TODO

```
replace-below
         : ((k , i) (c , j) : ℤ × ℤ)
         → ((n , _) : i <ℤ j) → (c belowⁿ k) n
         → Σ ((y , _) , _) ꞉ CompactInterval (k , i) , y j ≡ c
replace-below (k , i) (c , j) (n , refl) b with build-via-ci (k , i)
... | ((x , u) , refl) = α
 where
  i<j = n , refl
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
    ζ : y i vert-trich-ij-i ≡ k
    ζ = below-vec-!!sn c k n b _
    θ : y j vert-trich-ij-j ≡ c
    θ = below-vec-!!0 c k n b
    θ* : (η : vert-trich-ij j) → y j η ≡ c
    θ* η = transport (λ - → y j - ≡ c)
             (vert-trich-ij-is-prop j i<j vert-trich-ij-j η) θ
    ζ* : (η : vert-trich-ij i) → y i η ≡ k
    ζ* η = transport (λ - → y i - ≡ k)
             (vert-trich-ij-is-prop i i<j vert-trich-ij-i η) ζ
    γ* : (z : ℤ) → (η : vert-trich-ij z) (η' : vert-trich-ij (succℤ z))
       → y (succℤ z) η' below y z η
    γ* z η η' = transport (λ - → y (succℤ z) - below y z η)
                  (vert-trich-ij-is-prop (succℤ z) i<j
                    (vert-trich-ij-succ z i<j η) η') (γ z η)

replace-above
         : ((k , i) (c , j) : ℤ × ℤ)
         → ((n , _) : j <ℤ i) → (c aboveⁿ k) n
         → Σ ((y , _) , _) ꞉ CompactInterval (k , i) , y j ≡ c
replace-above (k , i) (c , j) j<i b 
 = ((pr₁ (pr₁ γ)) , (pr₂ γ)) , (pr₂ (pr₁ γ))
 where
   γ = replace-below (c , j) (k , i) j<i (aboveⁿ-implies-belowⁿ k c (pr₁ j<i) b)
```

TODO

```
upRight≤upLeft-succ : (a : ℤ) → upRight a ≡ upLeft (succℤ a)
upRight≤upLeft-succ a = ap upRight (predsuccℤ _ ⁻¹)

upRight≤upLeft : (a b : ℤ) → a <ℤ b → upRight a ≤ upLeft b
upRight≤upLeft a b (n      , refl)
 = transport (_≤ upLeft (succℤ a +pos n)) (upRight≤upLeft-succ a ⁻¹)
     (upLeft-monotone _ _ (n , refl))

upLeft-or-upRight' : (k₁ k₂ c : ℤ) (n m : ℕ)
                   → k₁ +pos n ≡ c
                   → c +pos m ≡ k₂
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

downRight≡downLeft : (a : ℤ) → downRight a ≡ downLeft (succℤ a)
downRight≡downLeft a = ap succℤ (ℤ-left-succ a a ⁻¹ ∙ ℤ+-comm (succℤ a) a)
                     ∙ ℤ-left-succ a (succℤ a) ⁻¹

down-choices' : (k₁ k₂ c : ℤ) (n m : ℕ)
              → k₁ +pos n ≡ c
              → c +pos m ≡ k₂
              → k₁ <ℤ k₂
              → (downRight k₁ ≤ downLeft  c ≤ downLeft k₂)
              + (downRight k₁ ≤ downRight c ≤ downLeft k₂)
down-choices' k₁ .((k₁ +pos zero) +pos zero) .(k₁ +pos zero) 0 0 refl refl f
 = 𝟘-elim (b<a→a≢b _ _ f refl)
down-choices'
 k₁ .((k₁ +pos zero) +pos succ m) .(k₁ +pos zero) 0 (succ m) refl refl f
 = inr ((zero , refl)
       , transport (downRight k₁ ≤_) (downRight≡downLeft (k₁ +pos m))
           (downRight-monotone _ _ (m , refl)))
down-choices'
 k₁ .((k₁ +pos succ n) +pos m) .(k₁ +pos succ n) (succ n) m refl refl f
 = inl (transport (downRight k₁ ≤_) (downRight≡downLeft (k₁ +pos n))
          (downRight-monotone _ _ (n , refl))
      , downLeft-monotone _ _ (m , refl))

apparently : (k₁ k₂ c : ℤ)
           → downRight (upLeft k₁) ≤ c ≤ downLeft (upRight k₂)
           → k₁ ≤ c ≤ k₂
apparently k₁ k₂ c (l≤c , c≤u)
 = ℤ≤-trans _ _ _ (downRight-upLeft k₁) l≤c
 , ℤ≤-trans _ _ _ c≤u (downLeft-upRight k₂) 

down-choices : (k₁ k₂ c : ℤ)
             → (k₁ <ℤ k₂) + (k₁ ≡ k₂)
             → upLeft k₁ ≤           c ≤ upRight k₂
             →       (k₁ ≤ downLeft  c ≤ k₂)
             +       (k₁ ≤ downMid   c ≤ k₂)
             +       (k₁ ≤ downRight c ≤ k₂)
down-choices k₁ k₂ c (inl k₁<k₂) ((m₁ , η₁) , (m₂ , η₂))
 = Cases (down-choices' (upLeft k₁) (upRight k₂) c m₁ m₂ η₁ η₂ (upLeft-<< k₁ k₂ k₁<k₂))
     (λ l → inl         (apparently _ _ _ l))
     (λ r → (inr ∘ inr) (apparently _ _ _ r))
down-choices k k c (inr refl) ((m₁ , η₁) , (m₂ , η₂))
 = Cases (below-implies-below' k c (above-implies-below c k ((m₁ , η₁) , (m₂ , η₂))))
     l (cases m r)
 where
   l : _
   l refl = inl ((zero , refl) , zero , refl)
   m : _
   m refl = inr (inl ((zero , refl) , zero , refl))
   r : _
   r refl = inr (inr ((zero , refl) , zero , refl))

upLeft-or-upRight : (k₁ k₂ c : ℤ)
                  → k₁ ≤ k₂
                  → downLeft k₁ ≤         c ≤ downRight k₂
                  →         (k₁ ≤ upLeft  c ≤           k₂)
                  +         (k₁ ≤ upRight c ≤           k₂)
upLeft-or-upRight k₁ k₂ c k₁≤k₂ ((m₁ , η₁) , (m₂ , η₂))
 = Cases (upLeft-or-upRight' (downLeft k₁) (downRight k₂) c m₁ m₂ η₁ η₂ (downLeft≤<downRight k₁ k₂ k₁≤k₂))
     (λ l → inl (transport (_≤ upLeft c ≤ k₂) (upRight-downLeft k₁ ⁻¹)
       (transport (upRight (downLeft k₁) ≤ upLeft c ≤_) (upLeft-downRight k₂) l)))
     (λ r → inr (transport (_≤ upRight c ≤ k₂) (upRight-downLeft k₁ ⁻¹)
       (transport (upRight (downLeft k₁) ≤ upRight c ≤_) (upLeft-downRight k₂) r)))

rec-f-≡ : {X : 𝓤 ̇ } → (f : X → X) (x : X) (n : ℕ)
        → rec (f x) f n ≡ rec x f (succ n) 
rec-f-≡ f x zero = refl
rec-f-≡ f x (succ n) = ap f (rec-f-≡ f x n)
```

TODO

```
{-
below-lower-upper : (k c : ℤ) (n : ℕ)
                  → (c belowⁿ k) n
                  → rec k downLeft (succ n) ≤ c ≤ rec k downRight (succ n)
below-lower-upper k c zero = id
below-lower-upper k c (succ n) (b , η , θ)
 = ℤ≤-trans _ _ _ (transport (_≤ rec k* downLeft (succ n))
                    (rec-f-≡ downLeft k (succ n))
                      (downLeftⁿ-monotone (downLeft k) k* n dLk≤k*))
                    (pr₁ IH₂)
 , ℤ≤-trans _ _ _ (pr₂ IH₂)
                  (transport (rec k* downRight (succ n) ≤_)
                    (rec-f-≡ downRight k (succ n))
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
-}
lower-upper-below : (k c : ℤ) (n : ℕ)
                  → rec k downLeft (succ n) ≤ c ≤ rec k downRight (succ n)
                  → (c belowⁿ k) n
lower-upper-below k c 0 = id
lower-upper-below k c (succ n) l≤c≤u
 = Cases (upLeft-or-upRight _ _ _ (downLeft≤downRight k (succ n)) l≤c≤u)
     (λ η → (upLeft  c) , ((above-implies-below _ _ (upLeft-above  c)) , (IH-l η)))
     (λ η → (upRight c) , ((above-implies-below _ _ (upRight-above c)) , (IH-r η)))
 where
   IH-l = lower-upper-below k (upLeft  c) n 
   IH-r = lower-upper-below k (upRight c) n

lower-upper-above : (k c : ℤ) (n : ℕ)
                  → rec k upLeft (succ n) ≤ c ≤ rec k upRight (succ n)
                  → (c aboveⁿ k) n
lower-upper-above k c 0 = id
lower-upper-above k c (succ n) l≤c≤u
 = Cases (down-choices _ _ _ (ℤ≤-split _ _ (upLeft≤upRightⁿ k (succ n))) l≤c≤u)
      (λ η → downLeft  c , below-implies-above _ _ (downLeft-below  c) , (IH-l η))
     (cases
      (λ η → downMid   c , below-implies-above _ _ (downMid-below   c) , (IH-m η))
      (λ η → downRight c , below-implies-above _ _ (downRight-below c) , (IH-r η)))
 where
   IH-l = lower-upper-above k (downLeft  c) n
   IH-m = lower-upper-above k (downMid   c) n
   IH-r = lower-upper-above k (downRight c) n

replace (k , i) (c , δ) l≤c≤u with ℤ-trichotomous i δ
... | inl i<δ
    = replace-below (k , i) (c , δ) i<δ (lower-upper-below k c (pr₁ i<δ) l≤c≤u)
... | inr (inl refl)
    = build-via-ci (k , i)
    , (build-via'-correct (k , i) (ℤ-trichotomous i i) ∙ ≤ℤ-antisym k c l≤c≤u)
... | inr (inr δ<i)
    = replace-above (k , i) (c , δ) δ<i (lower-upper-above k c (pr₁ δ<i) l≤c≤u)
```

## Signed-digits are isomorphic to Ternary Boehm reals

Recall that we previously represented numbers in the closed interval
[-1,1] using signed-digit functions of type ℕ → 𝟛.

⦉_⦊ : (ℕ → 𝟛) → ℝ
⦉ α ⦊ = Σᵢ α i * 2^{-i-1}

This interval is represented by the Boehm "brick" (-1 , -1) : ℕ × ℕ.

```
[−1,1]-code : ℤ × ℤ
[−1,1]-code = (negsucc 0 , negsucc 0)
```

The location structure of the signed-digit approach is actually
isomorphic to the ternary Boehm approach.

For example, the signed digit function
 α ≔     { −1            ,  O           , +1             ...} : ℕ → 𝟛
follows the same location structure as
 x ≔ {-1 , downLeft x(0) , downMid x(1) , downRight x(2) ...} : ℕ → ℤ

```
𝟛-to-down : 𝟛 → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

signed-to-boehm' : (ℕ → 𝟛) → (ℕ → ℤ)
signed-to-boehm' α 0 = negsucc 0
signed-to-boehm' α (succ n) = 𝟛-to-down (α n) (signed-to-boehm' α n)
```

signed-to-boehm'-below
  : (α : ℕ → 𝟛) → (n : ℕ)
  → (signed-to-boehm' α (succ n)) below (signed-to-boehm' α n)
signed-to-boehm'-below α n = {!!} -- Easy

signed-to-boehm : (ℕ → 𝟛) → CompactInterval [−1,1]-code
signed-to-boehm α
 = build-ci (signed-to-boehm' α , signed-to-boehm'-below α)

Therefore, it should be the case that, for all x : ℕ → 𝟛
⦉ x ⦊ = ⟦ signed-to-boehm x ⟧.

Recall that we use an interval object specification of the real
numbers 𝕀.

We already defined the following realisability map,

q : 𝟛 → 𝕀
q −1 = −1
q  O =  O
q +1 = +1

𝕢 : (ℕ → 𝟛) → 𝕀
𝕢 = M ∘ map ⟨_⟩

We also want to define the following realisability map,

𝕣 : CompactInterval [−1,1]-code → 𝕀

such that for all x : ℕ → 𝟛, 𝕢 x = 𝕣 (signed-to-boehm x).

We will do this by defining,

boehm-to-signed : CompactInterval [−1,1]-code → (ℕ → 𝟛)
boehm-to-signed {!!}

such that

boehm-signed-iso₁ : boehm-to-signed ∘ signed-to-boehm ≃ id
boehm-signed-iso₁ = {!!}

boehm-signed-iso₂ : signed-to-boehm ∘ boehm-to-signed ≃ id
boehm-signed-iso₂ = {!!}

Then, by setting

𝕣 = 𝕢 ∘ boehm-to-signed,

our proof follows: we immediately get that for all x : ℕ → 𝟛,

𝕢 x = (𝕢 ∘ boehm-to-signed) (signed-to-boehm x),

by boehm-signed-iso₁.

----

Ask Andrew:
 * Implement countable/iterated midpoint on Dedekind reals

-------------------------------------------------------------------

## The key difference

The key difference between the signed digit approach and the Boehm
approach is that,
 * With signed digit, the information kept in x(n) *depends on*
                      the information in all x(i) such that i < n,
 * With Boehm codes,  the information kept in x(n) *includes*
                      the information in all x(i) such that i < n.

-------------------------------------------------------------------

## Closeness function on 𝕋

For every discrete-sequence type ℕ → X (where X is discrete), we have
a canonical closeness function c : (ℕ → X) × (ℕ → X) → ℕ∞.

Recall that for x,y : ℕ → X and any δ : ℕ,

c (x , y) ≼ ι δ ⇔ (x ≈ y) δ,

where c(x , y) : ℕ∞ is the value of the discrete-sequence closeness
function for x and y.

```
_≈'_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈' β) n = (i : ℕ) → i <ℕ n → α n ≡ β n
```

From the canonical closeness function on (ℕ → ℤ), we can define one
on 𝕋:

c : 𝕋 × 𝕋 → ℕ∞
c ((α , _) , (β , _)) = c (α ∘ pos , β ∘ pos)

Note that we only take into account positive precision-levels of
object x : 𝕋; but, as we already said, for our purposes of encoding
real numbers, the information kept in any ⟨ x ⟩ (pos n₁) : ℤ includes
the information kept in any ⟨ x ⟩ (negsucc n₂) : ℤ.

This closeness function, like that on signed-digits, gives the
closeness of *encodings* of real numbers; not the real numbers
themselves. If we wish to determine the closeness of the numbers
themselves, we can instead use the following pseudo-closeness
function (BUT MAYBE NOT)

pc : 𝕋 × 𝕋 → ℕ∞ 
pc ((α , _) , (β , _))
 = λ n → dec-to-𝟚 (abs (α (pos n) −ℤ β (pos n)) ≤ 2)

## Predicates we wish to search

In our general regression framework, we search uniformly continuous
decidable predicates on types equipped with closeness functions.

(Recall that there is no non-trivial uniformly continuous decidable
predicate on the real numbers ℝ.)

When defining uniformly continuous predicates on signed-digits,
we utilised the discrete-sequence closeness function.

```
uc-d-predicates-on-seqs : {𝓦 𝓤 : Universe} → {X : 𝓤 ̇ } → (δ : ℕ) → (𝓦 ⁺) ⊔ 𝓤 ̇
uc-d-predicates-on-seqs {𝓦} {𝓤} {X} δ
 = decidable-predicate-informed-by {𝓦}
     (sequence-relation-≈' (λ _ → X) δ)
```

We call the δ : ℕ of such a predicate its 'modulus of continuity'.

So for uniformly continuous decidable predicates p on signed-digit
encodings x,y : ℕ → 𝟛, with modulus of continuity δ : ℕ, it is enough
to know that (x ≈ y) δ to know that p(x) is logically equivalent
to p(y).

(Reword ↓)
But! With Boehm codes 𝕋, all the information is kept in the most recent
code. So an "equivalent" predicate should only need to satisfy the
following.

```
open equivalence-relation

ℤ→ℤ-equivalence-relation : (δ : ℤ) → equivalence-relation {𝓤₀} (ℤ → ℤ)
_≣_     (ℤ→ℤ-equivalence-relation δ) x y   = x δ ≡ y δ
≣-refl  (ℤ→ℤ-equivalence-relation δ) x     = refl
≣-sym   (ℤ→ℤ-equivalence-relation δ) x y   = _⁻¹
≣-trans (ℤ→ℤ-equivalence-relation δ) x y z = _∙_

pr₁-equivalence-relation : {X : 𝓤 ̇ } {Y : X → 𝓤' ̇ }
                         → equivalence-relation {𝓥} X
                         → equivalence-relation {𝓥} (Σ Y)
_≣_     (pr₁-equivalence-relation A) x y   = pr₁ x ≣⟨ A ⟩ pr₁ y
≣-refl  (pr₁-equivalence-relation A) x     = ≣-refl  A (pr₁ x)
≣-sym   (pr₁-equivalence-relation A) x y   = ≣-sym   A (pr₁ x) (pr₁ y)
≣-trans (pr₁-equivalence-relation A) x y z = ≣-trans A (pr₁ x) (pr₁ y) (pr₁ z)

𝕋-equivalence-relation : (δ : ℤ) → equivalence-relation {𝓤₀} 𝕋
𝕋-equivalence-relation δ = pr₁-equivalence-relation (ℤ→ℤ-equivalence-relation δ)

𝕋c-equivalence-relation : ((k , i) : ℤ × ℤ) (δ : ℤ)
                        → equivalence-relation {𝓤₀} (CompactInterval (k , i))
𝕋c-equivalence-relation (k , i) δ = pr₁-equivalence-relation (𝕋-equivalence-relation δ)

special-predicate-on-𝕋 : {𝓦 : Universe} → (δ : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-𝕋 {𝓦} δ
 = decidable-predicate-informed-by {𝓦} (𝕋-equivalence-relation δ)
```

Relationships:
 * c (α , β) ≼ δ                 → pc (α , β) ≼ δ
 * c (α , β) ≼ (succ δ)          → ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ)
 * ⟨ α ⟩ (pos δ) ≡ ⟨ β ⟩ (pos δ) → pc (α , β) ≼ δ ?

## Special predicates on K relate to predicates on ℤ × ℤ

```
special-predicate-on-I : {𝓦 : Universe} → (δ : ℤ) → (𝓦 ⁺) ̇
special-predicate-on-I {𝓦} δ
 = decidable-predicate-informed-by {𝓦} (Identity ℤ)

open equiv-of-setoids

SE' : (δ : ℤ)
    → equiv-of-setoids
        (𝕋-equivalence-relation δ)
        (Identity ℤ)
f (SE' δ) = (λ α → α δ) ∘ ⟨_⟩
g (SE' δ) = build-via ∘ (_, δ)
trans-A (SE' δ) α = ap (λ - → build-via' (⟨ α ⟩ δ , δ) δ -) (ℤ-trichotomous-is-prop δ δ ((inr ∘ inl) refl) (ℤ-trichotomous δ δ))
trans-B (SE' δ) z = ap (λ - → build-via' (  z     , δ) δ -) (ℤ-trichotomous-is-prop δ δ ((inr ∘ inl) refl) (ℤ-trichotomous δ δ))
lift-AB (SE' δ) α β = id
lift-BA (SE' δ) z z refl = refl

special-predicate-𝕋-to-I
 : {𝓦 : Universe} → (δ : ℤ)
 →  (pdiϕ𝕋 : special-predicate-on-𝕋 {𝓦} δ)
 → Σ pdiϕI ꞉ special-predicate-on-I {𝓦} δ
 , ((x : 𝕋)
       → p⟨ 𝕋-equivalence-relation _    - pdiϕ𝕋 ⟩ x
       → p⟨ Identity _                   - pdiϕI ⟩ (f (SE' δ) x))
special-predicate-𝕋-to-I δ
 = convert-predicates _ _ (SE' δ)

special-predicate-I-to-𝕋
 : {𝓦 : Universe} → (δ : ℤ)
 →  (pdiϕI : special-predicate-on-I {𝓦} δ)
 → Σ pdiϕ𝕋 ꞉ special-predicate-on-𝕋 {𝓦} δ
 , ((x : ℤ)
       → p⟨ Identity _                   - pdiϕI ⟩ x
       → p⟨ 𝕋-equivalence-relation _     - pdiϕ𝕋 ⟩ (g (SE' δ) x))
special-predicate-I-to-𝕋 δ
 = convert-predicates _ _ (equiv-of-setoids-sym _ _ (SE' δ))
```

But these are not searchable!

## Special predicates on CompactIntervals relate to searchable predicates on I

```

special-predicate-on-𝕋c : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-𝕋c {𝓦} (k , i) δ
 = decidable-predicate-informed-by {𝓦} (𝕋c-equivalence-relation (k , i) δ)

special-predicate-on-Ic : {𝓦 : Universe} → (δ l u : ℤ) → (𝓦 ⁺) ̇ 
special-predicate-on-Ic {𝓦} δ l u
 = decidable-predicate-informed-by {𝓦} (Identity (ℤ[ l , u ]))
```

These are searchable.

```
{-
η : (n : ℤ) → (x : 𝕋) → CompactInterval (⟨ x ⟩ n , n)
η n = _, refl
-}
```

The Ic predicates are searchable, and are logically equivalent to the 𝕋c
predicates.

```
SE : ((k , i) : ℤ × ℤ) (δ : ℤ)
   → equiv-of-setoids
       (𝕋c-equivalence-relation (k , i) δ)
       (Identity ℤ[ (lower (k , i) δ) , (upper (k , i) δ) ])
f (SE (k , i) δ) α           = ⟨ ι α ⟩ δ , ci-lower-upper (k , i) α δ
g (SE (k , i) δ) (z , l≤z≤u) = pr₁ (replace (k , i) (z , δ) l≤z≤u)
trans-A (SE (k , i) δ) α
 = pr₂ (replace (k , i) (⟨ ι α ⟩ δ , δ) (ci-lower-upper (k , i) α δ)) ⁻¹
trans-B (SE (k , i) δ) (z , l≤z≤u)
 = to-subtype-≡ ≤ℤ²-is-prop (pr₂ (replace (k , i) (z , δ) l≤z≤u) ⁻¹)
lift-AB (SE (k , i) δ) α β
 = to-subtype-≡ ≤ℤ²-is-prop 
lift-BA (SE (k , i) δ) (z , l≤z≤u) (z , l≤z≤u) refl
 = refl

special-predicate-𝕋c-to-Ic
 : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
 →  (pdiϕ𝕋c : special-predicate-on-𝕋c {𝓦} (k , i) δ)
 → Σ pdiϕIc ꞉ special-predicate-on-Ic {𝓦} δ (lower (k , i) δ) (upper (k , i) δ)
 , ((x : CompactInterval (k , i))
       → p⟨ 𝕋c-equivalence-relation _ _ - pdiϕ𝕋c ⟩ x
       → p⟨ Identity _                  - pdiϕIc ⟩ (f (SE (k , i) δ) x))
special-predicate-𝕋c-to-Ic (k , i) δ
 = convert-predicates _ _ (SE (k , i) δ)

special-predicate-Ic-to-𝕋c
 : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
 →  (pdiϕIc : special-predicate-on-Ic {𝓦} δ (lower (k , i) δ) (upper (k , i) δ))
 → Σ pdiϕ𝕋c ꞉ special-predicate-on-𝕋c {𝓦} (k , i) δ
 , ((x : ℤ[ _ , _ ])
       → p⟨ Identity _                  - pdiϕIc ⟩ x
       → p⟨ 𝕋c-equivalence-relation _ _ - pdiϕ𝕋c ⟩ (g (SE (k , i) δ) x))
special-predicate-Ic-to-𝕋c (k , i) δ
 = convert-predicates _ _ (equiv-of-setoids-sym _ _ (SE (k , i) δ))
```

Therefore, 𝕋c predicates are searchable in two ways: directly, or
via the setoid equivalence.

```

𝕋c-searchable-directly : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
                       → Searchable {𝓦} (𝕋c-equivalence-relation (k , i) δ)
𝕋c-searchable-directly = {!!}

𝕋c-searchable-equiv : {𝓦 : Universe} → ((k , i) : ℤ × ℤ) → (δ : ℤ)
                    → Searchable {𝓦} (𝕋c-equivalence-relation (k , i) δ)
𝕋c-searchable-equiv (k , i) δ
 = convert-searchable _ _ (SE (k , i) δ) (ℤ[ l , u ]-searchable (pr₁ l≤u) (pr₂ l≤u))
 where
   l = lower (k , i) δ
   u = upper (k , i) δ
   l≤u = lower≤upper(k , i) δ

```


## Predicates to test

## Fuel

```
```


---------------------------------------------------------------------

## Predicates on interval encodings

A uc-d predicate on an interval encoding is as follows:

uc-d-predicate-on-I : (p : ℤ × ℤ → 𝓤 ̇ ) → 𝓤 ̇
uc-d-predicate-on-I p
 = ((k , i) : ℤ × ℤ) → decidable (p (k , i)))
 × (((k , i) (c , j) : ℤ) → (k , i) ≡ (c , j) → p (k , i) ⇔ p (c , j))

Of course, because ℤ × ℤ is discrete, such predicates are always
uniformly continuous -- the second condition always holds. Therefore,
we need only consider decidable predicates

d-predicate-on-I : 𝓤 ⁺
d-predicate-on-I p i l u
 = Σ p : (ℤ × ℤ → 𝓤 ̇ ) , Σ (i , l , u : ℤ) ̇
 , ((k : ℤ) → l ≤ k ≤ u → decidable (p (k , i)))

"Beneath" each special predicate on 𝕋, is a decidable predicate on ℤ.

construct-sp : d-predicate-on-I
             → Σ p* : (𝕋 → 𝓤 ̇) , special-predicate p 
construct-sp (p , i , l , u , d)
 = (λ (α , _) → p (α(i) , i))
 , (λ (α , _) → d (α(i) , i))
 , (i , λ (α , _) (β , _) αi≡βi →
      (transport (λ - → p (- , i)) (αi≡βi ⁻¹))
    , (transport (λ - → p (- , i))  αi≡βi    ))

destruct-sp : (p* : 𝕋 → 𝓤 ̇ ) → special-predicate p*
            → Σ p : (ℤ × ℤ) → 𝓤 ̇ , 

## Subsets of ℤ are searchable
