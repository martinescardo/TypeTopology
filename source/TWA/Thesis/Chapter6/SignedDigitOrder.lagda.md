[⇐ Index](../html/TWA.Thesis.index.html)

# Real-order preserving order on ternary signed-digit encodings

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Naturals.Order
open import UF.FunExt
open import UF.PropTrunc
open import Quotient.Type using (is-prop-valued)
open import Integers.Type
open import Notation.Order
open import Integers.Order

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter5.BelowAndAbove
open import TWA.Thesis.Chapter5.Integers

module TWA.Thesis.Chapter6.SignedDigitOrder
  (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
```

## Integer approx (originally defined in BoehmVerification)

```
𝟛-to-down : (a : 𝟛) → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

integer-approx' : 𝟛ᴺ → ℤ → (ℕ → ℤ)

integer-approx'' : 𝟛 → 𝟛ᴺ → ℤ → (ℕ → ℤ)
integer-approx'' _ α k 0 = k
integer-approx'' b α k (succ n)
 = integer-approx' α (𝟛-to-down b k) n

integer-approx' α = integer-approx'' (α 0) (α ∘ succ)

integer-approx : 𝟛ᴺ → (ℕ → ℤ)
integer-approx α = integer-approx' α (negsucc 0)

ternary-to-ℤ²' : 𝟛 → 𝟛ᴺ → ℤ → (ℕ → ℤ × ℕ)
ternary-to-ℤ²' b α k n = integer-approx α n , n

ternary-to-ℤ² : 𝟛ᴺ → (ℕ → ℤ × ℕ)
ternary-to-ℤ² α = ternary-to-ℤ²' (α 0) (α ∘ succ) (negsucc 0)
```

## Real preserving preorder

```

module RealPresOrder (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _≤𝟛ᴺ_ : 𝟛ᴺ → 𝟛ᴺ → 𝓤₀ ̇
 x ≤𝟛ᴺ y
  = ∃ n ꞉ ℕ
  , ((i : ℕ) → n ≤ i → integer-approx x i ≤ integer-approx y i)

 ≤𝟛ᴺ-is-preorder : is-preorder _≤𝟛ᴺ_
 ≤𝟛ᴺ-is-preorder = r , t , p
  where
   r : reflexive _≤𝟛ᴺ_
   r x = ∣ (0 , λ i _ → ℤ≤-refl _) ∣
   t : transitive _≤𝟛ᴺ_
   t x y z x≤y y≤z
    = ∥∥-rec ∃-is-prop (λ x≤y' → ∥∥-rec ∃-is-prop (∣_∣ ∘ γ x≤y') y≤z) x≤y
    where
     γ : (Σ n  ꞉ ℕ , ((i : ℕ) → n  ≤ i
                   → integer-approx x i ≤ integer-approx y i))
       → (Σ m  ꞉ ℕ , ((i : ℕ) → m  ≤ i
                   → integer-approx y i ≤ integer-approx z i))
       →  Σ nm ꞉ ℕ , ((i : ℕ) → nm ≤ i
                   → integer-approx x i ≤ integer-approx z i)
     γ (n , f) (m , g)
      = max n m
      , λ i nm≤i → ℤ≤-trans _ _ _ (f i (n≤ i nm≤i)) (g i (m≤ i nm≤i))
      where
       n≤ : (i : ℕ) → max n m ≤ i → n ≤ i
       n≤ i nm≤i = ≤-trans n (max n m) i (max-≤-upper-bound n m) nm≤i
       m≤ : (i : ℕ) → max n m ≤ i → m ≤ i
       m≤ i nm≤i = ≤-trans m (max n m) i (max-≤-upper-bound' m n) nm≤i
   p : is-prop-valued _≤𝟛ᴺ_
   p x y = ∃-is-prop
```

## Real-preserving approximate order

```
_≤ⁿ𝟛ᴺ_ : 𝟛ᴺ → 𝟛ᴺ → ℕ → 𝓤₀ ̇
(x ≤ⁿ𝟛ᴺ y) n = integer-approx x n ≤ integer-approx y n

≤ⁿ𝟛ᴺ-is-linear-preorder
 : (n : ℕ) → is-linear-preorder (λ x y → (x ≤ⁿ𝟛ᴺ y) n)
≤ⁿ𝟛ᴺ-is-linear-preorder n
 = ((λ x → ℤ≤-refl _)
 , (λ x y z → ℤ≤-trans _ _ _)
 , λ x y → ℤ≤-is-prop _ _)
 , λ x y → ℤ-dichotomous _ _

≤ⁿ𝟛ᴺ-is-decidable : (n : ℕ) (x y : 𝟛ᴺ)
                  → is-decidable ((x ≤ⁿ𝟛ᴺ y) n)
≤ⁿ𝟛ᴺ-is-decidable n x y = ℤ≤-decidable _ _

integer-approx'-ucontinuous
 : (ϵ : ℕ) (x y : 𝟛ᴺ)
 → (x ∼ⁿ y) ϵ
 → (k : ℤ)
 → integer-approx' x k ϵ ＝ integer-approx' y k ϵ
integer-approx'-ucontinuous 0 x y x∼y k = refl 
integer-approx'-ucontinuous (succ ϵ) x y x∼y k
 = ap (λ - → integer-approx'' (x 1) (x ∘ succ ∘ succ)
              (𝟛-to-down - k) ϵ)
   (x∼y 0 ⋆)
 ∙ integer-approx'-ucontinuous ϵ (x ∘ succ) (y ∘ succ)
     (x∼y ∘ succ) (𝟛-to-down (y 0) k)

≤ⁿ𝟛ᴺ-closeness : (ϵ : ℕ) (x y : 𝟛ᴺ)
               → C 𝟛ᴺ-ClosenessSpace ϵ x y
               → (x ≤ⁿ𝟛ᴺ y) ϵ
≤ⁿ𝟛ᴺ-closeness ϵ x y Cxy
 = 0 , integer-approx'-ucontinuous ϵ x y
         (C-to-∼ⁿ 𝟛-is-discrete x y ϵ Cxy) (negsucc 0)

≤ⁿ𝟛ᴺ-is-approx-order : is-approx-order 𝟛ᴺ-ClosenessSpace _≤ⁿ𝟛ᴺ_
≤ⁿ𝟛ᴺ-is-approx-order
 = ≤ⁿ𝟛ᴺ-is-linear-preorder , ≤ⁿ𝟛ᴺ-is-decidable , ≤ⁿ𝟛ᴺ-closeness

module RealPresOrder-Relates
 (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open RealPresOrder pt
 open ApproxOrder-Relates pt

 ≤ⁿ𝟛ᴺ-relates→ : _≤ⁿ𝟛ᴺ_ relates-to→ _≤𝟛ᴺ_
 ≤ⁿ𝟛ᴺ-relates→ x y f = ∣ (0 , λ x _ → f x) ∣

 ≤ⁿ𝟛ᴺ-relates← : _≤ⁿ𝟛ᴺ_ relates-to← _≤𝟛ᴺ_
 ≤ⁿ𝟛ᴺ-relates← x y = id

 ≤ⁿ𝟛ᴺ-relates : approx-order-relates
                 𝟛ᴺ-ClosenessSpace
                 _≤ⁿ𝟛ᴺ_ ≤ⁿ𝟛ᴺ-is-approx-order
                 _≤𝟛ᴺ_ ≤𝟛ᴺ-is-preorder
 ≤ⁿ𝟛ᴺ-relates = ≤ⁿ𝟛ᴺ-relates→ , ≤ⁿ𝟛ᴺ-relates←
```

[⇐ Index](../html/TWA.Thesis.index.html)
