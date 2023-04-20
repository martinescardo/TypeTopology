Andrew Sneap, Jan-July 2021

This file defines addition of rational numbers, and proves various properties of
addition.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness  --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Base hiding (_≈_)
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (_+_ to _𝔽+_)
open import Rationals.Type

module Rationals.Addition where

_+_ : ℚ → ℚ → ℚ
(p , _) + (q , _) = toℚ (p 𝔽+ q)

infixl 32 _+_

ℚ+-comm : (p q : ℚ) → p + q ＝ q + p
ℚ+-comm (p , _) (q , _) = ap toℚ I
 where
  I : p 𝔽+ q ＝ q 𝔽+ p
  I = 𝔽+-comm p q

toℚ-+ : (p q : 𝔽) → toℚ (p 𝔽+ q) ＝ toℚ p + toℚ q
toℚ-+ p q = equiv→equality (p 𝔽+ q) (p' 𝔽+ q') conclusion
 where
  p-ℚ = toℚ p
  q-ℚ = toℚ q
  p' = to𝔽 p-ℚ
  q' = to𝔽 q-ℚ

  I : p ≈ p'
  I = ≈-toℚ p

  II : q ≈ q'
  II = ≈-toℚ q

  III : p 𝔽+ q ≈ p' 𝔽+ q
  III = ≈-addition p p' q I

  IV : q 𝔽+ p' ≈ q' 𝔽+ p'
  IV = ≈-addition  q q' p' II

  V : p' 𝔽+ q ≈ p' 𝔽+ q'
  V = transport₂ _≈_ (𝔽+-comm q p') (𝔽+-comm q' p') IV

  conclusion : p 𝔽+ q ≈ p' 𝔽+ q'
  conclusion = ≈-trans (p 𝔽+ q) (p' 𝔽+ q) (p' 𝔽+ q') III V

ℚ+-assoc : (p q r : ℚ) → p + q + r ＝ p + (q + r)
ℚ+-assoc (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) + (q , β) + (r , δ) ＝ (p , α) + ((q , β) + (r , δ))
  γ = (p , α) + (q , β) + (r , δ)   ＝⟨ refl ⟩
      toℚ (p 𝔽+ q) + (r , δ)        ＝⟨ i    ⟩
      toℚ (p 𝔽+ q) + toℚ r          ＝⟨ ii   ⟩
      toℚ (p 𝔽+ q 𝔽+ r)             ＝⟨ iii  ⟩
      toℚ (p 𝔽+ (q 𝔽+ r))           ＝⟨ iv   ⟩
      toℚ p + toℚ (q 𝔽+ r)          ＝⟨ v    ⟩
      (p , α) + toℚ (q 𝔽+ r)        ＝⟨ refl ⟩
      (p , α) + ((q , β) + (r , δ)) ∎
   where
    i   = ap (toℚ (p 𝔽+ q) +_) (toℚ-to𝔽 (r , δ))
    ii  = toℚ-+ (p 𝔽+ q) r ⁻¹
    iii = ap toℚ (𝔽+-assoc p q r)
    iv  = toℚ-+ p (q 𝔽+ r)
    v   = ap (_+ toℚ (q 𝔽+ r)) (toℚ-to𝔽 (p , α) ⁻¹)

ℚ+-rearrange : (x y z : ℚ) → x + y + z ＝ x + z + y
ℚ+-rearrange x y z = x + y + z     ＝⟨ ℚ+-assoc x y z          ⟩
                     x + (y + z)   ＝⟨ ap (x +_) (ℚ+-comm y z) ⟩
                     x + (z + y)   ＝⟨ ℚ+-assoc x z y ⁻¹       ⟩
                     x + z + y     ∎

ℚ+-rearrange' : (x y z : ℚ) → x + y + z ＝ z + x + y
ℚ+-rearrange' x y z = x + y + z   ＝⟨ ℚ+-comm (x + y) z ⟩
                      z + (x + y) ＝⟨ ℚ+-assoc z x y ⁻¹ ⟩
                      z + x + y   ∎

ℚ-zero-right-neutral : (q : ℚ) → q + 0ℚ ＝ q
ℚ-zero-right-neutral (q , α) = γ
 where
  γ : (q , α) + 0ℚ ＝ (q , α)
  γ = (q , α) + 0ℚ           ＝⟨ refl                            ⟩
      toℚ (q 𝔽+ (pos 0 , 0)) ＝⟨ ap toℚ (𝔽-zero-right-neutral q) ⟩
      toℚ q                  ＝⟨ toℚ-to𝔽 (q , α) ⁻¹              ⟩
      q , α                  ∎

ℚ-zero-left-neutral : (q : ℚ) → 0ℚ + q ＝ q
ℚ-zero-left-neutral q = ℚ+-comm 0ℚ q ∙ ℚ-zero-right-neutral q

add-same-denom : ((x , a) (y , a) : 𝔽)
               → toℚ (x , a) + toℚ (y , a) ＝ toℚ (x ℤ+ y , a)
add-same-denom (x , a) (y , b) = γ
 where
  I : ((x , b) 𝔽+ (y , b)) ≈ (x ℤ+ y , b)
    → toℚ ((x , b) 𝔽+ (y , b)) ＝ toℚ (x ℤ+ y , b)
  I = equiv→equality ((x , b) 𝔽+ (y , b)) (x ℤ+ y , b)

  II : (x , b) 𝔽+ (y , b) ≈ (x ℤ+ y , b)
  II = 𝔽-add-same-denom (x , b) (y , b)

  γ : toℚ (x , b) + toℚ (y , b) ＝ toℚ (x ℤ+ y , b)
  γ = toℚ (x , b) + toℚ (y , b) ＝⟨ toℚ-+ (x , b) (y , b) ⁻¹ ⟩
      toℚ ((x , b) 𝔽+ (y , b))  ＝⟨ I II                     ⟩
      toℚ (x ℤ+ y , b)          ∎

1/3+1/3 : 1/3 + 1/3 ＝ 2/3
1/3+1/3 = add-same-denom (pos 1 , 2) (pos 1 , 2)

1/4+1/4 : 1/4 + 1/4 ＝ 1/2
1/4+1/4 = γ
 where
  γ : toℚ (pos 1 , 3) + toℚ (pos 1 , 3) ＝ toℚ (pos 1 , 1)
  γ = toℚ (pos 1 , 3) + toℚ (pos 1 , 3) ＝⟨ i  ⟩
      toℚ (pos 1 ℤ+ pos 1 , 3)          ＝⟨ ii ⟩
      toℚ (pos 1 , 1)                   ∎
   where
    i  = add-same-denom (pos 1 , 3) (pos 1 , 3)
    ii = equiv→equality (pos 2 , 3) (pos 1 , 1) refl

1/2+1/4 : 1/2 + 1/4 ＝ 3/4
1/2+1/4 = equiv→equality ((pos 1 , 1) 𝔽+ (pos 1 , 3)) (pos 3 , 3) refl

\end{code}

For the following code, the flag lossy-unification must be added, otherwise the
<<<<<<< HEAD
type checking takes too long to complete.
=======
file has compilation issues.
>>>>>>> master

\begin{code}

1/4+3/4 : 1/4 + 3/4 ＝ 1ℚ
1/4+3/4 = I ⁻¹ ∙ equiv→equality ((pos 1 , 3) 𝔽+ (pos 3 , 3)) (pos 1 , 0) refl
 where
  abstract
   I : toℚ ((pos 1 , 3) 𝔽+ (pos 3 , 3)) ＝  toℚ (pos 1 , 3) + toℚ (pos 3 , 3)
   I = toℚ-+ (pos 1 , 3) (pos 3 , 3)

1/3+2/3 : 1/3 + 2/3 ＝ 1ℚ
1/3+2/3 = I ∙ equiv→equality (pos 3 , 2) (pos 1 , 0) refl
 where
  abstract
   I : toℚ (pos 1 , 2) + toℚ (pos 2 , 2) ＝ toℚ (pos 1 ℤ+ pos 2 , 2)
   I = add-same-denom (pos 1 , 2) (pos 2 , 2)

2/3+1/3 : 2/3 + 1/3 ＝ 1ℚ
2/3+1/3 = ℚ+-comm 2/3 1/3 ∙ 1/3+2/3

1/2+1/2 : 1/2 + 1/2 ＝ 1ℚ
1/2+1/2 = I refl
 where
  I : ((pos 1 , 1) 𝔽+ (pos 1 , 1)) ≈ (pos 1 , 0)
    → toℚ ((pos 1 , 1) 𝔽+ (pos 1 , 1)) ＝ toℚ (pos 1 , 0)
  I = equiv→equality ((pos 1 , 1) 𝔽+ (pos 1 , 1)) (pos 1 , 0)

1/5+1/5 : 1/5 + 1/5 ＝ 2/5
1/5+1/5 = I
 where
  abstract
   I : 1/5 + 1/5 ＝ 2/5
   I = add-same-denom (pos 1 , 4) (pos 1 , 4)

1/5+2/5 : 1/5 + 2/5 ＝ 3/5
1/5+2/5 = I
 where
  abstract
   I : 1/5 + 2/5 ＝ 3/5
   I = add-same-denom (pos 1 , 4) (pos 2 , 4)

2/5+1/5 : 2/5 + 1/5 ＝ 3/5
2/5+1/5 = (ℚ+-comm 2/5 1/5) ∙ (1/5+2/5)

2/5+3/5-lemma : toℚ (pos 2 , 4) + toℚ (pos 3 , 4) ＝ toℚ (pos 2 ℤ+ pos 3 , 4)
2/5+3/5-lemma = I
 where
  abstract
   I : toℚ (pos 2 , 4) + toℚ (pos 3 , 4) ＝ toℚ (pos 2 ℤ+ pos 3 , 4)
   I = add-same-denom (pos 2 , 4) (pos 3 , 4)

2/5+3/5 : 2/5 + 3/5 ＝ 1ℚ
2/5+3/5 = I
 where
  abstract
   I : 2/5 + 3/5 ＝ 1ℚ
   I = 2/5+3/5-lemma ∙ equiv→equality (pos 5 , 4) (pos 1 , 0) refl

\end{code}
