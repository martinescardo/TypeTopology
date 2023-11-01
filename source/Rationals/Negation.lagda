Andrew Sneap, January-March 2021

In this file I define negation of real numbers.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Base hiding (_≈_)
open import UF.FunExt
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (-_ to 𝔽-_ ; _+_ to _𝔽+_ ; _*_ to _𝔽*_)
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Multiplication

module Rationals.Negation where

-_ : ℚ → ℚ
- ((x , a) , p) = toℚ (𝔽- (x , a))

infix 32 -_

_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

infixl 32 _-_

ℚ-minus-zero-is-zero : 0ℚ ＝ - 0ℚ
ℚ-minus-zero-is-zero = refl

toℚ-neg : ((x , a) : 𝔽) → (- toℚ (x , a)) ＝ toℚ (𝔽- (x , a))
toℚ-neg (x , a) = equiv→equality (ℤ- x' , a') (𝔽- (x , a)) γ
 where
  x'  = numℚ (x , a)
  a'  = dnomℚ (x , a)
  pa  = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'

  γ : (ℤ- x' , a') ≈ (𝔽- (x , a))
  γ = (ℤ- x') ℤ* pa ＝⟨ negation-dist-over-mult' x' pa    ⟩
      ℤ- x' ℤ* pa   ＝⟨ ap ℤ-_ (≈-toℚ (x , a) ⁻¹)         ⟩
      ℤ- x ℤ* pa'   ＝⟨ negation-dist-over-mult' x pa' ⁻¹ ⟩
      (ℤ- x) ℤ* pa' ∎

ℚ-minus-dist : (p q : ℚ) → (- p) + (- q) ＝ - (p + q)
ℚ-minus-dist ((x , a) , p) ((y , b) , q) = γ
 where
  iiₐₚ : (ℤ- x , a) 𝔽+ (ℤ- y , b) ≈ (𝔽- ((x , a) 𝔽+ (y , b)))
  iiₐₚ = 𝔽-minus-dist (x , a) (y , b)

  i   = toℚ-+ (ℤ- x , a) (ℤ- y , b) ⁻¹
  ii  = equiv→equality ((ℤ- x , a) 𝔽+ (ℤ- y , b)) (𝔽- ((x , a) 𝔽+ (y , b))) iiₐₚ
  iii = toℚ-neg ((x , a) 𝔽+ (y , b)) ⁻¹

  γ : (- ((x , a) , p)) - ((y , b) , q) ＝ - (((x , a) , p) + ((y , b) , q))
  γ = (- ((x , a) , p)) - ((y , b) , q) ＝⟨ refl ⟩
      toℚ (ℤ- x , a) + toℚ (ℤ- y , b)   ＝⟨ i    ⟩
      toℚ ((ℤ- x , a) 𝔽+ (ℤ- y , b))    ＝⟨ ii   ⟩
      toℚ (𝔽- ((x , a) 𝔽+ (y , b)))     ＝⟨ iii  ⟩
      - toℚ ((x , a) 𝔽+ (y , b))        ＝⟨ refl ⟩
      - (((x , a) , p) + ((y , b) , q)) ∎

ℚ-inverse-sum-to-zero : (q : ℚ) → q - q ＝ 0ℚ
ℚ-inverse-sum-to-zero ((x , a) , p) = γ
 where
  I : ((x , a) 𝔽+ (𝔽- (x , a))) ≈ (pos 0 , 0)
    → toℚ ((x , a) 𝔽+ (𝔽- (x , a))) ＝ toℚ (pos 0 , 0)
  I = equiv→equality ((x , a) 𝔽+ (𝔽- (x , a))) (pos 0 , 0)

  γ : ((x , a) , p) - ((x , a) , p) ＝ 0ℚ
  γ = ((x , a) , p) - ((x , a) , p)  ＝⟨ i   ⟩
      toℚ (x , a) - toℚ (x , a)      ＝⟨ ii  ⟩
      toℚ (x , a) + toℚ (𝔽- (x , a)) ＝⟨ iii ⟩
      toℚ ((x , a) 𝔽+ (𝔽- (x , a)))  ＝⟨ iv  ⟩
      0ℚ ∎
   where
    i   = ap (λ z → z - z) (toℚ-to𝔽 ((x , a) , p))
    ii  = ap (toℚ (x , a) +_) (toℚ-neg (x , a))
    iii = toℚ-+ (x , a) (𝔽- (x , a)) ⁻¹
    iv  = I (𝔽+-inverse' (x , a))

ℚ-inverse-sum-to-zero' : (q : ℚ) → (- q) + q ＝ 0ℚ
ℚ-inverse-sum-to-zero' q = ℚ+-comm (- q) q ∙ ℚ-inverse-sum-to-zero q

ℚ+-inverse : (q : ℚ) → Σ q' ꞉ ℚ , q + q' ＝ 0ℚ
ℚ+-inverse q = (- q) , (ℚ-inverse-sum-to-zero q)

ℚ+-inverse' : (q : ℚ) → Σ q' ꞉ ℚ , q' + q ＝ 0ℚ
ℚ+-inverse' q = f (ℚ+-inverse q)
  where
   f : Σ q' ꞉ ℚ , q + q' ＝ 0ℚ → Σ q' ꞉ ℚ , q' + q ＝ 0ℚ
   f (q' , e) = q' , (ℚ+-comm q' q ∙ e)

ℚ-minus-minus : (p : ℚ) → p ＝ - (- p)
ℚ-minus-minus ((x , a) , α) = γ
 where
  γ : ((x , a) , α) ＝ - (- ((x , a) , α))
  γ = ((x , a) , α)         ＝⟨ i    ⟩
      toℚ (x , a)           ＝⟨ ii   ⟩
      toℚ (ℤ- (ℤ- x) , a)   ＝⟨ refl ⟩
      toℚ (𝔽- (𝔽- (x , a))) ＝⟨ iii  ⟩
      - toℚ (𝔽- (x , a))    ＝⟨ iv   ⟩
      - (- toℚ (x , a))     ＝⟨ v    ⟩
      - (- ((x , a) , α))   ∎
   where
    i   = toℚ-to𝔽 ((x , a) , α)
    ii  = ap (λ z → toℚ (z , a)) (minus-minus-is-plus x ⁻¹)
    iii = toℚ-neg (𝔽- (x , a)) ⁻¹
    iv  = ap -_ (toℚ-neg (x , a) ⁻¹)
    v   = ap (-_ ∘ -_) (toℚ-to𝔽 ((x , a) , α) ⁻¹)

ℚ-minus-dist' : (p q : ℚ) → - (p - q) ＝ q - p
ℚ-minus-dist' p q = γ
 where
  γ : - (p - q) ＝ q - p
  γ = - (p - q)     ＝⟨ ℚ-minus-dist p (- q) ⁻¹            ⟩
      (- p) - (- q) ＝⟨ ap ((- p) +_) (ℚ-minus-minus q ⁻¹) ⟩
      (- p) + q     ＝⟨ ℚ+-comm (- p) q                    ⟩
      q - p         ∎

ℚ-minus-dist'' : (p q : ℚ) → p - q ＝ - (q - p)
ℚ-minus-dist'' p q = ℚ-minus-dist' q p ⁻¹

ℚ-add-zero : (x y z : ℚ) → (x + y) ＝ (x - z) + (z + y)
ℚ-add-zero x y z = γ
 where
  i   = ap (_+ y) (ℚ-zero-right-neutral x ⁻¹)
  ii  = ap (λ k → (x + k) + y) (ℚ-inverse-sum-to-zero' z ⁻¹)
  iii = ap (_+ y) (ℚ+-assoc x (- z) z ⁻¹)
  iv  = ℚ+-assoc (x - z) z y

  γ : (x + y) ＝ (x - z) + (z + y)
  γ = (x + y)             ＝⟨ i   ⟩
      (x + 0ℚ) + y        ＝⟨ ii  ⟩
      x + ((- z) + z) + y ＝⟨ iii ⟩
      x + (- z) + z + y   ＝⟨ iv  ⟩
      (x - z) + (z + y)   ∎

ℚ-negation-dist-over-mult : (p q : ℚ) → (- p) * q ＝ - (p * q)
ℚ-negation-dist-over-mult ((x , a) , α) ((y , b) , β) = γ
 where
  I : ((𝔽- (x , a)) 𝔽* (y , b)) ≈ (𝔽- ((x , a) 𝔽* (y , b)))
    → toℚ ((𝔽- (x , a)) 𝔽* (y , b)) ＝ toℚ (𝔽- ((x , a) 𝔽* (y , b)))
  I = equiv→equality ((𝔽- (x , a)) 𝔽* (y , b)) (𝔽- ((x , a) 𝔽* (y , b)))

  i   = ap (toℚ (𝔽- (x , a)) *_) (toℚ-to𝔽 ((y , b) , β))
  ii  = toℚ-* (𝔽- (x , a)) (y , b) ⁻¹
  iii = I (𝔽-subtraction-dist-over-mult (x , a) (y , b))
  iv  = toℚ-neg ((x , a) 𝔽* (y , b)) ⁻¹

  γ : (- ((x , a) , α)) * ((y , b) , β) ＝ - ((x , a) , α) * ((y , b) , β)
  γ = (- ((x , a) , α)) * ((y , b) , β) ＝⟨ refl ⟩
      toℚ (𝔽- (x , a)) * ((y , b) , β)  ＝⟨ i    ⟩
      toℚ (𝔽- (x , a)) * toℚ (y , b)    ＝⟨ ii   ⟩
      toℚ ((𝔽- (x , a)) 𝔽* (y , b))     ＝⟨ iii  ⟩
      toℚ (𝔽- ((x , a) 𝔽* (y , b)))     ＝⟨ iv   ⟩
      - toℚ ((x , a) 𝔽* (y , b))        ＝⟨ refl ⟩
      - ((x , a) , α) * ((y , b) , β)   ∎

ℚ-negation-dist-over-mult' : (p q : ℚ) → p * (- q) ＝ - (p * q)
ℚ-negation-dist-over-mult' p q = γ
 where
  γ : p * (- q) ＝ - p * q
  γ = p * (- q) ＝⟨ ℚ*-comm p (- q)               ⟩
      (- q) * p ＝⟨ ℚ-negation-dist-over-mult q p ⟩
      - q * p   ＝⟨ ap -_ (ℚ*-comm q p)           ⟩
      - p * q   ∎

ℚ-negation-dist-over-mult'' : (p q : ℚ) → p * (- q) ＝ (- p) * q
ℚ-negation-dist-over-mult'' p q = γ
 where
  γ : p * (- q) ＝ (- p) * q
  γ = p * (- q) ＝⟨ ℚ-negation-dist-over-mult' p q   ⟩
      - p * q   ＝⟨ ℚ-negation-dist-over-mult p q ⁻¹ ⟩
      (- p) * q ∎

toℚ-subtraction : (p q : 𝔽) → toℚ p - toℚ q ＝ toℚ (p 𝔽+ (𝔽- q))
toℚ-subtraction p q = γ
 where
  γ : toℚ p - toℚ q ＝ toℚ (p 𝔽+ (𝔽- q))
  γ = toℚ p - toℚ q      ＝⟨ ap (toℚ p +_) (toℚ-neg q) ⟩
      toℚ p + toℚ (𝔽- q) ＝⟨ toℚ-+ p (𝔽- q) ⁻¹         ⟩
      toℚ (p 𝔽+ (𝔽- q))  ∎

ℚ-inverse-intro : (p q : ℚ) → p ＝ p + (q - q)
ℚ-inverse-intro p q = p           ＝⟨ ℚ-zero-right-neutral p ⁻¹              ⟩
                      p + 0ℚ      ＝⟨ ap (p +_) (ℚ-inverse-sum-to-zero q ⁻¹) ⟩
                      p + (q - q) ∎

ℚ-inverse-intro'' : (p q : ℚ) → p ＝ p + q - q
ℚ-inverse-intro'' p q = ℚ-inverse-intro p q ∙ ℚ+-assoc p q (- q) ⁻¹

ℚ-inverse-intro' : (p q : ℚ) → p ＝ (q - q) + p
ℚ-inverse-intro' p q = ℚ-inverse-intro p q ∙ ℚ+-comm p (q - q)

ℚ-inverse-intro''' : (p q : ℚ) → p ＝ p + ((- q) + q)
ℚ-inverse-intro''' p q = ℚ-inverse-intro p q ∙ ap (p +_) (ℚ+-comm q (- q))

ℚ-inverse-intro'''' : (p q : ℚ) → p ＝ p - q + q
ℚ-inverse-intro'''' p q = ℚ-inverse-intro''' p q ∙ ℚ+-assoc p (- q) q ⁻¹

1-2/3 : 1ℚ - 2/3 ＝ 1/3
1-2/3 = refl

1-1/3 : 1ℚ - 1/3 ＝ 2/3
1-1/3 = refl

1-2/5＝3/5 : 1ℚ - 2/5 ＝ 3/5
1-2/5＝3/5 = refl

1-1/2 : 1ℚ - 1/2 ＝ 1/2
1-1/2 = refl

1/2-1 : 1/2 - 1ℚ ＝ - 1/2
1/2-1 = refl

ℚ-minus-half : (p : ℚ) → p - 1/2 * p ＝ 1/2 * p
ℚ-minus-half p
 = p - 1/2 * p          ＝⟨ ap (_- 1/2 * p) (ℚ-mult-left-id p ⁻¹)               ⟩
   1ℚ * p - 1/2 * p     ＝⟨ ap (1ℚ * p +_) (ℚ-negation-dist-over-mult 1/2 p ⁻¹) ⟩
   1ℚ * p + (- 1/2) * p ＝⟨ ℚ-distributivity' p 1ℚ (- 1/2) ⁻¹                   ⟩
   (1ℚ - 1/2) * p       ＝⟨ refl                                                ⟩
   1/2 * p              ∎

ℚ+-right-cancellable : (p q r : ℚ) → p + r ＝ q + r → p ＝ q
ℚ+-right-cancellable p q r e = γ
 where
  γ : p ＝ q
  γ = p         ＝⟨ ℚ-inverse-intro'' p r    ⟩
      p + r - r ＝⟨ ap (_- r) e              ⟩
      q + r - r ＝⟨ ℚ-inverse-intro'' q r ⁻¹ ⟩
      q         ∎

ℚ-add-zero-twice'' : (p q r : ℚ) → p ＝ p + q + r - q - r
ℚ-add-zero-twice'' p q r = γ
 where
  γ : p ＝ p + q + r - q - r
  γ = p                   ＝⟨ ℚ-inverse-intro'' p q                        ⟩
      p + q - q           ＝⟨ ap (λ ■ → p + ■ - q) (ℚ-inverse-intro'' q r) ⟩
      p + (q + r - r) - q ＝⟨ ap (_- q) (ℚ+-assoc p (q + r) (- r) ⁻¹)      ⟩
      p + (q + r) - r - q ＝⟨ ap (λ ■ → ■ - r - q) (ℚ+-assoc p q r ⁻¹)     ⟩
      p + q + r - r - q   ＝⟨ ℚ+-rearrange (p + q + r) (- q) (- r) ⁻¹      ⟩
      p + q + r - q - r   ∎

ℚ-add-zero-twice''' : (p q r : ℚ) → p ＝ p - q - r + q + r
ℚ-add-zero-twice''' p q r = γ
 where
  γ : p ＝ p - q - r + q + r
  γ = p                         ＝⟨ ℚ-add-zero-twice'' p q r                    ⟩
      p + q + r - q - r         ＝⟨ ℚ+-assoc (p + q + r) (- q) (- r)            ⟩
      p + q + r + ((- q) - r)   ＝⟨ ap (_+ ((- q) - r)) (ℚ+-assoc p q r)        ⟩
      p + (q + r) + ((- q) - r) ＝⟨ ℚ+-rearrange p (q + r) ((- q) - r)          ⟩
      p + ((- q) - r) + (q + r) ＝⟨ ap (_+ (q + r)) (ℚ+-assoc p (- q) (- r) ⁻¹) ⟩
      p - q - r + (q + r)       ＝⟨ ℚ+-assoc (p - q - r) q r ⁻¹                 ⟩
      p - q - r + q + r         ∎

ℚ-add-zero-twice : (p q : ℚ) → p ＝ p - q - q + q + q
ℚ-add-zero-twice p q = ℚ-add-zero-twice''' p q q

ℚ-add-zero-twice' : (p q : ℚ) → p ＝ p + q + q - q - q
ℚ-add-zero-twice' p q = ℚ-add-zero-twice'' p q q

\end{code}
