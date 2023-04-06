Andrew Sneap, January-March 2021

In this file I define negation of real numbers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

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

ℚ+-inverse-lemma : ((x , a) : 𝔽) → ((ℤ- x , a) 𝔽+ (x , a)) ≈ (pos 0 , 0)
ℚ+-inverse-lemma (x , a) = I
 where
  I : ((ℤ- x , a) 𝔽+ (x , a)) ≈ (pos zero , zero)
  I = ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ℤ* pos 1 ＝⟨ ℤ-mult-right-id ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ⟩
      ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a)))          ＝⟨ distributivity-mult-over-ℤ (ℤ- x) x (pos (succ a)) ⁻¹ ⟩
      ((ℤ- x) ℤ+ x) ℤ* pos (succ a)                            ＝⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ+-comm (ℤ- x) x)  ⟩
      (x ℤ+ (ℤ- x)) ℤ* pos (succ a)                            ＝⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ-sum-of-inverse-is-zero x) ⟩
      pos 0 ℤ* pos (succ a)                                    ＝⟨ ℤ-zero-left-base (pos (succ a)) ⟩
      pos 0                                                    ＝⟨ ℤ-zero-left-base (pos (succ (pred (succ a ℕ* succ a)))) ⁻¹  ⟩
      pos zero ℤ* pos (succ (pred (succ a ℕ* succ a)))         ∎

ℚ-inverse-sum-to-zero : (q : ℚ) → q + (- q) ＝ 0ℚ
ℚ-inverse-sum-to-zero ((x , a) , p) = γ
 where
  -qnc : Σ (x' , y') ꞉ 𝔽 , toℚ (ℤ- x , a) ＝ toℚ (x' , y')
  -qnc = q-has-qn (toℚ (ℤ- x , a))

  x' : ℤ
  x' = pr₁ (pr₁ -qnc)

  y' : ℕ
  y' = pr₂ (pr₁ -qnc)

  I : ((x , a) 𝔽+ (x' , y')) ≈ (pos 0 , 0) → toℚ ((x , a) 𝔽+ (x' , y')) ＝ toℚ (pos 0 , 0)
  I = equiv→equality ((x , a) 𝔽+ (x' , y')) (pos 0 , 0)

  II : (x , a) 𝔽+ (x' , y') ≈ ((x' , y') 𝔽+ (x , a))
  II = transport ((x , a) 𝔽+ (x' , y') ≈_) (𝔽+-comm (x , a) (x' , y')) (≈-refl ((x , a) 𝔽+ (x' , y')))

  IIIᵢ : (x' , y') ≈ (ℤ- x , a)
  IIIᵢ = ≈-sym (ℤ- x , a) (x' , y') (equality→equiv (ℤ- x , a) (x' , y') (pr₂ -qnc))

  III : ((x' , y') 𝔽+ (x , a)) ≈ ((ℤ- x , a) 𝔽+ (x , a))
  III = ≈-addition (x' , y') (ℤ- x , a) (x , a) IIIᵢ

  IVᵢ : (x , a) 𝔽+ (x' , y') ≈ ((ℤ- x , a) 𝔽+ (x , a))
  IVᵢ = ≈-trans ((x , a) 𝔽+ (x' , y')) ((x' , y') 𝔽+ (x , a)) ((ℤ- x , a) 𝔽+ (x , a)) II III

  IV : ((ℤ- x , a) 𝔽+ (x , a)) ≈ (pos 0 , 0)
  IV = ℚ+-inverse-lemma (x , a)

  V : ((x , a) 𝔽+ (x' , y')) ≈ (pos 0 , 0)
  V = ≈-trans ((x , a) 𝔽+ (x' , y')) ((ℤ- x , a) 𝔽+ (x , a)) ((pos 0 , 0)) IVᵢ IV

  γ : (((x , a) , p) + (- ((x , a) , p))) ＝ 0ℚ
  γ = (((x , a) , p) + (- ((x , a) , p)))     ＝⟨ refl ⟩
      (((x , a) , p) + toℚ (ℤ- x , a))        ＝⟨ refl ⟩
      toℚ ((x , a) 𝔽+ (x' , y'))             ＝⟨ I V ⟩
      toℚ (pos 0 , 0)                         ＝⟨ refl ⟩
      0ℚ ∎

ℚ-inverse-sum-to-zero' : (q : ℚ) → (- q) + q ＝ 0ℚ
ℚ-inverse-sum-to-zero' q = ℚ+-comm (- q) q ∙ ℚ-inverse-sum-to-zero q

ℚ+-inverse : (q : ℚ) → Σ q' ꞉ ℚ , q + q' ＝ 0ℚ
ℚ+-inverse q = (- q) , (ℚ-inverse-sum-to-zero q)

ℚ+-inverse' : (q : ℚ) → Σ q' ꞉ ℚ , q' + q ＝ 0ℚ
ℚ+-inverse' q = f (ℚ+-inverse q)
  where
   f : Σ q' ꞉ ℚ , q + q' ＝ 0ℚ → Σ q' ꞉ ℚ , q' + q ＝ 0ℚ
   f (q' , e) = q' , (ℚ+-comm q' q ∙ e)

ℚ-minus-minus : (p : ℚ) → p ＝ (- (- p))
ℚ-minus-minus p = IV
 where
  p-constructed : Σ (x , a) ꞉ 𝔽 , p ＝ toℚ (x , a)
  p-constructed = q-has-qn p

  x = pr₁ (pr₁ p-constructed)
  a = pr₂ (pr₁ p-constructed)

  I : (- toℚ (x , a)) ＝ toℚ (ℤ- x , a)
  I = toℚ-neg (x , a)

  II : - toℚ (ℤ- x , a) ＝ toℚ ((ℤ- (ℤ- x)) , a)
  II = toℚ-neg (ℤ- x , a)

  III : toℚ ((ℤ- (ℤ- x)) , a) ＝ toℚ (x , a)
  III = ap (λ k → toℚ (k , a)) (minus-minus-is-plus x)

  IV : p ＝ (- (- p))
  IV = p                     ＝⟨ pr₂ p-constructed ⟩
       toℚ (x , a)           ＝⟨ III ⁻¹ ⟩
       toℚ (ℤ- (ℤ- x) , a)   ＝⟨ II ⁻¹ ⟩
       (- toℚ (ℤ- x , a))    ＝⟨ ap -_ (I ⁻¹) ⟩
       (- (- toℚ (x , a)))   ＝⟨ ap (λ k → - (- k)) (pr₂ p-constructed ⁻¹) ⟩
       (- (- p)) ∎

ℚ-add-zero : (x y z : ℚ) → (x + y) ＝ ((x - z) + (z + y))
ℚ-add-zero x y z = I
 where
  I : (x + y) ＝ ((x - z) + (z + y))
  I = (x + y)                    ＝⟨ ap (_+ y) (ℚ-zero-right-neutral x ⁻¹) ⟩
      ((x + 0ℚ) + y)             ＝⟨ ap (λ k → (x + k) + y) (ℚ-inverse-sum-to-zero' z ⁻¹) ⟩
      ((x + ((- z) + z)) + y)    ＝⟨ ap (_+ y) (ℚ+-assoc x (- z) z ⁻¹) ⟩
      (((x + (- z)) + z) + y)    ＝⟨ ℚ+-assoc (x - z) z y ⟩
      ((x - z) + (z + y)) ∎

ℚ-negation-dist-over-mult : (p q : ℚ) → (- p) * q ＝ - (p * q)
ℚ-negation-dist-over-mult ((x , a) , α) ((y , b) , β) = I
 where
  xa : Σ (x' , a') ꞉ 𝔽 , ((x , a) , α) ＝ toℚ (x' , a')
  xa = q-has-qn ((x , a) , α)
  yb : Σ (y' , b') ꞉ 𝔽 , ((y , b) , β) ＝ toℚ (y' , b')
  yb = q-has-qn ((y , b) , β)
  x' = pr₁ (pr₁ xa)
  a' = pr₂ (pr₁ xa)
  y' = pr₁ (pr₁ yb)
  b' = pr₂ (pr₁ yb)

  II : ((𝔽- (x' , a')) 𝔽* (y' , b')) ≈ (𝔽- ((x' , a') 𝔽* (y' , b')))
  II = 𝔽-subtraction-dist-over-mult (x' , a') (y' , b')

  I : (- ((x , a) , α)) * ((y , b) , β) ＝ - ((x , a) , α) * ((y , b) , β)
  I = (- ((x , a) , α)) * ((y , b) , β)    ＝⟨ ap (λ z → (- ((x , a) , α)) * z) (pr₂ yb) ⟩
      toℚ (𝔽- (x , a)) * toℚ (y' , b')     ＝⟨ toℚ-* (𝔽- (x , a)) (y' , b') ⁻¹ ⟩
      toℚ ((𝔽- (x' , a')) 𝔽* (y' , b'))   ＝⟨ equiv→equality ((𝔽- (x' , a')) 𝔽* (y' , b')) (𝔽- ((x' , a') 𝔽* (y' , b'))) II ⟩
      toℚ (𝔽- ((x' , a') 𝔽* (y' , b')))   ＝⟨ toℚ-neg ((x' , a') 𝔽* (y' , b')) ⁻¹ ⟩
      - toℚ ((x' , a') 𝔽* (y' , b'))      ＝⟨ ap -_ (toℚ-* (x' , a') (y' , b')) ⟩
      - toℚ (x' , a') * toℚ (y' , b')      ＝⟨ ap₂ (λ z z' → - (z * z')) (pr₂ xa ⁻¹) (pr₂ yb ⁻¹) ⟩
      - ((x , a) , α) * ((y , b) , β)      ∎

toℚ-subtraction : (p q : 𝔽) → toℚ p - toℚ q ＝ toℚ (p 𝔽+ (𝔽- q))
toℚ-subtraction p q = II
 where
  I : toℚ (p 𝔽+ (𝔽- q)) ＝ toℚ p + toℚ (𝔽- q)
  I = toℚ-+ p (𝔽- q)
  II : toℚ p - toℚ q ＝ toℚ (p 𝔽+ (𝔽- q))
  II = toℚ p - toℚ q       ＝⟨ ap (toℚ p +_) (toℚ-neg q) ⟩
       toℚ p + toℚ (𝔽- q) ＝⟨ I ⁻¹ ⟩
       toℚ (p 𝔽+ (𝔽- q)) ∎

1-2/5＝3/5 : 1ℚ - 2/5 ＝ 3/5
1-2/5＝3/5 = 1ℚ - 2/5              ＝⟨ ap (λ α → α - 2/5) (2/5+3/5 ⁻¹) ⟩
               2/5 + 3/5 - 2/5       ＝⟨ ℚ+-assoc 2/5 3/5 (- 2/5) ⟩
               2/5 + (3/5 - 2/5)     ＝⟨ ap (2/5 +_) (ℚ+-comm 3/5 (- 2/5)) ⟩
               2/5 + ((- 2/5) + 3/5) ＝⟨ ℚ+-assoc 2/5 (- 2/5) 3/5 ⁻¹ ⟩
               2/5 - 2/5 + 3/5       ＝⟨ ap (_+ 3/5) (ℚ-inverse-sum-to-zero 2/5) ⟩
               0ℚ + 3/5              ＝⟨ ℚ-zero-left-neutral 3/5 ⟩
               3/5                   ∎


ℚ-inverse-intro : (p q : ℚ) → p ＝ p + (q - q)
ℚ-inverse-intro p q = p           ＝⟨ ℚ-zero-right-neutral p ⁻¹ ⟩
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
