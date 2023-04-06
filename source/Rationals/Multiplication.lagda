Andrew Sneap, January-March 2021
Updated January-March 2022

In this file I define multiplication of rationals, and prove
properties of multiplication.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Base hiding (_≈_)
open import Naturals.Properties
open import Integers.Abs
open import Integers.Type
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (_*_ to _ℚₙ*_ ; _+_ to _ℚₙ+_)
open import Rationals.Type
open import Rationals.Addition

module Rationals.Multiplication where

_*_ : ℚ → ℚ → ℚ
(p , _) * (q , _) = toℚ (p ℚₙ* q)

infixl 33 _*_

toℚ-* : (p q : ℚₙ) → toℚ (p ℚₙ* q) ＝ toℚ p * toℚ q
toℚ-* p q = equiv→equality (p ℚₙ* q) (p' ℚₙ* q') conclusion
 where
  p' = toℚₙ (toℚ p)
  q' = toℚₙ (toℚ q)

  I : p ≈ p'
  I = ≈-toℚ p

  II : q ≈ q'
  II = ≈-toℚ q

  III : p ℚₙ* q ≈ p' ℚₙ* q
  III = ≈-over-* p p' q I

  IV : q ℚₙ* p' ≈ q' ℚₙ* p'
  IV = ≈-over-* q q' p' II

  V : p' ℚₙ* q ≈ p' ℚₙ* q'
  V = transport₂ _≈_ (ℚₙ*-comm q p') (ℚₙ*-comm q' p') IV

  conclusion : p ℚₙ* q ≈ p' ℚₙ* q'
  conclusion = ≈-trans (p ℚₙ* q) (p' ℚₙ* q) (p' ℚₙ* q') III V

ℚ*-comm : (p q : ℚ) → p * q ＝ q * p
ℚ*-comm (p , _) (q , _) = ap toℚ (ℚₙ*-comm p q)

ℚ*-assoc : (p q r : ℚ) → p * q * r ＝ p * (q * r)
ℚ*-assoc (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) * (q , β) * (r , δ) ＝ (p , α) * ((q , β) * (r , δ))
  γ = (p , α) * (q , β) * (r , δ)   ＝⟨ refl ⟩
      toℚ (p ℚₙ* q) * (r , δ)       ＝⟨ i    ⟩
      toℚ (p ℚₙ* q) * toℚ r         ＝⟨ ii   ⟩
      toℚ (p ℚₙ* q ℚₙ* r)            ＝⟨ iii ⟩
      toℚ (p ℚₙ* (q ℚₙ* r))         ＝⟨ iv   ⟩
      toℚ p * toℚ (q ℚₙ* r)         ＝⟨ v    ⟩
      (p , α) * toℚ (q ℚₙ* r)       ＝⟨ refl ⟩
      (p , α) * ((q , β) * (r , δ)) ∎
   where
    i   = ap (toℚ (p ℚₙ* q) *_) (toℚ-toℚₙ (r , δ))
    ii  = toℚ-* (p ℚₙ* q) r ⁻¹
    iii = ap toℚ (ℚₙ*-assoc p q r)
    iv  = toℚ-* p (q ℚₙ* r)
    v   = ap (_* toℚ (q ℚₙ* r)) (toℚ-toℚₙ (p , α) ⁻¹)

ℚ-zero-left-is-zero : (q : ℚ) → 0ℚ * q ＝ 0ℚ
ℚ-zero-left-is-zero ((x , a) , q) = γ
 where
  γ : 0ℚ * ((x , a) , q) ＝ 0ℚ
  γ = 0ℚ * ((x , a) , q)             ＝⟨ i  ⟩
      toℚ (pos 0 , 0) * toℚ (x , a)  ＝⟨ ii ⟩
      toℚ ((pos 0 , 0) ℚₙ* (x , a))  ＝⟨ iii ⟩
      0ℚ ∎
   where
    iiiₐₚ : ((pos 0 , 0) ℚₙ* (x , a)) ≈ (pos 0 , 0)
    iiiₐₚ = ℚₙ-zero-left-is-zero (x , a)

    i   = ap (0ℚ *_) (toℚ-toℚₙ ((x , a) , q))
    ii  = toℚ-* (pos 0 , 0) (x , a) ⁻¹
    iii = equiv→equality ((pos 0 , 0) ℚₙ* (x , a)) (pos 0 , 0) iiiₐₚ

ℚ-zero-right-is-zero : (q : ℚ) → q * 0ℚ ＝ 0ℚ
ℚ-zero-right-is-zero q = ℚ*-comm q 0ℚ ∙ ℚ-zero-left-is-zero q

ℚ-mult-left-id : (q : ℚ) → 1ℚ * q ＝ q
ℚ-mult-left-id (q , α) = γ
 where
  γ : 1ℚ * (q , α) ＝ (q , α)
  γ = 1ℚ * (q , α)            ＝⟨ ap (toℚ (pos 1 , 0) *_) (toℚ-toℚₙ (q , α)) ⟩
      toℚ (pos 1 , 0) * toℚ q ＝⟨ toℚ-* (pos 1 , 0) q ⁻¹ ⟩
      toℚ ((pos 1 , 0) ℚₙ* q) ＝⟨ ap toℚ (ℚₙ-mult-left-id q) ⟩
      toℚ q                   ＝⟨ toℚ-toℚₙ (q , α) ⁻¹ ⟩
      (q , α)                 ∎

ℚ-mult-right-id : (q : ℚ) → q * 1ℚ ＝ q
ℚ-mult-right-id q = ℚ*-comm q 1ℚ ∙ ℚ-mult-left-id q

ℚ-distributivity : (p q r : ℚ) → p * (q + r) ＝ p * q + p * r
ℚ-distributivity (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) * ((q , β) + (r , δ)) ＝ (p , α) * (q , β) + (p , α) * (r , δ)
  γ = (p , α) * ((q , β) + (r , δ))          ＝⟨ refl ⟩
      (p , α) * toℚ (q ℚₙ+ r)                ＝⟨ i    ⟩
      toℚ p * toℚ (q ℚₙ+ r)                  ＝⟨ ii   ⟩
      toℚ (p ℚₙ* (q ℚₙ+ r))                   ＝⟨ iii ⟩
      toℚ (p ℚₙ* q ℚₙ+ p ℚₙ* r)               ＝⟨ iv  ⟩
      toℚ (p ℚₙ* q) + toℚ (p ℚₙ* r)          ＝⟨ v   ⟩
      toℚ (p ℚₙ* q) + toℚ p * toℚ r         ＝⟨ vi   ⟩
      toℚ p * toℚ q + toℚ p * toℚ r         ＝⟨ vii  ⟩
      (p , α) * toℚ q + (p , α) * toℚ r     ＝⟨ viii ⟩
      (p , α) * (q , β) + (p , α) * toℚ r   ＝⟨ ix   ⟩
      (p , α) * (q , β) + (p , α) * (r , δ) ∎
   where
    i    = ap (_* toℚ (q ℚₙ+ r)) (toℚ-toℚₙ (p , α))
    ii   = toℚ-* p (q ℚₙ+ r) ⁻¹
    iii  = equiv→equality (p ℚₙ* (q ℚₙ+ r)) (p ℚₙ* q ℚₙ+ p ℚₙ* r) (ℚₙ-dist p q r)
    iv   = toℚ-+ (p ℚₙ* q) (p ℚₙ* r)
    v    = ap (toℚ (p ℚₙ* q) +_) (toℚ-* p r)
    vi   = ap (_+ toℚ p * toℚ r) (toℚ-* p q)
    vii  = ap (λ - → - * toℚ q + - * toℚ r) (toℚ-toℚₙ (p , α) ⁻¹)
    viii = ap (λ - → (p , α) * - + (p , α) * toℚ r) (toℚ-toℚₙ (q , β) ⁻¹)
    ix   = ap (λ - → (p , α) * (q , β) + (p , α) * -) (toℚ-toℚₙ (r , δ) ⁻¹)

ℚ-distributivity' : (p q r : ℚ) → (q + r) * p ＝ q * p + r * p
ℚ-distributivity' p q r = γ
 where
  γ : (q + r) * p ＝ q * p + r * p
  γ = (q + r) * p   ＝⟨ ℚ*-comm (q + r) p                   ⟩
      p * (q + r)   ＝⟨ ℚ-distributivity p q r              ⟩
      p * q + p * r ＝⟨ ap₂ _+_ (ℚ*-comm p q) (ℚ*-comm p r) ⟩
      q * p + r * p ∎

multiplicative-inverse : (q : ℚ) → ¬ (q ＝ 0ℚ) → ℚ
multiplicative-inverse ((pos 0        , a) , p) nz = 𝟘-elim (nz γ)
 where
  γ : (pos 0 , a) , p ＝ 0ℚ
  γ = numerator-zero-is-zero (((pos 0 , a) , p)) refl
multiplicative-inverse ((pos (succ x) , a) , p) nz = toℚ ((pos (succ a)) , x)
multiplicative-inverse ((negsucc x , a) , p) nz = toℚ ((negsucc  a) , x)

division-by-self-is-one : ((x , a) : ℚₙ) → x ＝ pos (succ a) → toℚ (x , a) ＝ 1ℚ
division-by-self-is-one (negsucc x , a) e = 𝟘-elim (negsucc-not-pos e)
division-by-self-is-one (pos 0 , a) e = 𝟘-elim (zero-not-positive a γ)
 where
  γ : 0 ＝ succ a
  γ = pos-lc e
division-by-self-is-one (pos (succ x) , a) e = I II
 where
  I : (pos (succ x) , a) ≈ (pos 1 , 0)
    → toℚ (pos (succ x) , a) ＝ toℚ (pos 1 , 0)
  I = equiv→equality (pos (succ x) , a) (pos (succ 0) , 0)

  II : (pos (succ x) , a) ≈ (pos 1 , 0)
  II = pos (succ x)          ＝⟨ e                                ⟩
       pos (succ a)          ＝⟨ ℤ-mult-left-id (pos (succ a)) ⁻¹ ⟩
       pos 1 ℤ* pos (succ a) ∎

ℚ*-inverse-product-is-one : (q : ℚ) → (nz : ¬ (q ＝ 0ℚ)) → q * multiplicative-inverse q nz ＝ 1ℚ
ℚ*-inverse-product-is-one ((pos 0 , a) , p) nz = 𝟘-elim (nz γ)
 where
  γ : (pos 0 , a) , p ＝ 0ℚ
  γ = numerator-zero-is-zero ((pos 0 , a) , p) refl
ℚ*-inverse-product-is-one ((pos (succ x) , a) , p) nz = γ
 where
  ψ : pos (succ x) ℤ* pos (succ a) ＝ pos (succ (pred (succ a ℕ* succ x)))
  ψ = pos (succ x) ℤ* pos (succ a)         ＝⟨ ℤ*-comm (pos (succ x)) (pos (succ a)) ⟩
      pos (succ a) ℤ* pos (succ x)         ＝⟨ denom-setup a x ⁻¹                    ⟩
      pos (succ (pred (succ a ℕ* succ x))) ∎

  γ : ((pos (succ x) , a) , p) * toℚ ((pos (succ a)) , x) ＝ 1ℚ
  γ = ((pos (succ x) , a) , p) * toℚ ((pos (succ a)) , x)              ＝⟨ ap (_* toℚ (pos (succ a) , x)) (toℚ-toℚₙ (((pos (succ x) , a) , p))) ⟩
      toℚ (pos (succ x) , a) * toℚ (pos (succ a) , x)                  ＝⟨ toℚ-* (pos (succ x) , a) (pos (succ a) , x) ⁻¹                       ⟩
      toℚ ((pos (succ x) , a) ℚₙ* (pos (succ a) , x))                  ＝⟨ refl                                                                    ⟩
      toℚ ((pos (succ x) ℤ* pos (succ a)) , (pred (succ a ℕ* succ x))) ＝⟨ division-by-self-is-one ((pos (succ x) ℤ* pos (succ a)) , (pred (succ a ℕ* succ x))) ψ ⟩
      toℚ (pos 1 , 0)                                                  ＝⟨ refl                                                                    ⟩
      1ℚ                                                               ∎
ℚ*-inverse-product-is-one ((negsucc x    , a) , p) nz = γ
 where
  ψ : negsucc x ℤ* negsucc a ＝ pos (succ (pred (succ a ℕ* succ x)))
  ψ = negsucc x ℤ* negsucc a               ＝⟨ minus-times-minus-is-positive (pos (succ x)) (pos (succ a)) ⟩
      pos (succ x) ℤ* pos (succ a)         ＝⟨ ℤ*-comm (pos (succ x)) (pos (succ a))                       ⟩
      pos (succ a) ℤ* pos (succ x)         ＝⟨ denom-setup a x ⁻¹                                          ⟩
      pos (succ (pred (succ a ℕ* succ x))) ∎

  γ : ((negsucc x , a) , p) * toℚ ((negsucc  a) , x) ＝ 1ℚ
  γ = ((negsucc x , a) , p) * toℚ (negsucc a , x) ＝⟨ ap (_* toℚ (negsucc a , x)) (toℚ-toℚₙ ((negsucc x , a) , p))                 ⟩
      (toℚ (negsucc x , a) * toℚ (negsucc a , x)) ＝⟨ toℚ-* (negsucc x , a) (negsucc a , x) ⁻¹                                     ⟩
      toℚ ((negsucc x , a) ℚₙ* (negsucc a , x))   ＝⟨ division-by-self-is-one (negsucc x ℤ* negsucc a , pred (succ a ℕ* succ x)) ψ ⟩
      1ℚ                                          ∎

ℚ*-inverse : (q : ℚ) → ¬ (q ＝ 0ℚ) → Σ q' ꞉ ℚ , q * q' ＝ 1ℚ
ℚ*-inverse q nz = (multiplicative-inverse q nz) , ℚ*-inverse-product-is-one q nz

⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0         = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec 2/3 (_* 2/3) n

⟨2/3⟩-to-mult : (n : ℕ) → ⟨2/3⟩^ (succ n) ＝ (⟨2/3⟩^ n) * 2/3
⟨2/3⟩-to-mult 0 = f
 where
  abstract
   f : ⟨2/3⟩^ (succ 0) ＝ ((⟨2/3⟩^ 0) * 2/3)
   f = (ℚ-mult-left-id 2/3) ⁻¹
⟨2/3⟩-to-mult (succ n) = refl

⟨1/n⟩ : ℕ → ℚ
⟨1/n⟩ n = toℚ (pos 1 , n)

⟨1/sn⟩ : ℕ → ℚ
⟨1/sn⟩ 0 = 1ℚ
⟨1/sn⟩ (succ n) = ⟨1/n⟩ n

⟨1/n⟩-1 : ⟨1/n⟩ 0 ＝ 1ℚ
⟨1/n⟩-1 = equiv→equality (pos 1 , 0) (pos 1 , 0) refl

⟨1/n⟩-1/2 : ⟨1/n⟩ 1 ＝ 1/2
⟨1/n⟩-1/2 = equiv→equality (pos 1 , 1) (pos 1 , 1) refl

⟨1/2⟩^_ : ℕ → ℚ
⟨1/2⟩^ 0         = toℚ (pos 1 , 0)
⟨1/2⟩^ (succ n)  = rec (1/2) (_* 1/2) n

ℚ-into-half : (q : ℚ) → q ＝ q * 1/2 + q * 1/2
ℚ-into-half q = q                 ＝⟨ ℚ-mult-right-id q ⁻¹       ⟩
                q * 1ℚ            ＝⟨ ap (q *_) (1/2+1/2 ⁻¹)     ⟩
                q * (1/2 + 1/2)   ＝⟨ ℚ-distributivity q 1/2 1/2 ⟩
                q * 1/2 + q * 1/2 ∎

ℚ*-rearrange : (x y z : ℚ) → x * y * z ＝ x * z * y
ℚ*-rearrange x y z = x * y * z     ＝⟨ ℚ*-assoc x y z          ⟩
                     x * (y * z)   ＝⟨ ap (x *_) (ℚ*-comm y z) ⟩
                     x * (z * y)   ＝⟨ ℚ*-assoc x z y ⁻¹       ⟩
                     x * z * y     ∎

ℚ*-rearrange' : (x y z : ℚ) → x * y * z ＝ z * x * y
ℚ*-rearrange' x y z = x * y * z   ＝⟨ ℚ*-comm (x * y) z ⟩
                      z * (x * y) ＝⟨ ℚ*-assoc z x y ⁻¹ ⟩
                      z * x * y   ∎

half-of-quarter : 1/2 * 1/2 ＝ 1/4
half-of-quarter = toℚ-* (pos 1 , 1) (pos 1 , 1)

\end{code}
