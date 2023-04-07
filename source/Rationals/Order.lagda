Andrew Sneap, January-March 2021
Updated November 2021

In this file I define order of rationals, and prove many properties of order.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Properties
open import Notation.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import MLTT.Plus-Properties
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Type
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (_+_ to _𝔽+_ ; _*_ to _𝔽*_) hiding (-_)
open import Rationals.FractionsOrder
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation

module Rationals.Order where

_≤ℚ_ : (p q : ℚ) → 𝓤₀ ̇
(p , _) ≤ℚ (q , _) = p 𝔽≤ q

instance
 Order-ℚ-ℚ : Order ℚ ℚ
 _≤_ {{Order-ℚ-ℚ}} = _≤ℚ_

ℚ≤-is-prop : (p q : ℚ) → is-prop (p ≤ q)
ℚ≤-is-prop (p , _) (q , _) = 𝔽≤-is-prop p q

_<ℚ_ : (p q : ℚ) → 𝓤₀ ̇
(p , _) <ℚ (q , _) = p 𝔽< q

instance
 Strict-Order-ℚ-ℚ : Strict-Order ℚ ℚ
 _<_ {{Strict-Order-ℚ-ℚ}} = _<ℚ_

ℚ<-is-prop : (p q : ℚ) → is-prop (p < q)
ℚ<-is-prop (p , _) (q , _) = 𝔽<-is-prop p q

ℚ<-trans : (p q r : ℚ) → p < q → q < r → p < r
ℚ<-trans (p , _) (q , _) (r , _) α β = 𝔽<-trans p q r α β

ℚ≤-refl : (q : ℚ) → q ≤ q
ℚ≤-refl q = 0 , by-definition

ℚ<-coarser-than-≤ : (p q : ℚ) → p < q → p ≤ q
ℚ<-coarser-than-≤ (p , _) (q , _) l = 𝔽<-coarser-than-≤ p q l

toℚ-< : (p q : 𝔽) → p 𝔽< q → toℚ p < toℚ q
toℚ-< (x , a) (y , b) l = γ
 where
  x' = numℚ (x , a)
  a' = dnomℚ (x , a)
  h  = hcf𝔽 (x , a)
  y' = numℚ (y , b)
  b' = dnomℚ (y , b)
  h' = hcf𝔽 (y , b)
  pb' = (pos ∘ succ) b'
  pa' = (pos ∘ succ) a'
  ph  = (pos ∘ succ) h
  pb  = (pos ∘ succ) b
  ph' = (pos ∘ succ) h'
  pa  = (pos ∘ succ) a

  I : is-pos-succ (ph ℤ* ph')
  I = is-pos-succ-mult ph ph' ⋆ ⋆

  lemma : (p q r s : ℤ) → p ℤ* q ℤ* (r ℤ* s) ＝ q ℤ* s ℤ* (p ℤ* r)
  lemma p q r s = p ℤ* q ℤ* (r ℤ* s)   ＝⟨ i   ⟩
                  q ℤ* p ℤ* (r ℤ* s)   ＝⟨ ii  ⟩
                  q ℤ* (p ℤ* (r ℤ* s)) ＝⟨ iii ⟩
                  q ℤ* (p ℤ* (s ℤ* r)) ＝⟨ iv  ⟩
                  q ℤ* (p ℤ* s ℤ* r)   ＝⟨ v   ⟩
                  q ℤ* (s ℤ* p ℤ* r)   ＝⟨ vi  ⟩
                  q ℤ* (s ℤ* (p ℤ* r)) ＝⟨ vii ⟩
                  q ℤ* s ℤ* (p ℤ* r)   ∎
   where
    i   = ap (_ℤ* (r ℤ* s)) (ℤ*-comm p q)
    ii  = ℤ*-assoc q p (r ℤ* s)
    iii = ap (λ - → q ℤ* (p ℤ* -)) (ℤ*-comm r s)
    iv  = ap (q ℤ*_) (ℤ*-assoc p s r ⁻¹)
    v   = ap (λ - → q ℤ* (- ℤ* r)) (ℤ*-comm p s)
    vi  = ap (q ℤ*_) (ℤ*-assoc s p r)
    vii = ℤ*-assoc q s (p ℤ* r) ⁻¹

  II : x ℤ* pb ＝ x' ℤ* pb' ℤ* (ph ℤ* ph')
  II = x ℤ* pb                  ＝⟨ ap (_ℤ* pb) (numr (x , a))          ⟩
       ph ℤ* x' ℤ* pb           ＝⟨ ap (ph ℤ* x' ℤ*_) (dnomrP' (y , b)) ⟩
       ph ℤ* x' ℤ* (ph' ℤ* pb') ＝⟨ lemma ph x' ph' pb'                 ⟩
       x' ℤ* pb' ℤ* (ph ℤ* ph') ∎

  III : y ℤ* pa ＝ y' ℤ* pa' ℤ* (ph ℤ* ph')
  III = y ℤ* pa                  ＝⟨ ap (_ℤ* pa) (numr (y , b))           ⟩
        ph' ℤ* y' ℤ* pa          ＝⟨ ap (ph' ℤ* y' ℤ*_) (dnomrP' (x , a)) ⟩
        ph' ℤ* y' ℤ* (ph ℤ* pa') ＝⟨ lemma ph' y' ph pa'                  ⟩
        y' ℤ* pa' ℤ* (ph' ℤ* ph) ＝⟨ ap (y' ℤ* pa' ℤ*_) (ℤ*-comm ph' ph)  ⟩
        y' ℤ* pa' ℤ* (ph ℤ* ph') ∎

  γ' : x' ℤ* pb' ℤ* (ph ℤ* ph') < y' ℤ* pa' ℤ* (ph ℤ* ph')
  γ' = transport₂ _<_ II III l

  γ : x' ℤ* pb' < y' ℤ* pa'
  γ = ordering-right-cancellable (x' ℤ* pb') (y' ℤ* pa') (ph ℤ* ph') I γ'

toℚ-≤ : (p q : 𝔽) → p 𝔽≤ q → toℚ p ≤ toℚ q
toℚ-≤ (x , a) (y , b) l = Cases I II III
 where
  pa = (pos ∘ succ) a
  pb = (pos ∘ succ) b

  I : x ℤ* pb < y ℤ* pa ∔ (x ℤ* pb ＝ y ℤ* pa)
  I = ℤ≤-split (x ℤ* pb) (y ℤ* pa) l

  II : x ℤ* pb < y ℤ* pa → toℚ (x , a) ≤ toℚ (y , b)
  II l = ℚ<-coarser-than-≤ (toℚ (x , a)) (toℚ (y , b)) l'
   where
    l' : toℚ (x , a) < toℚ (y , b)
    l' = toℚ-< (x , a) (y , b) l

  III : x ℤ* pb ＝ y ℤ* pa → toℚ (x , a) ≤ toℚ (y , b)
  III e = transport (toℚ (x , a) ≤_) e' (ℚ≤-refl (toℚ (x , a)))
   where
    e' : toℚ (x , a) ＝ toℚ (y , b)
    e' = equiv→equality (x , a) (y , b) e

ℚ-no-max-element : (p : ℚ) → Σ q ꞉ ℚ , (p < q)
ℚ-no-max-element ((x , a) , α) = q , III
 where
  q : ℚ
  q = toℚ (succℤ x , a)

  x' : ℤ
  x' = pr₁ (pr₁ q)
  a' : ℕ
  a'  = pr₂ (pr₁ q)
  pa  = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'

  I : succℤ x ℤ* pa' ＝ x' ℤ* pa
  I = ≈-toℚ (succℤ x , a)

  II : x ℤ* pa' < succℤ x ℤ* pa'
  II = positive-multiplication-preserves-order x (succℤ x) pa' ⋆ (<-incrℤ x)

  III : x ℤ* pa' < x' ℤ* pa
  III = transport (x ℤ* pa' <_) I II

ℚ-no-least-element : (q : ℚ) → Σ p ꞉ ℚ , p < q
ℚ-no-least-element ((x , a) , α) = p , III
 where
  p : ℚ
  p = toℚ ((predℤ x) , a)

  x' : ℤ
  x' = pr₁ (pr₁ p)
  a' : ℕ
  a' = pr₂ (pr₁ p)

  pa = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'

  I : predℤ x ℤ* pa' ＝ x' ℤ* pa
  I = ≈-toℚ (predℤ x , a)

  II : predℤ x ℤ* pa' < x ℤ* pa'
  II = positive-multiplication-preserves-order (predℤ x) x pa' ⋆ (<-predℤ x)

  III : x' ℤ* pa < (x ℤ* pa')
  III = transport (_< x ℤ* pa') I II

ℚ-trichotomous : (p q : ℚ) → (p < q) ∔ (p ＝ q) ∔ (q < p)
ℚ-trichotomous ((x , a) , α) ((y , b) , β) =
 γ (ℤ-trichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a)))
 where
  γ : (x ℤ* pos (succ b)) < (y ℤ* pos (succ a))
     ∔ (x ℤ* pos (succ b) ＝ y ℤ* pos (succ a))
     ∔ (y ℤ* pos (succ a)) < (x ℤ* pos (succ b))
    →  ((x , a) , α) < ((y , b) , β)
     ∔ ((x , a) , α ＝ (y , b) , β)
     ∔ ((y , b) , β) < ((x , a) , α)
  γ (inl z)       = inl z
  γ (inr (inr z)) = inr (inr z)
  γ (inr (inl z)) = inr (inl γ')
   where
    I : x , a ＝ y , b
    I = equiv-with-lowest-terms-is-equal (x , a) (y , b) z α β

    γ' : (x , a) , α ＝ (y , b) , β
    γ' = to-subtype-＝ is-in-lowest-terms-is-prop I

ℚ-dichotomous : (p q : ℚ) → p ≤ q ∔ q ≤ p
ℚ-dichotomous ((x , a) , α) ((y , b) , β) = γ
 where
  γ : ((x , a) , α) ≤ ((y , b) , β) ∔ ((y , b) , β) ≤ ((x , a) , α)
  γ = ℤ-dichotomous (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

ℚ-dichotomous' : (p q : ℚ) → p < q ∔ q ≤ p
ℚ-dichotomous' p q = γ (ℚ-trichotomous p q)
 where
  γ : p < q ∔ (p ＝ q) ∔ q < p → p < q ∔ q ≤ p
  γ (inl l) = inl l
  γ (inr (inl e)) = inr (transport (_≤ p) e (ℚ≤-refl p))
  γ (inr (inr l)) = inr (ℚ<-coarser-than-≤ q p l)

located-property : (p q x : ℚ) → p < q → (p < x) ∔ (x < q)
located-property p q x l = γ (ℚ-trichotomous x q)
 where
  γ : (x < q) ∔ (x ＝ q) ∔ (q < x) → (p < x) ∔ (x < q)
  γ (inl z)       = inr z
  γ (inr (inl z)) = inl (transport (p <_) (z ⁻¹) l)
  γ (inr (inr z)) = inl (ℚ<-trans p q x l z)

half-𝔽 : 𝔽 → 𝔽
half-𝔽 (x , a) = x , succ (2 ℕ* a)

rounded-lemma₀ : (a : ℕ) → succ (2 ℕ* pred (succ a)) ＝ pred (2 ℕ* (succ a))
rounded-lemma₀ 0 = refl
rounded-lemma₀ (succ a) =
 succ (2 ℕ* pred (succ (succ a))) ＝⟨ i    ⟩
 succ (2 ℕ* succ a)               ＝⟨ ii   ⟩
 pred (succ (succ (2 ℕ* succ a))) ＝⟨ refl ⟩
 pred (2 ℕ* succ a ℕ+ 2)          ＝⟨ refl ⟩
 pred (2 ℕ* (succ a) ℕ+ 2 ℕ* 1)   ＝⟨ iii  ⟩
 pred (2 ℕ+ (2 ℕ* (succ a)))      ＝⟨ refl ⟩
 pred (2 ℕ* succ (succ a))        ∎
  where
   i   = ap (λ - → succ (2 ℕ* -)) (pred-succ (succ a))
   ii  = pred-succ (succ (2 ℕ* succ a)) ⁻¹
   iii = ap pred (distributivity-mult-over-addition 2 (succ a) 1 ⁻¹)

ℚ-zero-less-than-positive : (x y : ℕ) → 0ℚ < toℚ ((pos (succ x)) , y)
ℚ-zero-less-than-positive x y = toℚ-< (pos 0 , 0) (pos (succ x) , y) (x , γ)
 where
  γ : succℤ (pos 0 ℤ* pos (succ y)) ℤ+ pos x ＝ pos (succ x) ℤ* pos 1
  γ = succℤ (pos 0 ℤ* pos (succ y)) ℤ+ pos x ＝⟨ i   ⟩
      succℤ (pos 0) ℤ+ pos x                 ＝⟨ ii   ⟩
      succℤ (pos 0 ℤ+ pos x)                 ＝⟨ iii  ⟩
      succℤ (pos x)                          ＝⟨ refl ⟩
      pos (succ x)                           ＝⟨ refl ⟩
      pos (succ x) ℤ* pos 1                  ∎
   where
    i   = ap (λ α → succℤ α ℤ+ pos x) (ℤ-zero-left-base (pos (succ y)))
    ii  = ℤ-left-succ (pos 0) (pos x)
    iii = ap succℤ (ℤ+-comm (pos 0) (pos x))

ℚ<-addition-preserves-order : (p q r : ℚ) → p < q → (p + r) < (q + r)
ℚ<-addition-preserves-order (p , _) (q , _) (r , _) l =
 toℚ-< (p 𝔽+ r) (q 𝔽+ r) (𝔽<-addition-preserves-order p q r l)

ℚ<-adding : (p q r s : ℚ) → p < q → r < s → p + r < q + s
ℚ<-adding (p , _) (q , _) (r , _) (s , _) l₁ l₂ = toℚ-< (p 𝔽+ r) (q 𝔽+ s) I
 where
  I : p 𝔽+ r 𝔽< q 𝔽+ s
  I = 𝔽<-adding p q r s l₁ l₂

ℚ<-addition-preserves-order' : (p q r : ℚ) → p < q → 0ℚ < r → p < q + r
ℚ<-addition-preserves-order' p q r l m = γ
 where
  I : p + 0ℚ ＝ p
  I = ℚ-zero-right-neutral p

  II  : p + 0ℚ < q + r
  II = ℚ<-adding p q 0ℚ r l m

  γ : p < q + r
  γ = transport (_< q + r) I II

ℚ<-pos-multiplication-preserves-order : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < p * q
ℚ<-pos-multiplication-preserves-order (p , _) (q , _) l₁ l₂ = γ
 where
  I : (pos 0 , 0) 𝔽< (p 𝔽* q)
  I = 𝔽-pos-multiplication-preserves-order p q l₁ l₂

  γ : toℚ (pos 0 , 0) < toℚ (p 𝔽* q)
  γ = toℚ-< (pos 0 , 0) (p 𝔽* q) I

ℚ≤-pos-multiplication-preserves-order : (p q : ℚ)
                                      → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ (p * q)
ℚ≤-pos-multiplication-preserves-order (p , _) (q , _) l₁ l₂ = γ
 where
  I : (pos 0 , 0) 𝔽≤ (p 𝔽* q)
  I = 𝔽≤-pos-multiplication-preserves-order p q l₁ l₂

  γ : toℚ (pos 0 , 0) ≤ toℚ (p 𝔽* q)
  γ = toℚ-≤ (pos 0 , 0) (p 𝔽* q) I

ℚ<-addition-preserves-order'' : (p q : ℚ) → 0ℚ < q → p < p + q
ℚ<-addition-preserves-order'' p q l = γ
 where
  I : 0ℚ + p ＝ p
  I = ℚ-zero-left-neutral p

  II : q + p ＝ p + q
  II = ℚ+-comm q p

  III : 0ℚ + p < q + p
  III = ℚ<-addition-preserves-order 0ℚ q p l

  γ : p < p + q
  γ = transport₂ _<_ I II III

ℚ<-subtraction-preserves-order : (p q : ℚ) → 0ℚ < q → p - q < p
ℚ<-subtraction-preserves-order p q l = transport (p - q <_) III II
 where
  I : p < p + q
  I = ℚ<-addition-preserves-order'' p q l

  II : p - q < p + q - q
  II = ℚ<-addition-preserves-order p (p + q) (- q) I

  III : p + q - q ＝ p
  III = p + q - q   ＝⟨ ℚ+-assoc p q (- q)                  ⟩
        p + (q - q) ＝⟨ ap (p +_) (ℚ-inverse-sum-to-zero q) ⟩
        p + 0ℚ      ＝⟨ ℚ-zero-right-neutral p              ⟩
        p           ∎

ℚ<-subtraction-preserves-order' : (p q : ℚ) → q < 0ℚ → p + q < p
ℚ<-subtraction-preserves-order' p q l = γ
 where
  I : q + p < 0ℚ + p
  I = ℚ<-addition-preserves-order q 0ℚ p l

  II : q + p ＝ p + q
  II = ℚ+-comm q p

  III : 0ℚ + p ＝ p
  III = ℚ-zero-left-neutral p

  γ : p + q < p
  γ = transport₂ _<_ II III I

ℚ<-subtraction-preserves-order'' : (p q r : ℚ) → p < q - r → p + r < q
ℚ<-subtraction-preserves-order'' p q r l = transport (p + r <_) II I
 where
  I : p + r < q - r + r
  I = ℚ<-addition-preserves-order p (q - r) r l

  II : q - r + r ＝ q
  II = q - r + r       ＝⟨ ℚ+-assoc q (- r) r                   ⟩
       q + ((- r) + r) ＝⟨ ap (q +_) (ℚ-inverse-sum-to-zero' r) ⟩
       q + 0ℚ          ＝⟨ ℚ-zero-right-neutral q               ⟩
       q               ∎

ℚ<-subtraction-preserves-order''' : (p q r : ℚ) → p + q < r → p < r - q
ℚ<-subtraction-preserves-order''' p q r l = transport (_< r - q) II I
 where
  I : p + q - q < r - q
  I = ℚ<-addition-preserves-order (p + q) r (- q) l
  II : p + q - q ＝ p
  II = p + q - q       ＝⟨ ℚ+-assoc p q (- q)                  ⟩
       p + (q - q)     ＝⟨ ap (p +_) (ℚ-inverse-sum-to-zero q) ⟩
       p + 0ℚ          ＝⟨ ℚ-zero-right-neutral p              ⟩
       p ∎

ℚ<-difference-positive' : (p q : ℚ) → p < q → p - q < 0ℚ
ℚ<-difference-positive' p q l = γ
 where
  I : q - q ＝ 0ℚ
  I = ℚ-inverse-sum-to-zero q

  II : p - q < q - q
  II = ℚ<-addition-preserves-order p q (- q) l

  γ : p - q <  0ℚ
  γ = transport (p - q <_) I II

ℚ<-swap' : (p q r : ℚ) → p - q < r → p - r < q
ℚ<-swap' p q r l = transport₂ _<_ I II III
 where
  I : p - q + (q - r) ＝ p - r
  I = p - q + (q - r)       ＝⟨ i   ⟩
      p + ((- q) + (q - r)) ＝⟨ ii  ⟩
      p + ((- q) + q - r)   ＝⟨ iii ⟩
      p + (0ℚ - r)          ＝⟨ iv  ⟩
      p - r                 ∎
   where
    i   = ℚ+-assoc p (- q) (q - r)
    ii  = ap (p +_) (ℚ+-assoc (- q) q (- r) ⁻¹)
    iii = ap (λ z → p + (z - r)) (ℚ-inverse-sum-to-zero' q)
    iv  = ap (p +_) (ℚ-zero-left-neutral (- r))

  II : r + (q - r) ＝ q
  II = r + (q - r)     ＝⟨ ap (r +_) (ℚ+-comm q (- r))         ⟩
       r + ((- r) + q) ＝⟨ ℚ+-assoc r (- r) q ⁻¹               ⟩
       r - r + q       ＝⟨ ap (_+ q) (ℚ-inverse-sum-to-zero r) ⟩
       0ℚ + q          ＝⟨ ℚ-zero-left-neutral q               ⟩
       q ∎

  III : p - q + (q - r) < r + (q - r)
  III = ℚ<-addition-preserves-order (p - q) r (q - r) l

ℚ<-adding-zero : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < p + q
ℚ<-adding-zero p q l₁ l₂ = ℚ<-adding 0ℚ p 0ℚ q l₁ l₂

ℚ<-not-itself : (p : ℚ) → ¬ (p < p)
ℚ<-not-itself ((x , a) , _) l = ℤ-equal-not-less-than (x ℤ* (pos (succ a))) l

ℚ≤-split : (p q : ℚ) → p ≤ q → (p < q) ∔ (p ＝ q)
ℚ≤-split ((x , a) , α) ((y , b) , β) l = cases II III I
 where
  I : x ℤ* pos (succ b) < y ℤ* pos (succ a)
    ∔ (x ℤ* pos (succ b) ＝ y ℤ* pos (succ a))
  I = ℤ≤-split (x ℤ* pos (succ b)) (y ℤ* pos (succ a)) l

  II : x ℤ* pos (succ b) < y ℤ* pos (succ a)
     → x ℤ* pos (succ b) < y ℤ* pos (succ a)
     ∔ ((x , a) , α ＝ (y , b) , β)
  II = inl

  III : (x ℤ* pos (succ b) ＝ y ℤ* pos (succ a))
      → x ℤ* pos (succ b) < y ℤ* pos (succ a)
      ∔ ((x , a) , α ＝ (y , b) , β)
  III e = inr (ℚ-＝ ((x , a) , α) ((y , b) , β) e)

ℚ≤-addition-preserves-order : (p q r : ℚ) → p ≤ q → (p + r) ≤ (q + r)
ℚ≤-addition-preserves-order p q r l = I (ℚ≤-split p q l)
 where
  I : (p < q) ∔ (p ＝ q) → (p + r) ≤ (q + r)
  I (inl l) = ℚ<-coarser-than-≤ (p + r) (q + r) II
   where
    II : p + r < q + r
    II = ℚ<-addition-preserves-order p q r l
  I (inr e) = transport (p + r ≤_) II (ℚ≤-refl (p + r))
   where
    II : p + r ＝ q + r
    II = ap (_+ r) e

ℚ≤-addition-preserves-order'' : (p q : ℚ) → 0ℚ ≤ q → p ≤ p + q
ℚ≤-addition-preserves-order'' p q l = transport₂ _≤_ I II III
 where
  I : 0ℚ + p ＝ p
  I = ℚ-zero-left-neutral p

  II : q + p ＝ p + q
  II = ℚ+-comm q p

  III : 0ℚ + p ≤ q + p
  III = ℚ≤-addition-preserves-order 0ℚ q p l

ℚ≤-difference-positive : (p q : ℚ) → p ≤ q → 0ℚ ≤ q - p
ℚ≤-difference-positive p q l = transport (_≤ q - p) (ℚ-inverse-sum-to-zero p) I
 where
  I : p - p ≤ q - p
  I = ℚ≤-addition-preserves-order p q (- p) l

ℚ≤-pos-multiplication-preserves-order' : (p q r : ℚ)
                                       → (p ≤ q) → 0ℚ ≤ r → p * r ≤ q * r
ℚ≤-pos-multiplication-preserves-order' p q r l₁ l₂ = transport₂ _≤_ III IV II
 where
  I-lem : 0ℚ ≤ q - p
  I-lem = ℚ≤-difference-positive p q l₁

  I : 0ℚ ≤ (q - p) * r
  I = ℚ≤-pos-multiplication-preserves-order (q - p) r I-lem l₂

  II : 0ℚ + p * r ≤ (q - p) * r + p * r
  II = ℚ≤-addition-preserves-order 0ℚ ((q - p) * r) (p * r) I

  III : 0ℚ + p * r ＝ p * r
  III = ℚ-zero-left-neutral (p * r)

  IV : (q - p) * r + p * r ＝ q * r
  IV = (q - p) * r + p * r         ＝⟨ i   ⟩
       q * r + (- p) * r + p * r   ＝⟨ ii  ⟩
       q * r + ((- p) * r + p * r) ＝⟨ iii ⟩
       q * r + ((- p * r) + p * r) ＝⟨ iv  ⟩
       q * r + 0ℚ                  ＝⟨ v   ⟩
       q * r                       ∎
   where
    i   = ap (_+ p * r) (ℚ-distributivity' r q (- p))
    ii  = ℚ+-assoc (q * r) ((- p) * r) (p * r)
    iii = ap (λ z → (q * r) + (z + p * r)) (ℚ-negation-dist-over-mult p r)
    iv  = ap (q * r +_) (ℚ-inverse-sum-to-zero' (p * r))
    v   = ℚ-zero-right-neutral (q * r)

ℚ<-difference-positive : (p q : ℚ) → p < q → 0ℚ < q - p
ℚ<-difference-positive p q l = transport (_< q - p) (ℚ-inverse-sum-to-zero p) I
 where
  I : p - p < q - p
  I = ℚ<-addition-preserves-order p q (- p) l

ℚ<-pos-multiplication-preserves-order' : (p q r : ℚ)
                                       → p < q → 0ℚ < r → p * r < q * r
ℚ<-pos-multiplication-preserves-order' p q r l₁ l₂ = transport₂ _<_ III IV II
 where
  I-lem : 0ℚ < q - p
  I-lem = (ℚ<-difference-positive p q l₁)

  I : 0ℚ < (q - p) * r
  I = ℚ<-pos-multiplication-preserves-order (q - p) r I-lem l₂

  II : 0ℚ + p * r < (q - p) * r + p * r
  II = ℚ<-addition-preserves-order 0ℚ ((q - p) * r) (p * r) I

  III : 0ℚ + p * r ＝ p * r
  III = ℚ-zero-left-neutral (p * r)

  IV : (q - p) * r + p * r ＝ q * r
  IV = (q - p) * r + p * r         ＝⟨ i   ⟩
       q * r + (- p) * r + p * r   ＝⟨ ii  ⟩
       q * r + ((- p) * r + p * r) ＝⟨ iii ⟩
       q * r + ((- p * r) + p * r) ＝⟨ iv  ⟩
       q * r + 0ℚ                  ＝⟨ v   ⟩
       q * r                       ∎
   where
    i   = ap (_+ p * r) (ℚ-distributivity' r q (- p))
    ii  = ℚ+-assoc (q * r) ((- p) * r) (p * r)
    iii = ap (λ z → (q * r) + (z + p * r)) (ℚ-negation-dist-over-mult p r)
    iv  = ap (q * r +_) (ℚ-inverse-sum-to-zero' (p * r))
    v   = ℚ-zero-right-neutral (q * r)

order1ℚ : (p : ℚ) → p < p + 1ℚ
order1ℚ p = ℚ<-addition-preserves-order'' p 1ℚ (0 , refl)

order1ℚ' : (p : ℚ) → p - 1ℚ < p
order1ℚ' p = ℚ<-subtraction-preserves-order p 1ℚ (0 , refl)

ℚ≤-trans : (p q r : ℚ) → p ≤ q → q ≤ r → p ≤ r
ℚ≤-trans p q r l₁ l₂ = I (ℚ≤-split p q l₁) (ℚ≤-split q r l₂)
 where
  I : (p < q) ∔ (p ＝ q) → (q < r) ∔ (q ＝ r) → p ≤ r
  I (inl k) (inl e) = ℚ<-coarser-than-≤ p r (ℚ<-trans p q r k e)
  I (inl k) (inr e) = ℚ<-coarser-than-≤ p r (transport (p <_) e k)
  I (inr k) (inl e) = ℚ<-coarser-than-≤ p r (transport (_< r) (k ⁻¹) e)
  I (inr k) (inr e) = transport (p ≤_) e l₁

ℚ<-≤-trans : (p q r : ℚ) → p < q → q ≤ r → p < r
ℚ<-≤-trans p q r l₁ l₂ = I (ℚ≤-split q r l₂)
 where
  I : (q < r) ∔ (q ＝ r) → p < r
  I (inl l) = ℚ<-trans p q r l₁ l
  I (inr l) = transport (p <_) l l₁

ℚ≤-<-trans : (p q r : ℚ) → p ≤ q → q < r → p < r
ℚ≤-<-trans p q r l₁ l₂ = I (ℚ≤-split p q l₁)
 where
  I : (p < q) ∔ (p ＝ q) → p < r
  I (inl l) = ℚ<-trans p q r l l₂
  I (inr l) = transport (_< r) (l ⁻¹) l₂

ℚ≤-adding : (x y u v : ℚ) → x ≤ y → u ≤ v → x + u ≤ y + v
ℚ≤-adding x y u v l₁ l₂ = ℚ≤-trans (x + u) (y + u) (y + v) I III
 where
  I : x + u ≤ y + u
  I = ℚ≤-addition-preserves-order x y u l₁

  II : u + y ≤ v + y
  II = ℚ≤-addition-preserves-order u v y l₂

  III : y + u ≤ y + v
  III = transport₂ _≤_ (ℚ+-comm u y) (ℚ+-comm v y) II

ℚ≤-swap : (x y : ℚ) → x ≤ y → - y ≤ - x
ℚ≤-swap x y l = transport id III II
 where
  I : x - x ≤ y - x
  I = ℚ≤-addition-preserves-order x y (- x) l

  II : x - x - y ≤ y - x - y
  II = ℚ≤-addition-preserves-order (x - x) (y - x) (- y) I

  III : x - x - y ≤ y - x - y ＝ - y ≤ - x
  III = ap₂ _≤_ α β
   where
    α : x - x - y ＝ - y
    α = x - x - y             ＝⟨ ap (_- y) (ℚ-inverse-sum-to-zero x) ⟩
        0ℚ - y                ＝⟨ ℚ-zero-left-neutral (- y)           ⟩
        - y                   ∎
    β : y - x - y ＝ - x
    β = y - x - y             ＝⟨ ap (_- y) (ℚ+-comm y (- x))             ⟩
        (- x) + y - y         ＝⟨ ℚ+-assoc (- x) y (- y)                  ⟩
        (- x) + (y - y)       ＝⟨ ap ((- x) +_) (ℚ-inverse-sum-to-zero y) ⟩
        (- x) + 0ℚ            ＝⟨ ℚ-zero-right-neutral (- x)              ⟩
        (- x)                 ∎

ℚ≤-swap' : (x : ℚ) → x ≤ 0ℚ → 0ℚ ≤ - x
ℚ≤-swap' x l = transport (_≤ - x) ℚ-minus-zero-is-zero (ℚ≤-swap x 0ℚ l)

ℚ<-swap : (x y : ℚ) → x < y → - y < - x
ℚ<-swap x y l = γ (ℚ≤-split (- y) (- x) I)
 where
  I : - y ≤ - x
  I = ℚ≤-swap x y (ℚ<-coarser-than-≤ x y l)

  γ : - y < - x ∔ (- y ＝ - x) → - y < - x
  γ (inl il) = il
  γ (inr ir) = 𝟘-elim (ℚ<-not-itself x (transport (x <_) γ' l))
   where
    γ' : y ＝ x
    γ' = y       ＝⟨ ℚ-minus-minus y    ⟩
         - (- y) ＝⟨ ap -_ ir           ⟩
         - (- x) ＝⟨ ℚ-minus-minus x ⁻¹ ⟩
         x       ∎

ℚ<-swap'' : (p : ℚ) → p < 0ℚ → 0ℚ < - p
ℚ<-swap'' p l = transport (_< - p) ℚ-minus-zero-is-zero (ℚ<-swap p 0ℚ l)

ℚ<-swap''' : (x y : ℚ) → - y < - x → x < y
ℚ<-swap''' x y l = transport₂ _<_ I II III
 where
  I : - (- x) ＝ x
  I = ℚ-minus-minus x ⁻¹

  II : - (- y) ＝ y
  II = ℚ-minus-minus y ⁻¹

  III : - (- x) < - (- y)
  III = ℚ<-swap (- y) (- x) l

-- TODO : Cleanup from here

multiplicative-inverse-preserves-pos : (p : ℚ) → 0ℚ < p → (nz : ¬ (p ＝ 0ℚ)) → 0ℚ < multiplicative-inverse p nz
multiplicative-inverse-preserves-pos ((pos 0 , a) , α) l nz = 𝟘-elim (nz (numerator-zero-is-zero ((pos zero , a) , α) by-definition))
multiplicative-inverse-preserves-pos ((pos (succ x) , a) , α) l nz = toℚ-< (pos 0 , 0) (pos (succ a) , x) (a , I)
 where
  I : succℤ (pos 0 ℤ* pos (succ x)) ℤ+ pos a ＝ pos (succ a) ℤ* pos 1
  I = succℤ (pos 0 ℤ* pos (succ x)) ℤ+ pos a ＝⟨ ℤ-left-succ (pos 0 ℤ* pos (succ x)) (pos a) ⟩
      succℤ (pos 0 ℤ* pos (succ x) ℤ+ pos a) ＝⟨ ℤ-right-succ (pos 0 ℤ* pos (succ x)) (pos a) ⁻¹ ⟩
      pos 0 ℤ* pos (succ x) ℤ+ pos (succ a)  ＝⟨ ap (_ℤ+ pos (succ a)) (ℤ-zero-left-base (pos (succ x))) ⟩
      pos 0 ℤ+ pos (succ a) ＝⟨ ℤ-zero-left-neutral (pos (succ a)) ⟩
      pos (succ a) ＝⟨ ℤ-mult-right-id (pos (succ a)) ⟩
      pos (succ a) ℤ* pos 1 ∎
multiplicative-inverse-preserves-pos ((negsucc x , a) , α) l nz = 𝟘-elim (ℚ<-not-itself ((negsucc x , a) , α) (ℚ<-trans (((negsucc x , a) , α)) 0ℚ (((negsucc x , a) , α)) I l))
 where
  I : ((negsucc x , a) , α) < 0ℚ
  I = transport (_< 0ℚ) (toℚ-to𝔽 ((negsucc x , a) , α) ⁻¹) (toℚ-< (negsucc x , a) (pos 0 , 0) II)
   where
    II : (negsucc x , a) 𝔽< (pos 0 , 0)
    II = x , III
     where
      III : succℤ (negsucc x ℤ* pos 1) ℤ+ pos x ＝ pos 0 ℤ* pos (succ a)
      III = succℤ (negsucc x ℤ* pos 1) ℤ+ pos x ＝⟨ ℤ-left-succ (negsucc x ℤ* pos 1) (pos x) ⟩
            succℤ (negsucc x ℤ* pos 1 ℤ+ pos x) ＝⟨ by-definition ⟩
            negsucc x ℤ* pos 1 ℤ+ pos (succ x)  ＝⟨ ap (_ℤ+ pos (succ x)) (ℤ-mult-right-id (negsucc x)) ⟩
            negsucc x ℤ+ pos (succ x)           ＝⟨ ℤ-sum-of-inverse-is-zero' (pos (succ x)) ⟩
            pos 0                               ＝⟨ ℤ-zero-left-base (pos (succ a)) ⁻¹ ⟩
            pos 0 ℤ* pos (succ a)               ∎

ℚ-equal-or-less-than-is-prop : (x y : ℚ) → is-prop ((x ＝ y) ∔ (y < x))
ℚ-equal-or-less-than-is-prop x y (inl l) (inl r) = ap inl (ℚ-is-set l r)
ℚ-equal-or-less-than-is-prop x y (inl l) (inr r) = 𝟘-elim (ℚ<-not-itself y ((transport (y <_) l r)))
ℚ-equal-or-less-than-is-prop x y (inr l) (inl r) = 𝟘-elim ((ℚ<-not-itself x (transport (_< x) (r ⁻¹) l)))
ℚ-equal-or-less-than-is-prop x y (inr l) (inr r) = ap inr (ℚ<-is-prop y x l r)

ℚ-trich-a : (x y : ℚ) → (l : x < y) → ℚ-trichotomous x y ＝ inl l
ℚ-trich-a x y l = equality-cases (ℚ-trichotomous x y) I II
 where
  I : (l₂ : x < y) → ℚ-trichotomous x y ＝ inl l₂ → ℚ-trichotomous x y ＝ inl l
  I l₂ e = e ∙ ap inl (ℚ<-is-prop x y l₂ l)
  II : (y₁ : (x ＝ y) ∔ (y < x)) → ℚ-trichotomous x y ＝ inr y₁ → ℚ-trichotomous x y ＝ inl l
  II (inl e) _ = 𝟘-elim (ℚ<-not-itself y (transport (_< y) e l))
  II (inr lt) _ = 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x l lt))

ℚ-trich-b : (x y : ℚ) → (r : (x ＝ y) ∔ (y < x)) → ℚ-trichotomous x y ＝ inr r
ℚ-trich-b x y r = equality-cases (ℚ-trichotomous x y) I II
 where
  I : (l : x < y) → ℚ-trichotomous x y ＝ inl l → ℚ-trichotomous x y ＝ inr r
  I l _ = Cases r (λ e → 𝟘-elim (ℚ<-not-itself y (transport (_< y) e l)))
                   λ e → 𝟘-elim (ℚ<-not-itself x (ℚ<-trans x y x l e))
  II : (s : (x ＝ y) ∔ (y < x)) → ℚ-trichotomous x y ＝ inr s → ℚ-trichotomous x y ＝ inr r
  II s e = e ∙ (ap inr III)
   where
    III : s ＝ r
    III = ℚ-equal-or-less-than-is-prop x y s r

ℚ-trich-c : (x : ℚ) → (e : (x ＝ x) ∔ x < x) → ℚ-trichotomous x x ＝ inr e
ℚ-trich-c x e = equality-cases (ℚ-trichotomous x x) I II
 where
  I : (k : x < x) → ℚ-trichotomous x x ＝ inl k → ℚ-trichotomous x x ＝ inr e
  I k f = 𝟘-elim (ℚ<-not-itself x k)

  II : (k : (x ＝ x) ∔ (x < x)) → ℚ-trichotomous x x ＝ inr k → ℚ-trichotomous x x ＝ inr e
  II k l = Cases k III
                   (λ - → 𝟘-elim (ℚ<-not-itself x -) )
   where
    III : x ＝ x → ℚ-trichotomous x x ＝ inr e
    III z = l ∙ ap inr (ℚ-equal-or-less-than-is-prop x x k e)

trisect : (x y : ℚ) → x < y → Σ (x' , y') ꞉ ℚ × ℚ , (x < x') × (x' < y') × (y' < y) × (y - x' ＝ 2/3 * (y - x)) × (y' - x ＝ 2/3 * (y - x))
trisect x y l = (x + d * 1/3 , x + d * 2/3) , I , II , III , IV , V
 where
  d : ℚ
  d = y - x
  α : 0ℚ < d
  α = ℚ<-difference-positive x y l

  β : 0ℚ < 1/3
  β = ℚ-zero-less-than-positive 0 2

  γ : 0ℚ < d * 1/3
  γ = ℚ<-pos-multiplication-preserves-order d 1/3 α β

  ψ : (x + d * 1/3) < (x + d * 1/3 + d * 1/3)
  ψ = ℚ<-addition-preserves-order'' (x + d * 1/3) (d * 1/3) γ

  η : d * 2/3 < d
  η = transport₂ _<_ ii iii i
   where
    i : (0ℚ + d * 2/3) < (d * 1/3 + d * 2/3)
    i = ℚ<-addition-preserves-order 0ℚ (d * 1/3) (d * 2/3) γ
    ii : 0ℚ + d * 2/3 ＝ d * 2/3
    ii = ℚ-zero-left-neutral (d * 2/3)
    iii : d * 1/3 + d * 2/3 ＝ d
    iii = d * 1/3 + d * 2/3 ＝⟨ ℚ-distributivity d 1/3 2/3 ⁻¹ ⟩
          d * (1/3 + 2/3)   ＝⟨ ap (d *_) (1/3+2/3) ⟩
          d * 1ℚ            ＝⟨ ℚ-mult-right-id d ⟩
          d                 ∎

  I : x < (x + d * 1/3)
  I = ℚ<-addition-preserves-order'' x (d * 1/3) γ

  II : (x + d * 1/3) < (x + d * 2/3)
  II = transport (x + d * 1/3 <_) i ψ
   where
    i : x + d * 1/3 + d * 1/3 ＝ x + d * 2/3
    i = x + d * 1/3 + d * 1/3   ＝⟨ ℚ+-assoc x (d * 1/3) (d * 1/3) ⟩
        x + (d * 1/3 + d * 1/3) ＝⟨ ap (x +_) (ℚ-distributivity d 1/3 1/3 ⁻¹) ⟩
        x + d * (1/3 + 1/3)     ＝⟨ ap (λ z → x + (d * z)) (1/3+1/3) ⟩
        x + d * 2/3             ∎


  III : x + d * 2/3 < y
  III = transport₂ _<_ ii iii i
   where
    i : d * 2/3 + x < d + x
    i = ℚ<-addition-preserves-order (d * 2/3) d x η
    ii : d * 2/3 + x ＝ x + d * 2/3
    ii = ℚ+-comm (d * 2/3) x
    iii : d + x ＝ y
    iii = d + x            ＝⟨ ℚ+-assoc y (- x) x ⟩
          y + ((- x) + x)  ＝⟨ ap (y +_) (ℚ-inverse-sum-to-zero' x) ⟩
          y + 0ℚ           ＝⟨ ℚ-zero-right-neutral y ⟩
          y                ∎

  IV : y - (x + d * 1/3) ＝ 2/3 * d
  IV = y - (x + d * 1/3)                 ＝⟨ ap (y +_) (ℚ-minus-dist x (d * 1/3)) ⁻¹ ⟩
       y + ((- x) + (- d * 1/3))         ＝⟨ ℚ+-assoc y (- x) (- d * 1/3) ⁻¹ ⟩
       d + (- d * 1/3)                   ＝⟨ ap (_+ (- (d * 1/3))) (ℚ-mult-left-id d ⁻¹) ⟩
       1ℚ * d + (- d * 1/3)              ＝⟨ ap (λ z → (z * d) + (- (d * 1/3))) (1/3+2/3) ⟩
       1ℚ * d + (- d * 1/3)              ＝⟨ ap (_+ (- (d * 1/3))) (ℚ*-comm (1/3 + 2/3) d)  ⟩
       d * (1/3 + 2/3) + (- d * 1/3)     ＝⟨ ap (λ z → (d * z) + (- (d * 1/3))) (ℚ+-comm 1/3 2/3) ⟩
       d * (2/3 + 1/3) + (- d * 1/3)     ＝⟨ ap (_+ - (d * 1/3)) (ℚ-distributivity d 2/3 1/3) ⟩
       d * 2/3 + d * 1/3 + (- d * 1/3)   ＝⟨ ℚ+-assoc (d * 2/3) (d * 1/3) (- (d * 1/3)) ⟩
       d * 2/3 + (d * 1/3 + (- d * 1/3)) ＝⟨ ap₂ _+_ (ℚ*-comm d 2/3) (ℚ-inverse-sum-to-zero (d * 1/3)) ⟩
       2/3 * d + 0ℚ                      ＝⟨ ℚ-zero-right-neutral (2/3 * d) ⟩
       2/3 * d ∎

  V : x + d * 2/3 - x ＝ 2/3 * d
  V = x + d * 2/3 - x       ＝⟨ ap (_+ (- x)) (ℚ+-comm x (d * 2/3)) ⟩
      d * 2/3 + x + (- x)   ＝⟨ ℚ+-assoc (d * 2/3) x (- x) ⟩
      d * 2/3 + (x - x)     ＝⟨ ap₂ _+_ (ℚ*-comm d 2/3) (ℚ-inverse-sum-to-zero x) ⟩
      2/3 * d + 0ℚ          ＝⟨ ℚ-zero-right-neutral (2/3 * d) ⟩
      2/3 * d ∎

ℚ≤-anti : (p q : ℚ) → p ≤ q → q ≤ p → p ＝ q
ℚ≤-anti p q l₁ l₂ = I (ℚ≤-split p q l₁) (ℚ≤-split q p l₂)
 where
  I : (p < q) ∔ (p ＝ q) → (q < p) ∔ (q ＝ p) → p ＝ q
  I (inl l) (inl r) = 𝟘-elim (ℚ<-not-itself p (ℚ<-trans p q p l r))
  I (inl l) (inr r) = r ⁻¹
  I (inr e) (inl f) = e
  I (inr e) (inr f) = e

0<1/2 : 0ℚ < 1/2
0<1/2 = toℚ-< (pos 0 , 0) (pos 1 , 1) (0 , refl)

0<1/4 : 0ℚ < 1/4
0<1/4 = toℚ-< (pos 0 , 0) (pos 1 , 3) (0 , refl)

0<1/5 : 0ℚ < 1/5
0<1/5 = toℚ-< (pos 0 , 0) (pos 1 , 5) (0 , refl)

1/2<1 : 1/2 < 1ℚ
1/2<1 = toℚ-< (pos 1 , 1) (pos 1 , 0) (0 , refl)

halving-preserves-order : (p : ℚ) → 0ℚ < p → 0ℚ < p * 1/2
halving-preserves-order p l = ℚ<-pos-multiplication-preserves-order p 1/2 l 0<1/2

halving-preserves-order' : (p : ℚ) → 0ℚ < p → 0ℚ < 1/2 * p
halving-preserves-order' p l = ℚ<-pos-multiplication-preserves-order 1/2 p 0<1/2 l

quarter-preserves-order : (p : ℚ) → 0ℚ < p → 0ℚ < p * 1/4
quarter-preserves-order p l = ℚ<-pos-multiplication-preserves-order p 1/4 l 0<1/4

quarter-preserves-order' : (p : ℚ) → 0ℚ < p → 0ℚ < 1/4 * p
quarter-preserves-order' p l = ℚ<-pos-multiplication-preserves-order 1/4 p 0<1/4 l

half-of-pos-is-less : (p : ℚ) → 0ℚ < p → 1/2 * p < p
half-of-pos-is-less p l = transport (1/2 * p <_) III II
 where
  I : 0ℚ < 1/2 * p
  I = halving-preserves-order' p l
  II : 1/2 * p < 1/2 * p + 1/2 * p
  II = ℚ<-addition-preserves-order'' (1/2 * p) (1/2 * p) I
  III : 1/2 * p + 1/2 * p ＝ p
  III = 1/2 * p + 1/2 * p ＝⟨ ℚ-distributivity' p 1/2 1/2 ⁻¹ ⟩
        (1/2 + 1/2) * p   ＝⟨ ap (_* p) (1/2+1/2) ⟩
        1ℚ * p            ＝⟨ ℚ-mult-left-id p ⟩
        p ∎

ℚ-dense : (p q : ℚ) → p < q → Σ x ꞉ ℚ , (p < x) × (x < q)
ℚ-dense p q l = p + (1/2 * (q - p)) , left-inequality , right-inequality
 where
  I : 0ℚ < (q - p) * 1/2
  I = halving-preserves-order (q - p) (ℚ<-difference-positive p q l)

  II : 0ℚ < 1/2 * (q - p)
  II = transport (0ℚ <_) (ℚ*-comm (q - p) 1/2) I

  III : p + 1/2 * (q - p) < p + 1/2 * (q - p) + 1/2 * (q - p)
  III = ℚ<-addition-preserves-order'' (p + 1/2 * (q - p)) (1/2 * (q - p)) II

  IV : p + 1/2 * (q - p) + 1/2 * (q - p) ＝ q
  IV = p + 1/2 * (q - p) + 1/2 * (q - p)    ＝⟨ ℚ+-assoc p (1/2 * (q - p)) (1/2 * (q - p))       ⟩
       p + (1/2 * (q - p) + 1/2 * (q - p))  ＝⟨ ap (p +_) (ℚ-distributivity' (q - p) 1/2 1/2 ⁻¹) ⟩
       p + (1/2 + 1/2) * (q - p)            ＝⟨ ap (λ α → p + α * (q - p)) (1/2+1/2)             ⟩
       p + 1ℚ * (q - p)                     ＝⟨ ap (p +_) (ℚ-mult-left-id (q - p))               ⟩
       p + (q - p)                          ＝⟨ ap (p +_) (ℚ+-comm q (- p))                         ⟩
       p + ((- p) + q)                      ＝⟨ ℚ+-assoc p (- p) q ⁻¹                            ⟩
       p - p + q                            ＝⟨ ap (_+ q) (ℚ-inverse-sum-to-zero p)              ⟩
       0ℚ + q                               ＝⟨ ℚ-zero-left-neutral q                            ⟩
       q                                    ∎

  left-inequality : p < p + 1/2 * (q - p)
  left-inequality = ℚ<-addition-preserves-order'' p (1/2 * (q - p)) II

  right-inequality : p + 1/2 * (q - p) < q
  right-inequality = transport (p + 1/2 * (q - p) <_) IV III

inequality-chain-outer-bounds-inner : (a b c d : ℚ) → a < b → b < c → c < d → c - b < d - a
inequality-chain-outer-bounds-inner a b c d l₁ l₂ l₃ = ℚ<-trans (c - b) (d - b) (d - a) I III
 where
  I : c - b < d - b
  I = ℚ<-addition-preserves-order c d (- b) l₃
  II : - b < - a
  II = ℚ<-swap a b l₁
  III : d - b < d - a
  III = transport₂ _<_ (ℚ+-comm (- b) d) (ℚ+-comm (- a) d) (ℚ<-addition-preserves-order (- b) (- a) d II)

ℚ<-trans₂ : (p q r s : ℚ) → p < q → q < r → r < s → p < s
ℚ<-trans₂ p q r s l₁ l₂ l₃ = ℚ<-trans p r s I l₃
 where
  I : p < r
  I = ℚ<-trans p q r l₁ l₂

ℚ<-trans₃ : (p q r s t : ℚ) → p < q → q < r → r < s → s < t → p < t
ℚ<-trans₃ p q r s t l₁ l₂ l₃ l₄ = ℚ<-trans p s t I l₄
 where
  I : p < s
  I = ℚ<-trans₂ p q r s l₁ l₂ l₃

ℚ≤-trans₂ : (p q r s : ℚ) → p ≤ q → q ≤ r → r ≤ s → p ≤ s
ℚ≤-trans₂ p q r s l₁ l₂ l₃ = ℚ≤-trans p r s I l₃
 where
  I : p ≤ r
  I = ℚ≤-trans p q r l₁ l₂

ℚ≤-trans₃ : (p q r s t : ℚ) → p ≤ q → q ≤ r → r ≤ s → s ≤ t → p ≤ t
ℚ≤-trans₃ p q r s t l₁ l₂ l₃ l₄ = ℚ≤-trans p s t I l₄
 where
  I : p ≤ s
  I = ℚ≤-trans₂ p q r s l₁ l₂ l₃

ℚ<-addition-cancellable : (a b c : ℚ) → a + b < c + b → a < c
ℚ<-addition-cancellable a b c l = transport₂ _<_ (I a b) (I c b) (ℚ<-addition-preserves-order (a + b) (c + b) (- b) l)
 where
  I : (a b : ℚ) → a + b - b ＝ a
  I a b = a + b - b   ＝⟨ ℚ+-assoc a b (- b) ⟩
          a + (b - b) ＝⟨ ap (a +_) (ℚ-inverse-sum-to-zero b) ⟩
          a + 0ℚ      ＝⟨ ℚ-zero-right-neutral a ⟩
          a           ∎

ℚ<-addition-cancellable' : (a b c : ℚ) → b + a < b + c → a < c
ℚ<-addition-cancellable' a b c l = ℚ<-addition-cancellable a b c
                                       (transport₂ _<_ (ℚ+-comm b a) (ℚ+-comm b c) l)

order-lemma : (a b c d : ℚ) → a - b < c - d → d < b ∔ a < c
order-lemma a b c d l = I (ℚ-trichotomous a c)
 where
  I : (a < c) ∔ (a ＝ c) ∔ (c < a) → d < b ∔ a < c
  I (inl a<c) = inr a<c
  I (inr (inl a＝c)) = inl (ℚ<-swap''' d b ii)
   where
    i : c - b < c - d
    i = transport (λ z → z - b < c - d) a＝c l
    ii : - b < - d
    ii = ℚ<-addition-cancellable' (- b) c (- d) i
  I (inr (inr c<a)) = inl (ℚ<-swap''' d b iii)
   where
    i :  - a < - c
    i = ℚ<-swap c a c<a
    ii : (- a) + (a - b) < (- c) + (c - d)
    ii = ℚ<-adding (- a) (- c) (a - b) (c - d) i l
    iv : (a b : ℚ) → (- a) + (a - b) ＝ - b
    iv a b = (- a) + (a - b)   ＝⟨ ℚ+-assoc (- a) a (- b) ⁻¹ ⟩
             (- a) + a - b     ＝⟨ ap (_- b) (ℚ-inverse-sum-to-zero' a) ⟩
             0ℚ - b            ＝⟨ ℚ-zero-left-neutral (- b) ⟩
             - b ∎
    iii : - b < - d
    iii = transport₂ _<_ (iv a b) (iv c d) ii

\end{code}
