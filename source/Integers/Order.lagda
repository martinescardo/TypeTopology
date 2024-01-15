Andrew Sneap, 26th November 2021

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.AbsoluteDifference using (∣_-_∣)
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Subsingletons

open import Integers.Abs
open import Integers.Type
open import Integers.Addition
open import Integers.Multiplication
open import Integers.Negation
open import Naturals.Addition renaming (_+_ to _ℕ+_)

module Integers.Order where

\end{code}

First, the definition of < and ≤ for the integers. See the NaturalsOrder import
to see how < is defined similarly to < for the natural numbers.  Following the
definitions are the proofs that the relations are propositions, and some simple
proofs for each.

\begin{code}

_≤ℤ_ _≥ℤ_ : (x y : ℤ) → 𝓤₀ ̇
x ≤ℤ y = Σ n ꞉ ℕ , x + pos n ＝ y
x ≥ℤ y = y ≤ℤ x

_<ℤ_ _>ℤ_ : (x y : ℤ) → 𝓤₀ ̇
x <ℤ y = succℤ x ≤ℤ y
x >ℤ y = y <ℤ x

instance
 Order-ℤ-ℤ : Order ℤ ℤ
 _≤_ {{Order-ℤ-ℤ}} = _≤ℤ_

 Strict-Order-ℤ-ℤ : Strict-Order ℤ ℤ
 _<_ {{Strict-Order-ℤ-ℤ}} = _<ℤ_

 Strict-Order-Chain-ℤ-ℤ-ℤ : Strict-Order-Chain ℤ ℤ ℤ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℤ-ℤ-ℤ}} p q r = (p < q) × (q < r)

 Order-Chain-ℤ-ℤ-ℤ : Order-Chain ℤ ℤ ℤ _≤_ _≤_
 _≤_≤_ {{Order-Chain-ℤ-ℤ-ℤ}} p q r = (p ≤ q) × (q ≤ r)

ℤ≤-is-prop : (x y : ℤ) → is-prop (x ≤ y)
ℤ≤-is-prop x y (n , p) (m , q) = to-subtype-＝ I II
 where
  I : (k : ℕ) → (α β : x + pos k ＝ y) → α ＝ β
  I _ = ℤ-is-set

  II : n ＝ m
  II = pos-lc (ℤ+-lc (pos n) (pos m) x γ)
   where
    γ : x + pos n ＝ x + pos m
    γ = x + pos n ＝⟨ p    ⟩
        y         ＝⟨ q ⁻¹ ⟩
        x + pos m ∎

ℤ<-is-prop : (x y : ℤ) → is-prop (x < y)
ℤ<-is-prop x = ℤ≤-is-prop (succℤ x)

≤-incrℤ : (x : ℤ) → x ≤ succℤ x
≤-incrℤ x = 1 , refl

<-incrℤ : (x : ℤ) → x < succℤ x
<-incrℤ x = 0 , refl

≤-predℤ : (x : ℤ) → predℤ x ≤ x
≤-predℤ x = 1 , succpredℤ x

≤-predℤ' : (x y : ℤ) → x ≤ y → predℤ x ≤ predℤ y
≤-predℤ' x y (n , e) = n , γ
 where
  γ : predℤ x + pos n ＝ predℤ y
  γ = predℤ x + pos n   ＝⟨ ℤ-left-pred x (pos n) ⟩
      predℤ (x + pos n) ＝⟨ ap predℤ e            ⟩
      predℤ y ∎

<-predℤ : (x : ℤ) → predℤ x < x
<-predℤ x = 0 , succpredℤ x

<-is-≤ : (x y : ℤ) → x < y → x ≤ y
<-is-≤ x y (a , p) = succ a , γ
 where
  γ : succℤ (x + pos a) ＝ y
  γ = succℤ (x + pos a) ＝⟨ ℤ-left-succ x (pos a) ⁻¹ ⟩
      succℤ x + pos a   ＝⟨ p                        ⟩
      y                 ∎

ℕ-order-respects-ℤ-order : (m n : ℕ) → m < n → pos m < pos n
ℕ-order-respects-ℤ-order m n l = I (subtraction'' m n l)
 where
  I : (Σ k ꞉ ℕ , succ k ℕ+ m ＝ n) → pos m < pos n
  I (k , e) = k , II
   where
    II : succℤ (pos m) + pos k ＝ pos n
    II = succℤ (pos m) + pos k ＝⟨ distributivity-pos-addition (succ m) k     ⟩
         pos (succ m ℕ+ k)     ＝⟨ ap pos (addition-commutativity (succ m) k) ⟩
         pos (k ℕ+ succ m)     ＝⟨ ap pos (succ-left k m ⁻¹)                  ⟩
         pos (succ k ℕ+ m)     ＝⟨ ap pos e                                   ⟩
         pos n                 ∎

ℕ-order-respects-ℤ-order' : (m n : ℕ) → m < n → negsucc n < negsucc m
ℕ-order-respects-ℤ-order' m n l = I (subtraction'' m n l)
 where
  I : (Σ k ꞉ ℕ , succ k ℕ+ m ＝ n) → negsucc n < negsucc m
  I (k , e) = k , γ
   where
    k' = pos (succ k)
    m' = pos (succ m)
    n' = pos (succ n)

    II : k' + m' ＝ n'
    II = k' + m'                ＝⟨ i  ⟩
         pos (succ k ℕ+ succ m) ＝⟨ ii ⟩
         n'                     ∎
     where
      i  = distributivity-pos-addition (succ k) (succ m)
      ii = ap (pos ∘ succ) e

    γ : succℤ (negsucc n) + pos k ＝ negsucc m
    γ = succℤ (negsucc n) + pos k         ＝⟨ i    ⟩
        negsucc n + k'                    ＝⟨ ii   ⟩
        k' + negsucc n                    ＝⟨ iii  ⟩
        k' + negsucc n + pos 0            ＝⟨ iv   ⟩
        k' + negsucc n + (m' + negsucc m) ＝⟨ v    ⟩
        k' + negsucc n + m' + negsucc m   ＝⟨ vi   ⟩
        k' + (negsucc n + m') + negsucc m ＝⟨ vii  ⟩
        k' + (m' + negsucc n) + negsucc m ＝⟨ viii ⟩
        k' + m' + negsucc n + negsucc m   ＝⟨ ix   ⟩
        k' + m' + (negsucc n + negsucc m) ＝⟨ x    ⟩
        n' + (negsucc n + negsucc m)      ＝⟨ xi   ⟩
        n' + negsucc n + negsucc m        ＝⟨ xii  ⟩
        pos 0 + negsucc m                 ＝⟨ xiii ⟩
        negsucc m                         ∎
      where
       ivₐₚ : pos 0 ＝ m' - m'
       ivₐₚ = ℤ-sum-of-inverse-is-zero m' ⁻¹

       i    = ℤ-left-succ (negsucc n) (pos k)
       ii   = ℤ+-comm (negsucc n) k'
       iii  = ℤ-zero-right-neutral (k' + negsucc n)
       iv   = ap ((k' + negsucc n) +_) ivₐₚ
       v    = ℤ+-assoc (k' + negsucc n) m' (negsucc m) ⁻¹
       vi   = ap (_+ negsucc m) (ℤ+-assoc k' (negsucc n) m')
       vii  = ap (λ p → k' + p + negsucc m) (ℤ+-comm (negsucc n) m')
       viii = ap (_+ negsucc m) (ℤ+-assoc k' m' (negsucc n) ⁻¹)
       ix   = ℤ+-assoc (k' + m') (negsucc n) (negsucc m)
       x    = ap (λ p → p + (negsucc n + negsucc m)) II
       xi   = ℤ+-assoc n' (negsucc n) (negsucc m) ⁻¹
       xii  = ap (_+ negsucc m) (ℤ-sum-of-inverse-is-zero n')
       xiii = ℤ-zero-left-neutral (negsucc m)

ℤ-bigger-or-equal-not-less : (x y : ℤ) → x ≤ y → ¬ (y < x)
ℤ-bigger-or-equal-not-less x y (α , p) (β , q) = 𝟘-elim γ
 where
  I : x + succℤ (pos (α ℕ+ β)) ＝ x + pos 0
  I = x + succℤ (pos (α ℕ+ β))    ＝⟨ i             ⟩
      x + succℤ (pos α + pos β)   ＝⟨ ii            ⟩
      succℤ (x + (pos α + pos β)) ＝⟨ iii           ⟩
      succℤ (x + pos α + pos β)   ＝⟨ iv            ⟩
      succℤ (x + pos α) + pos β   ＝⟨ v             ⟩
      x                           ＝⟨ by-definition ⟩
      x + pos 0                   ∎
   where
    i   = ap (λ - → x + succℤ -) (distributivity-pos-addition α β ⁻¹)
    ii  = ℤ-right-succ x (pos α + pos β)
    iii = ap succℤ (ℤ+-assoc x (pos α) (pos β) ⁻¹)
    iv  = ℤ-left-succ (x + pos α) (pos β) ⁻¹
    v   = transport (λ - → succℤ - + (pos β) ＝ x) (p ⁻¹) q

  II : succℤ (pos (α ℕ+ β)) ＝ pos 0
  II = ℤ+-lc (succℤ (pos (α ℕ+ β))) (pos 0) x I

  γ : 𝟘
  γ = pos-succ-not-zero (α ℕ+ β) II

ℤ≤-split : (x y : ℤ) → x ≤ y → (x < y) ∔ (x ＝ y)
ℤ≤-split x y (zero , p)   = inr p
ℤ≤-split x y (succ a , p) = inl (a , (ℤ-left-succ x (pos a)  ∙ p))

ℤ≤-trans : (x y z : ℤ) → x ≤ y → y ≤ z → x ≤ z
ℤ≤-trans x y z (a , p) (b , q) = a ℕ+ b , I
 where
  I : x + pos (a ℕ+ b) ＝ z
  I = x + pos (a ℕ+ b)    ＝⟨ ap (x +_) (distributivity-pos-addition a b ⁻¹) ⟩
      x + (pos a + pos b) ＝⟨ ℤ+-assoc x (pos a) (pos b) ⁻¹                  ⟩
      x + pos a + pos b   ＝⟨ ap (_+ (pos b)) p                              ⟩
      y + (pos b)         ＝⟨ q                                              ⟩
      z                   ∎

ℤ<-trans : (x y z : ℤ) → x < y → y < z → x < z
ℤ<-trans x y z l₁ l₂ = ℤ≤-trans (succℤ x) (succℤ y) z I l₂
 where
  I : succℤ x ≤ succℤ y
  I = ℤ≤-trans (succℤ x) y (succℤ y) l₁ (≤-incrℤ y)

ℤ<-≤-trans : (x y z : ℤ) → x < y → y ≤ z → x < z
ℤ<-≤-trans x y z l₁ l₂ = cases γ₁ γ₂ I
 where
  I : (y < z) ∔ (y ＝ z)
  I = ℤ≤-split y z l₂

  γ₁ : y < z → x < z
  γ₁ l₃ = ℤ<-trans x y z l₁ l₃

  γ₂ : y ＝ z → x < z
  γ₂ e = transport (x <_) e l₁

ℤ≤-<-trans : (x y z : ℤ) → x ≤ y → y < z → x < z
ℤ≤-<-trans x y z l₁ l₂ = cases γ₁ γ₂ I
 where
  I : (x < y) ∔ (x ＝ y)
  I = ℤ≤-split x y l₁

  γ₁ : x < y → x < z
  γ₁ l₃ = ℤ<-trans x y z l₃ l₂

  γ₂ : x ＝ y → x < z
  γ₂ e = transport (_< z) (e ⁻¹) l₂

ℤ≤-refl : (x : ℤ) → x ≤ x
ℤ≤-refl x = 0 , refl

ℤ-equal-not-less-than : (x : ℤ) → ¬ (x < x)
ℤ-equal-not-less-than x (0 , α)      = succℤ-no-fp x (α ⁻¹)
ℤ-equal-not-less-than x (succ n , α) = pos-succ-not-zero (n ℕ+ 1) γ
 where
  I : x + succℤ (succℤ (pos n)) ＝ x + pos 0
  I = x + succℤ (succℤ (pos n))  ＝⟨ ℤ-right-succ x (succℤ (pos n))   ⟩
      succℤ (x + succℤ (pos n))  ＝⟨ ℤ-left-succ x (succℤ (pos n)) ⁻¹ ⟩
      succℤ x + succℤ (pos n)    ＝⟨ by-definition                    ⟩
      succℤ x + pos (succ n)     ＝⟨ α                                ⟩
      x                          ＝⟨ ℤ-zero-right-neutral x           ⟩
      x + pos 0                  ∎

  γ : succℤ (succℤ (pos n)) ＝ pos 0
  γ = ℤ+-lc (succℤ (succℤ (pos n))) (pos 0) x I

ℤ-zero-less-than-pos : (n : ℕ) → pos 0 < pos (succ n)
ℤ-zero-less-than-pos n = ℕ-order-respects-ℤ-order 0 (succ n) (zero-least n)

ℤ-zero-least-pos : (n : ℕ) → pos 0 ≤ pos n
ℤ-zero-least-pos 0 = ℤ≤-refl (pos 0)
ℤ-zero-least-pos (succ n) = γ
 where
  I : pos 0 ≤ pos n
  I = ℤ-zero-least-pos n

  II : pos n ≤ pos (succ n)
  II = ≤-incrℤ (pos n)

  γ : pos 0 ≤ pos (succ n)
  γ = ℤ≤-trans (pos 0) (pos n) (pos (succ n)) I II

negative-less-than-positive : (x y : ℕ) → negsucc x < pos y
negative-less-than-positive x y = (x ℕ+ y) , I
 where
  I : succℤ (negsucc x) + pos (x ℕ+ y) ＝ pos y
  I = succℤ (negsucc x) + pos (x ℕ+ y)        ＝⟨ i    ⟩
      succℤ (negsucc x) + (pos x + pos y)     ＝⟨ ii   ⟩
      succℤ (negsucc x) + pos x + pos y       ＝⟨ iii  ⟩
      negsucc x + pos (succ x) + pos y        ＝⟨ refl ⟩
      (- pos (succ x)) + pos (succ x) + pos y ＝⟨ iv   ⟩
      pos 0 + pos y                           ＝⟨ v    ⟩
      pos y                                   ∎
   where
    i   = ap (succℤ (negsucc x) +_) (distributivity-pos-addition x y ⁻¹)
    ii  = ℤ+-assoc (succℤ (negsucc x)) (pos x) (pos y) ⁻¹
    iii = ap (_+ pos y) (ℤ-left-succ (negsucc x) (pos x))
    iv  = ap (_+ pos y) (ℤ-sum-of-inverse-is-zero' (pos (succ x)))
    v   = ℤ-zero-left-neutral (pos y)

ℤ≤-swap : (x y : ℤ) → x ≤ y → - y ≤ - x
ℤ≤-swap x y (k , e) = k , ℤ+-lc ((- y) + pos k) (- x) (y + x) I
 where
  I : y + x + ((- y) + pos k) ＝ y + x - x
  I = y + x + ((- y) + pos k) ＝⟨ i             ⟩
      x + y + ((- y) + pos k) ＝⟨ ii            ⟩
      x + y - y + pos k       ＝⟨ iii           ⟩
      x + (y - y) + pos k     ＝⟨ iv            ⟩
      x + pos 0 + pos k       ＝⟨ by-definition ⟩
      x + pos k               ＝⟨ e             ⟩
      y                       ＝⟨ by-definition ⟩
      y + pos 0               ＝⟨ v             ⟩
      y + (x - x)             ＝⟨ vi            ⟩
      y + x - x               ∎
   where
    i   = ap (_+ ((- y) + pos k)) (ℤ+-comm y x)
    ii  = ℤ+-assoc (x + y) (- y) (pos k) ⁻¹
    iii = ap (_+ pos k) (ℤ+-assoc x y (- y))
    iv  = ap (λ α → x + α + (pos k)) (ℤ-sum-of-inverse-is-zero y)
    v   = ap (y +_) (ℤ-sum-of-inverse-is-zero x ⁻¹)
    vi  = ℤ+-assoc y x (- x) ⁻¹

ℤ≤-swap₂ : (x y z : ℤ) → x ≤ y ≤ z → (- y ≤ - x) × (- z ≤ - y)
ℤ≤-swap₂ x y z (l₁ , l₂) = (ℤ≤-swap x y l₁) , (ℤ≤-swap y z l₂)

ℕ≤-to-ℤ≤ : (x y : ℕ) → x ≤ y → pos x ≤ pos y
ℕ≤-to-ℤ≤ x y l = I (subtraction x y l)
 where
  I : (Σ k ꞉ ℕ , k ℕ+ x ＝ y) → pos x ≤ pos y
  I (k , e) = k , II
   where
    II : pos x + pos k ＝ pos y
    II = pos x + pos k ＝⟨ distributivity-pos-addition x k     ⟩
         pos (x ℕ+ k)  ＝⟨ ap pos (addition-commutativity x k) ⟩
         pos (k ℕ+ x)  ＝⟨ ap pos e                            ⟩
         pos y         ∎

ℤ-dichotomous : (x y : ℤ) → (x ≤ y) ∔ (y ≤ x)
ℤ-dichotomous (pos x) (pos y) = I (≤-dichotomous x y)
 where
  I : (x ≤ y) ∔ (y ≤ x) → (pos x ≤ pos y) ∔ (pos y ≤ pos x)
  I (inl l) = inl (ℕ≤-to-ℤ≤ x y l)
  I (inr r) = inr (ℕ≤-to-ℤ≤ y x r)
ℤ-dichotomous (pos x) (negsucc y) = inr (negative-less-than-positive (succ y) x)
ℤ-dichotomous (negsucc x) (pos y) = inl (negative-less-than-positive (succ x) y)
ℤ-dichotomous (negsucc x) (negsucc y) = Cases (≤-dichotomous x y) γ₁ γ₂
 where
  I : (a b : ℕ) → a ≤ b → negsucc b ≤ negsucc a
  I a b l = ℤ≤-swap (pos (succ a)) (pos (succ b)) II
   where
    II : pos (succ a) ≤ pos (succ b)
    II = ℕ≤-to-ℤ≤ (succ a) (succ b) l

  γ₁ : x ≤ y → (negsucc x ≤ negsucc y) ∔ (negsucc y ≤ negsucc x)
  γ₁ l = inr (I x y l)

  γ₂ : y ≤ x → (negsucc x ≤ negsucc y) ∔ (negsucc y ≤ negsucc x)
  γ₂ l = inl (I y x l)

trich-locate : (x y : ℤ) → 𝓤₀ ̇
trich-locate x y = (x < y) ∔ (x ＝ y) ∔ (y < x)

ℤ-trichotomous : (x y : ℤ) → trich-locate x y
ℤ-trichotomous x y = I (ℤ-dichotomous x y)
 where
  I : (x ≤ y) ∔ (y ≤ x) → (x < y) ∔ (x ＝ y) ∔ (y < x)
  I (inl l) = II (ℤ≤-split x y l)
   where
    II : (x < y) ∔ (x ＝ y) → (x < y) ∔ (x ＝ y) ∔ (y < x)
    II (inl l) = inl l
    II (inr r) = inr (inl r)
  I (inr r) = II (ℤ≤-split y x r)
   where
    II : (y < x) ∔ (y ＝ x) → (x < y) ∔ (x ＝ y) ∔ (y < x)
    II (inl l) = inr (inr l)
    II (inr r) = inr (inl (r ⁻¹))

ℤ-dichotomous' : (x y : ℤ) → x < y ∔ y ≤ x
ℤ-dichotomous' x y = I (ℤ-trichotomous x y)
 where
  I : (x < y) ∔ (x ＝ y) ∔ (y < x) → x < y ∔ y ≤ x
  I (inl x<y) = inl x<y
  I (inr (inl x＝y)) = inr (transport (_≤ x) x＝y (ℤ≤-refl x))
  I (inr (inr y<x)) = inr (<-is-≤ y x y<x)

ℤ-trichotomous-is-prop : (x y : ℤ) → is-prop (trich-locate x y)
ℤ-trichotomous-is-prop x y = +-is-prop I II γ
 where
  I : is-prop (x < y)
  I = ℤ<-is-prop x y

  II : is-prop ((x ＝ y) ∔ y < x)
  II = +-is-prop ℤ-is-set (ℤ<-is-prop y x) III
   where
    III : x ＝ y → ¬ (y < x)
    III e l = ℤ-equal-not-less-than y (transport (y <_) e l)

  γ : x < y → ¬ ((x ＝ y) ∔ y < x)
  γ l (inl e ) = ℤ-equal-not-less-than x (transport (x <_) (e ⁻¹) l)
  γ l (inr l') = ℤ-bigger-or-equal-not-less x y (<-is-≤ x y l) l'

ℤ≤-adding : (a b c d : ℤ) → a ≤ b → c ≤ d → a + c ≤ b + d
ℤ≤-adding a b c d (p , β) (q , β') = (p ℕ+ q) , I
 where
  I : a + c + pos (p ℕ+ q) ＝ b + d
  I = a + c + pos (p ℕ+ q)    ＝⟨ i    ⟩
      a + c + (pos p + pos q) ＝⟨ ii   ⟩
      a + c + pos p + pos q   ＝⟨ iii  ⟩
      c + a + pos p + pos q   ＝⟨ iv   ⟩
      c + (a + pos p) + pos q ＝⟨ v    ⟩
      c + b + pos q           ＝⟨ vi   ⟩
      b + c + pos q           ＝⟨ vii  ⟩
      b + (c + pos q)         ＝⟨ viii ⟩
      b + d                   ∎
   where
    i    = ap (a + c +_) (distributivity-pos-addition p q ⁻¹)
    ii   = ℤ+-assoc (a + c) (pos p) (pos q) ⁻¹
    iii  = ap (λ z → z + pos p + pos q) (ℤ+-comm a c)
    iv   = ap (_+ pos q) (ℤ+-assoc c a (pos p))
    v    = ap (λ z → c + z + pos q) β
    vi   = ap (_+ pos q) (ℤ+-comm c b)
    vii  = ℤ+-assoc b c (pos q)
    viii = ap (b +_) β'

ℤ<-adding : (a b c d : ℤ) → a < b → c < d → a + c < b + d
ℤ<-adding a b c d l₁ l₂ = ℤ<-trans (a + c) (a + succℤ c) (b + d) II III
 where
  I : succℤ a + succℤ c ≤ b + d
  I = ℤ≤-adding (succℤ a) b (succℤ c) d l₁ l₂

  II : a + c < a + succℤ c
  II = 0 , (ℤ-right-succ a c ⁻¹)

  III : a + succℤ c < b + d
  III = transport (_≤ b + d) (ℤ-left-succ a (succℤ c)) I

ℤ≤-adding' :  (a b c : ℤ) → a ≤ b → a + c ≤ b + c
ℤ≤-adding' a b c (k , p) = k , I
 where
  I : a + c + pos k ＝ b + c
  I = a + c + pos k   ＝⟨ ℤ+-assoc a c (pos k)          ⟩
      a + (c + pos k) ＝⟨ ap (a +_) (ℤ+-comm c (pos k)) ⟩
      a + (pos k + c) ＝⟨ ℤ+-assoc a (pos k) c ⁻¹       ⟩
      a + pos k + c   ＝⟨ ap (_+ c) p                   ⟩
      b + c           ∎

ℤ≤-adding-left : (a b c : ℤ) → a ≤ b → c + a ≤ c + b
ℤ≤-adding-left a b c l = transport₂ _≤_ I II III
 where
  I : a + c ＝ c + a
  I = ℤ+-comm a c

  II : b + c ＝ c + b
  II = ℤ+-comm b c

  III : a + c ≤ b + c
  III = ℤ≤-adding' a b c l

ℤ≤-adding₂ : (a b c d : ℤ) → a ≤ b ≤ c → (a + d ≤ b + d ≤ c + d)
ℤ≤-adding₂ a b c d (l₁ , l₂) = (ℤ≤-adding' a b d l₁) , (ℤ≤-adding' b c d l₂)

ℤ<-adding' : (a b c : ℤ) → a < b → a + c < b + c
ℤ<-adding' a b c (k , p) = I (ℤ≤-adding' (succℤ a) b c (k , p))
 where
  I : succℤ a + c ≤ b + c → a + c < b + c
  I (h , q) = h , II
   where
    II : succℤ (a + c) + pos h ＝ b + c
    II = succℤ (a + c) + pos h ＝⟨ ap (_+ (pos h)) (ℤ-left-succ a c ⁻¹) ⟩
         succℤ a + c + pos h   ＝⟨ q                                    ⟩
         b + c                 ∎

ℤ<-adding-left : (a b c : ℤ) → a < b → c + a < c + b
ℤ<-adding-left a b c l = transport₂ _<_ I II III
 where
  I : a + c ＝ c + a
  I = ℤ+-comm a c

  II : b + c ＝ c + b
  II = ℤ+-comm b c

  III : a + c < b + c
  III = ℤ<-adding' a b c l

ℤ<-adding'' : (a b c : ℤ) → a < b → c + a < c + b
ℤ<-adding'' a b c l = transport₂ _<_ (ℤ+-comm a c) (ℤ+-comm b c) I
 where
  I : a + c < b + c
  I = ℤ<-adding' a b c l

pmpo-lemma : (a b : ℤ) → (n : ℕ) → a < b →  a * pos (succ n) < b * pos (succ n)
pmpo-lemma a b = induction base step
 where
  base : a < b
       → a * pos 1 < b * pos 1
  base z = z

  step : (k : ℕ)
       → (a < b → a * pos (succ k) < b * pos (succ k))
       → a < b
       → a * pos (succ (succ k)) < b * pos (succ (succ k))
  step k IH l = ℤ<-adding a b (a + (a * pos k)) (b + (b * pos k)) l (IH l)

positive-multiplication-preserves-order : (a b c : ℤ)
                                        → is-pos-succ c
                                        → a < b
                                        → a * c < b * c
positive-multiplication-preserves-order a b (negsucc x)    p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos 0)        p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos (succ x)) p l = pmpo-lemma a b x l

positive-multiplication-preserves-order' : (a b c : ℤ)
                                         → is-pos-succ c
                                         → a ≤ b
                                         → a * c ≤ b * c
positive-multiplication-preserves-order' a b c p l = I (ℤ≤-split a b l)
 where
  I : (a < b) ∔ (a ＝ b) → a * c ≤ b * c
  I (inl l) = <-is-≤ (a * c) (b * c) γ
   where
    γ :  a * c < b * c
    γ = positive-multiplication-preserves-order a b c p l
  I (inr e) = transport (_≤ b * c) γ (ℤ≤-refl (b * c))
   where
    γ : b * c ＝ a * c
    γ = ap (_* c) (e ⁻¹)

ℤ*-multiplication-order : (a b c : ℤ)
                        → pos 0 ≤ c
                        → a ≤ b
                        → a * c ≤ b * c
ℤ*-multiplication-order a b (pos 0) p l = ℤ≤-refl (pos 0)
ℤ*-multiplication-order a b (pos (succ c)) p l
 = positive-multiplication-preserves-order' a b (pos (succ c)) ⋆ l
ℤ*-multiplication-order a b (negsucc c) p l = 𝟘-elim γ
 where
  I : negsucc c < pos 0
  I = negative-less-than-positive c 0

  γ : 𝟘
  γ = ℤ-bigger-or-equal-not-less (pos 0) (negsucc c) p I

nmco-lemma : (a b : ℤ) → (c : ℕ) → a < b → b * (negsucc c) < a * (negsucc c)
nmco-lemma a b = induction base step
 where
  base : a < b → b * negsucc 0 < a * negsucc 0
  base (k , γ) = k , I
   where
    II : (- b) + pos k + (a - a) ＝ a + pos k + ((- b) - a)
    II = (- b) + pos k + (a - a)    ＝⟨ i   ⟩
          pos k - b + (a - a)       ＝⟨ ii  ⟩
          pos k - b + a - a         ＝⟨ iii ⟩
          a + (pos k - b) - a       ＝⟨ iv  ⟩
          a + pos k - b - a         ＝⟨ v   ⟩
          a + pos k + ((- b) - a)   ∎
     where
      i   = ap (_+ (a - a)) (ℤ+-comm (- b) (pos k))
      ii  = ℤ+-assoc (pos k - b) a (- a) ⁻¹
      iii = ap (_+ (- a)) (ℤ+-comm (pos k - b) a)
      iv  = ap (_+ (- a)) (ℤ+-assoc a (pos k) (- b) ⁻¹)
      v   = ℤ+-assoc (a + pos k) (- b) (- a)

    I : succℤ (b * negsucc 0) + pos k ＝ a * negsucc 0
    I = succℤ (b * negsucc 0) + pos k    ＝⟨ by-definition ⟩
        succℤ (- b) + pos k              ＝⟨ i             ⟩
        succℤ ((- b) + pos k)            ＝⟨ ii            ⟩
        succℤ ((- b) + pos k) + pos 0    ＝⟨ iii           ⟩
        succℤ ((- b) + pos k) + (a - a)  ＝⟨ iv            ⟩
        succℤ ((- b) + pos k + (a - a))  ＝⟨ v             ⟩
        succℤ (a + pos k + ((- b) - a))  ＝⟨ vi            ⟩
        succℤ (a + pos k) + ((- b) - a)  ＝⟨ vii           ⟩
        succℤ a + pos k + ((- b) - a)    ＝⟨ viii          ⟩
        b + ((- b) - a)                  ＝⟨ ix            ⟩
        b - b - a                        ＝⟨ x             ⟩
        pos 0 - a                        ＝⟨ xi            ⟩
        - a                              ＝⟨ by-definition ⟩
        a * negsucc 0                    ∎
     where
       i    = ℤ-left-succ (- b) (pos k)
       ii   = ℤ-zero-right-neutral (succℤ ((- b) +pos k))
       iii  = ap (succℤ ((- b) + pos k) +_) (ℤ-sum-of-inverse-is-zero a ⁻¹)
       iv   = ℤ-left-succ ((- b) + pos k) (a - a)
       v    = ap succℤ II
       vi   = ℤ-left-succ (a + pos k) ((- b) - a) ⁻¹
       vii  = ap (_+ ((- b) - a)) (ℤ-left-succ a (pos k) ⁻¹)
       viii = ap (_+ ((- b) - a)) γ
       ix   = ℤ+-assoc b (- b) (- a) ⁻¹
       x    = ap (_+ (- a)) (ℤ-sum-of-inverse-is-zero b)
       xi   = ℤ-zero-left-neutral (- a)

  step : (k : ℕ)
       → (a < b → b * negsucc k < a * negsucc k)
       →  a < b → b * negsucc (succ k) < a * negsucc (succ k)
  step k IH l = ℤ<-adding (- b) (- a) (b * negsucc k) (a * negsucc k) I II
   where
    I : - b < - a
    I = base l
    II :  b * negsucc k < a * negsucc k
    II = IH l

negative-multiplication-changes-order : (a b c : ℤ)
                                      → negative c
                                      → a < b
                                      → b * c < a * c
negative-multiplication-changes-order a b (pos c)     g l = 𝟘-elim g
negative-multiplication-changes-order a b (negsucc c) g l = nmco-lemma a b c l

negative-multiplication-changes-order' : (a b c : ℤ)
                                       → negative c
                                       → a ≤ b
                                       → b * c ≤ a * c
negative-multiplication-changes-order' a b (pos x) g l = 𝟘-elim g
negative-multiplication-changes-order' a b (negsucc x) g l = I (ℤ≤-split a b l)
 where
  I : a < b ∔ (a ＝ b) → b * negsucc x ≤ a * negsucc x
  I (inl a<b) = <-is-≤ (b * negsucc x) (a * negsucc x) γ
   where
    γ : b * negsucc x < a * negsucc x
    γ = negative-multiplication-changes-order a b (negsucc x) ⋆ a<b
  I (inr a＝b) = transport (b * negsucc x ≤ℤ_) γ₁ γ₂
   where
    γ₁ : b * negsucc x ＝ a * negsucc x
    γ₁ = ap (_* negsucc x) (a＝b ⁻¹)

    γ₂ : b * negsucc x ≤ b * negsucc x
    γ₂ = ℤ≤-refl (b * negsucc x)

ℤ-mult-right-cancellable : (x y z : ℤ) → not-zero z → x * z ＝ y * z → x ＝ y
ℤ-mult-right-cancellable x y (pos 0)        nz e = 𝟘-elim (nz ⋆)
ℤ-mult-right-cancellable x y (pos (succ z)) nz e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ＝ y) ∔ (y < x) → x ＝ y
  tri-split (inl l) = 𝟘-elim (ℤ-equal-not-less-than (x * pos (succ z)) II)
   where
    I : x * pos (succ z) < y * pos (succ z)
    I = positive-multiplication-preserves-order x y (pos (succ z)) ⋆ l

    II : x * pos (succ z) < x * pos (succ z)
    II = transport (x * pos (succ z) <_) (e ⁻¹) I

  tri-split (inr (inl m)) = m
  tri-split (inr (inr r)) = 𝟘-elim (ℤ-equal-not-less-than (y * pos (succ z)) II)
   where
    I : y * pos (succ z) < x * pos (succ z)
    I = positive-multiplication-preserves-order y x (pos (succ z)) ⋆ r

    II : y * pos (succ z) < y * pos (succ z)
    II = transport (y * pos (succ z) <_) e I
ℤ-mult-right-cancellable x y (negsucc z)    nz e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ＝ y) ∔ (y < x) → x ＝ y
  tri-split (inl l) = 𝟘-elim (ℤ-equal-not-less-than (y * negsucc z) II)
   where
    I : y * negsucc z < x * negsucc z
    I = nmco-lemma x y z l

    II : y * negsucc z < y * negsucc z
    II = transport (y * negsucc z <_) e I

  tri-split (inr (inl r)) = r
  tri-split (inr (inr r)) = 𝟘-elim (ℤ-equal-not-less-than (x * negsucc z) II)
   where
    I : (x * negsucc z) < (y * negsucc z)
    I = nmco-lemma y x z r

    II : x * negsucc z < x * negsucc z
    II = transport (x * negsucc z <_) (e ⁻¹) I

ℤ-mult-left-cancellable : (x y z : ℤ) → not-zero z
                                      → z * x ＝ z * y
                                      → x ＝ y
ℤ-mult-left-cancellable x y z nz e = ℤ-mult-right-cancellable x y z nz I
 where
  I : x * z ＝ y * z
  I = x * z   ＝⟨ ℤ*-comm x z ⟩
      z * x   ＝⟨ e           ⟩
      z * y   ＝⟨ ℤ*-comm z y ⟩
      y * z   ∎

non-zero-multiplication : (x y : ℤ) → ¬ (x ＝ pos 0) → ¬ (y ＝ pos 0) → ¬ (x * y ＝ pos 0)
non-zero-multiplication (pos 0)        y xnz ynz e = xnz refl
non-zero-multiplication (pos (succ x)) y xnz ynz e = ynz γ
 where
  γ : y ＝ pos 0
  γ = ℤ-mult-left-cancellable y (pos 0) (pos (succ x)) id e
non-zero-multiplication (negsucc x)    y xnz ynz e = ynz γ
 where
  γ : y ＝ pos 0
  γ = ℤ-mult-left-cancellable y (pos 0) (negsucc x) id e

orcl : (a b : ℤ) → (n : ℕ) → a * (pos (succ n)) ≤ b * (pos (succ n)) → a ≤ b
orcl a b = induction base step
 where
  base : a * pos 1 ≤ b * pos 1 → a ≤ b
  base = id

  step : (k : ℕ)
       → (a * pos (succ k) ≤ b * pos (succ k) → a ≤ b)
       → a * pos (succ (succ k)) ≤ b * pos (succ (succ k))
       → a ≤ b
  step k IH (α , β) = cases₃ γ₁ γ₂ γ₃ (ℤ-trichotomous a b)
   where
    k' = pos (succ (succ k))

    γ₁ : a < b → a ≤ b
    γ₁ = <-is-≤ a b

    γ₂ : a ＝ b → a ≤ b
    γ₂ e = transport (a ≤_) e (ℤ≤-refl a)

    γ₃ : b < a → a ≤ b
    γ₃ l = 𝟘-elim III
     where
      I : a * k' ≤ b * k'
      I = α , β

      II : b * k' < a * k'
      II = positive-multiplication-preserves-order b a k' ⋆ l

      III : 𝟘
      III = ℤ-bigger-or-equal-not-less (a * k') (b * k') I II

orcl' : (a b : ℤ) → (n : ℕ) → a * (pos (succ n)) < b * (pos (succ n)) → a < b
orcl' a b n l = II (ℤ≤-split a b I)
 where
  I : a ≤ b
  I = orcl a b n (<-is-≤ (a * pos (succ n)) (b * pos (succ n)) l)
  II : a < b ∔ (a ＝ b) → a < b
  II (inl l) = l
  II (inr e) = 𝟘-elim (ℤ-equal-not-less-than (a * pos (succ n)) III)
   where
    III : a * pos (succ n) < a * pos (succ n)
    III = transport (λ - → (a * pos (succ n)) < (- * pos (succ n))) (e ⁻¹) l

ordering-right-cancellable : (a b c : ℤ) → is-pos-succ c → a * c < b * c → a < b
ordering-right-cancellable a b (negsucc x) p l    = 𝟘-elim p
ordering-right-cancellable a b (pos 0) p l        = 𝟘-elim p
ordering-right-cancellable a b (pos (succ x)) p l = orcl' a b x l

ℤ≤-ordering-right-cancellable : (a b c : ℤ)
                              → is-pos-succ c → a * c ≤ b * c → a ≤ b
ℤ≤-ordering-right-cancellable a b (pos zero) p l     = 𝟘-elim p
ℤ≤-ordering-right-cancellable a b (pos (succ x)) p l = orcl a b x l
ℤ≤-ordering-right-cancellable a b (negsucc x) p l    = 𝟘-elim p

ℤ≤-anti : (x y : ℤ) → x ≤ y → y ≤ x → x ＝ y
ℤ≤-anti x y l₁ l₂ = I (ℤ≤-split x y l₁) (ℤ≤-split y x l₂)
 where
  I : x < y ∔ (x ＝ y) → y < x ∔ (y ＝ x)
    → x ＝ y
  I (inl x<y) (inr e)   = e ⁻¹
  I (inr e)   (inl y<x) = e
  I (inr e)   (inr e')  = e
  I (inl x<y) (inl y<x) = 𝟘-elim III
   where
    II : x < x
    II = ℤ<-trans x y x x<y y<x

    III : 𝟘
    III = ℤ-equal-not-less-than x II

maxℤ : ℤ → ℤ → ℤ
maxℤ x y with ℤ-dichotomous x y
... | inl x≤y = y
... | inr y≤x = x

max₂ : ℤ → ℤ → ℤ → ℤ
max₂ x y z = maxℤ (maxℤ x y) z

max₃ : ℤ → ℤ → ℤ → ℤ → ℤ
max₃ w x y z = maxℤ (max₂ w x y) z

minℤ : ℤ → ℤ → ℤ
minℤ x y with ℤ-dichotomous x y
... | inl x≤y = x
... | inr y≤x = y

min₂ : ℤ → ℤ → ℤ → ℤ
min₂ x y z = minℤ (minℤ x y) z

min₃ : ℤ → ℤ → ℤ → ℤ → ℤ
min₃ w x y z = minℤ (min₂ w x y) z

\end{code}

Added by Todd

\begin{code}

ℤ≤-attach : (x y : ℤ) → (y ＝ x) ∔ (x < y) → x ≤ y
ℤ≤-attach x x (inl refl) = 0 , refl
ℤ≤-attach x y (inr (a , p)) = succ a , (ℤ-left-succ-pos x a ⁻¹ ∙ p)

ℤ≤-same-witness : (x y : ℤ) → ((n , _) (m , _) : x ≤ y) → n ＝ m
ℤ≤-same-witness x y p q = ap pr₁ (ℤ≤-is-prop x y p q)

ℤ≤-add-witness : (x y z : ℤ) → ((n , p) : x ≤ y) ((m , q) : y ≤ z)
               → ((o , r) : x ≤ z)
               → o ＝ n ℕ+ m
ℤ≤-add-witness x y z x≤y y≤z x≤z
 = ℤ≤-same-witness x z x≤z (ℤ≤-trans x y z x≤y y≤z)

ℤ-less-not-bigger-or-equal : (x y : ℤ) → x < y → ¬ (y ≤ x)
ℤ-less-not-bigger-or-equal x y x<y y≤x
 = ℤ-bigger-or-equal-not-less y x y≤x x<y

\end{code}

Lane Biocini, 07 September 2023

A proof of the triangle inequality in the Integers using the Absolute
Difference operation defined in the Naturals. We first prove a convenience
lemma.

\begin{code}

ℕ-order-respects-ℤ-order'' : (m n : ℕ) → m ≤ n → pos m ≤ pos n
ℕ-order-respects-ℤ-order'' zero n l = ℤ-zero-least-pos n
ℕ-order-respects-ℤ-order'' (succ m) n l = ℕ-order-respects-ℤ-order m n l

triangle-inequality₀ : (x y : ℕ) → abs (pos x +pos y) ≤ℕ abs (pos x) ℕ+ abs (pos y)
triangle-inequality₀ x y = transport (_≤ℕ x ℕ+ y) Γ (≤-refl (x ℕ+ y))
 where
  Γ : x ℕ+ y ＝ abs (pos x +pos y)
  Γ = x ℕ+ y ＝⟨ ap abs (distributivity-pos-addition x y) ⁻¹ ⟩
    abs (pos x +pos y) ∎

triangle-inequality₁ : (x y : ℕ) → abs (pos x +negsucc y) ≤ℕ succ (x ℕ+ y)
triangle-inequality₁ x y = transport (_≤ℕ succ (x ℕ+ y)) Γ γ
 where
  Γ : ∣ x - succ y ∣ ＝ abs (pos x +negsucc y)
  Γ = abs-pos-plus-negsucc x y ⁻¹

  γ : ∣ x - succ y ∣ ≤ℕ succ (x ℕ+ y)
  γ = triangle-inequality x 0 (succ y)

triangle-inequality₂ : (x y : ℕ) → abs (negsucc x +pos y) ≤ℕ (succ x ℕ+ y)
triangle-inequality₂ x y = transport₂ _≤ℕ_ I II (triangle-inequality₁ y x)
 where
  I : abs (pos y +negsucc x) ＝ abs (negsucc x +pos y)
  I = ap abs (ℤ+-comm (pos y) (negsucc x))

  II : succ (y ℕ+ x) ＝ succ x ℕ+ y
  II = ap succ (addition-commutativity y x) ∙ succ-left x y ⁻¹

triangle-inequality₃ : (x y : ℕ) → abs (negsucc x +negsucc y) ≤ℕ succ (succ x ℕ+ y)
triangle-inequality₃ x y = transport (_≤ℕ succ (succ x ℕ+ y)) Γ γ
 where
  Γ : abs (pos (succ x) + pos (succ y)) ＝ abs (negsucc x +negsucc y)
  Γ = abs (succℤ (pos (succ x) +pos y))   ＝⟨ i ⟩
      abs (- succℤ (pos (succ x) +pos y)) ＝⟨ ii ⟩
      abs (negsucc x +negsucc y)          ∎
   where
    i = abs-removes-neg-sign (succℤ (pos (succ x) +pos y))
    ii = ap abs (negation-dist (pos (succ x)) (pos (succ y))) ⁻¹

  γ : abs (pos (succ x) + pos (succ y)) ≤ℕ succ (succ x ℕ+ y)
  γ = triangle-inequality₀ (succ x) (succ y)

ℤ-triangle-inequality : (x y : ℤ) → abs (x + y) ≤ℕ abs x ℕ+ abs y
ℤ-triangle-inequality (pos x) (pos y) = triangle-inequality₀ x y
ℤ-triangle-inequality (pos x) (negsucc y) = triangle-inequality₁ x y
ℤ-triangle-inequality (negsucc x) (pos y) = triangle-inequality₂ x y
ℤ-triangle-inequality (negsucc x) (negsucc y) = triangle-inequality₃ x y

ℤ-triangle-inequality' : (x y : ℤ) → absℤ (x + y) ≤ℤ absℤ x + absℤ y
ℤ-triangle-inequality' x y = transport₂ _≤ℤ_ I II γ
 where
  I : pos (abs (x + y)) ＝ absℤ (x + y)
  I = pos-abs-is-absℤ (x + y)

  II : pos (abs x ℕ+ abs y) ＝ absℤ x + absℤ y
  II = pos (abs x ℕ+ abs y)   ＝⟨ i ⟩
     (pos (abs x) +pos abs y) ＝⟨ ii ⟩
     absℤ x + absℤ y          ∎
   where
    i = distributivity-pos-addition (abs x) (abs y) ⁻¹
    ii : (pos (abs x) +pos abs y) ＝ absℤ x + absℤ y
    ii = ap₂ (λ x y → x + y) (pos-abs-is-absℤ x) (pos-abs-is-absℤ y)

  γ : pos (abs (x + y)) ≤ℤ pos (abs x ℕ+ abs y)
  γ = ℕ-order-respects-ℤ-order'' (abs (x + y)) (abs x ℕ+ abs y) (ℤ-triangle-inequality x y)
