Andrew Sneap - 26th November 2021

In this file, I define order of integers, and prove some common properties of order.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import NaturalsOrder 
open import OrderNotation --TypeTopology
open import UF-Base 
open import UF-Subsingletons

open import IntegersAbs
open import IntegersB
open import IntegersAddition
open import IntegersMultiplication
open import IntegersNegation
open import MoreNaturalProperties
open import NaturalsAddition renaming (_+_ to _ℕ+_)
open import NaturalsOrderExtended

open import NaturalsOrderExtended

module IntegersOrder where

\end{code}

First, the definition of < and ≤ for the integers. See the NaturalsOrder import to see how < is defined similarly to < for the natural numbers.  Following the definitions are the proofs that the relations are propositions, and some simple proofs for each.

\begin{code}

_≤ℤ_ _≥ℤ_ : (x y : ℤ) → 𝓤₀ ̇
x ≤ℤ y = Σ n ꞉ ℕ , x + pos n ≡ y
x ≥ℤ y = y ≤ℤ x

instance
 Order-ℤ-ℤ : Order ℤ ℤ
 _≤_ {{Order-ℤ-ℤ}} = _≤ℤ_
 
_<ℤ_ _>ℤ_ : (x y : ℤ) → 𝓤₀ ̇
x <ℤ y = succℤ x ≤ y
x >ℤ y = y <ℤ x

instance
 Strict-Order-ℤ-ℤ : Strict-Order ℤ ℤ
 _<_ {{Strict-Order-ℤ-ℤ}} = _<ℤ_

ℤ≤-is-prop : (x y : ℤ) → is-prop (x ≤ y)
ℤ≤-is-prop x y (n , p) (m , q) = to-subtype-≡ (λ _ → ℤ-is-set) (pos-lc (ℤ+-lc (pos n) (pos m) x (p ∙ (q ⁻¹))))

ℤ<-is-prop : (x y : ℤ) → is-prop (x < y)
ℤ<-is-prop x = ℤ≤-is-prop (succℤ x)

≤-incrℤ : (x : ℤ) → x ≤ succℤ x
≤-incrℤ x = 1 , refl

<-incrℤ : (x : ℤ) → x < succℤ x
<-incrℤ x = 0 , refl

≤-predℤ : (x : ℤ) → predℤ x ≤ x
≤-predℤ x = 1 , succpredℤ x

<-predℤ : (x : ℤ) → predℤ x < x
<-predℤ x = 0 , succpredℤ x

<-is-≤ : (x y : ℤ) → x < y → x ≤ y
<-is-≤ x y (a , p) = succ a , (ℤ-left-succ x (pos a) ⁻¹ ∙ p)

ℤ-bigger-or-equal-not-less : (x y : ℤ) → x ≤ y → ¬ (y < x)
ℤ-bigger-or-equal-not-less x y (α , p) (β , q) = 𝟘-elim (pos-int-not-zero (α ℕ+ β) II)
 where
  I : x + succℤ (pos (α ℕ+ β)) ≡ x + pos 0
  I = x + succℤ (pos (α ℕ+ β))    ≡⟨ ap (λ - → x + succℤ -) (pos-addition-equiv-to-ℕ α β ⁻¹) ⟩
      x + succℤ (pos α + pos β)   ≡⟨ ℤ-right-succ x (pos α + pos β) ⟩
      succℤ (x + (pos α + pos β)) ≡⟨ ap succℤ (ℤ+-assoc x (pos α) (pos β) ⁻¹) ⟩
      succℤ ((x + pos α) + pos β) ≡⟨ ℤ-left-succ (x + pos α) (pos β) ⁻¹ ⟩
      succℤ (x + pos α) + pos β   ≡⟨ transport (λ - → succℤ - + (pos β) ≡ x) (p ⁻¹) q ⟩
      x                           ≡⟨ by-definition ⟩
      x + pos 0 ∎
  II : succℤ (pos (α ℕ+ β)) ≡ pos 0
  II = ℤ+-lc (succℤ (pos (α ℕ+ β))) (pos 0) x I

ℤ≤-split : (x y : ℤ) → x ≤ y → (x < y) ∔ (x ≡ y)
ℤ≤-split x y (zero , p) = inr p
ℤ≤-split x y (succ a , p) = inl (a , (ℤ-left-succ x (pos a)  ∙ p))

ℤ≤-trans : (x y z : ℤ) → x ≤ y → y ≤ z → x ≤ z
ℤ≤-trans x y z (a , p) (b , q) = a ℕ+ b , I
 where
  I : x + pos (a ℕ+ b) ≡ z
  I = x + pos (a ℕ+ b)        ≡⟨ ap (x +_) (pos-addition-equiv-to-ℕ a b ⁻¹) ⟩
      x + ((pos a) + (pos b)) ≡⟨ ℤ+-assoc x (pos a) (pos b) ⁻¹ ⟩
      (x + pos a) + (pos b)   ≡⟨ ap (_+ (pos b)) p ⟩
      y + (pos b)             ≡⟨ q ⟩
      z ∎

ℤ<-trans : (x y z : ℤ) → x < y → y < z → x < z
ℤ<-trans x y z l₁ l₂ = ℤ≤-trans (succℤ x) (succℤ y) z I l₂
 where
  I : succℤ x ≤ succℤ y
  I = ℤ≤-trans (succℤ x) y (succℤ y) l₁ (≤-incrℤ y)

ℤ≤-refl : (x : ℤ) → x ≤ x
ℤ≤-refl x = 0 , refl

ℤ-equal-not-less-than : (x : ℤ) → ¬ (x < x)
ℤ-equal-not-less-than x (0 , α)      = succℤ-no-fp x (α ⁻¹)
ℤ-equal-not-less-than x (succ n , α) = pos-int-not-zero (n ℕ+ 1) (ℤ+-lc (succℤ (succℤ (pos n))) (pos 0) x I)
 where
  I : x + succℤ (succℤ (pos n)) ≡ x + pos 0
  I = x + succℤ (succℤ (pos n)) ≡⟨ ℤ-right-succ x (succℤ (pos n)) ⟩
     succℤ (x + succℤ (pos n))  ≡⟨ ℤ-left-succ x (succℤ (pos n)) ⁻¹ ⟩
     succℤ x + succℤ (pos n)    ≡⟨ by-definition ⟩
     succℤ x + pos (succ n)     ≡⟨ α ⟩
     x ≡⟨ ℤ-zero-right-neutral x ⟩
     x + pos 0 ∎

ℤ-zero-less-than-pos : (n : ℕ) → pos 0 < pos (succ n)
ℤ-zero-less-than-pos 0     = 0 , refl
ℤ-zero-less-than-pos (succ n) = ℤ<-trans (pos 0) (pos (succ n)) (pos (succ (succ n))) IH (<-incrℤ (pos (succ n)))
 where
  IH : pos 0 < pos (succ n)
  IH = ℤ-zero-less-than-pos n

negative-less-than-positive : (x y : ℕ) → negsucc x < pos y
negative-less-than-positive x y = (x ℕ+ y) , I
 where
  I : succℤ (negsucc x) + pos (x ℕ+ y) ≡ pos y
  I = succℤ (negsucc x) + pos (x ℕ+ y)    ≡⟨ ap (succℤ (negsucc x) +_) (pos-addition-equiv-to-ℕ x y ⁻¹) ⟩
      succℤ (negsucc x) + (pos x + pos y)     ≡⟨ ℤ+-assoc (succℤ (negsucc x)) (pos x) (pos y) ⁻¹ ⟩
      succℤ (negsucc x) + pos x + pos y       ≡⟨ ap (_+ pos y) (ℤ-left-succ (negsucc x) (pos x)) ⟩
      negsucc x + pos (succ x) + pos y        ≡⟨ refl ⟩
      (- pos (succ x)) + pos (succ x) + pos y ≡⟨ ap (_+ pos y) (ℤ-sum-of-inverse-is-zero' (pos (succ x))) ⟩
      pos 0 + pos y                           ≡⟨ ℤ-zero-left-neutral (pos y) ⟩
      pos y                                   ∎  

ℕ-order-respects-ℤ-order : (m n : ℕ) → m < n → pos m < pos n
ℕ-order-respects-ℤ-order m n l = I (subtraction'' m n l)
 where
  I : (Σ k ꞉ ℕ , succ k ℕ+ m ≡ n) → pos m < pos n
  I (k , e) = k , II
   where
    II : succℤ (pos m) + pos k ≡ pos n
    II = succℤ (pos m) + pos k ≡⟨ pos-addition-equiv-to-ℕ (succ m) k ⟩
         pos (succ m ℕ+ k)     ≡⟨ ap pos (addition-commutativity (succ m) k) ⟩
         pos (k ℕ+ succ m)     ≡⟨ ap pos (succ-left k m ⁻¹) ⟩
         pos (succ k ℕ+ m)     ≡⟨ ap pos e ⟩
         pos n                 ∎

ℕ-order-respects-ℤ-order' : (m n : ℕ) → m < n → negsucc n < negsucc m
ℕ-order-respects-ℤ-order' m n l = I (subtraction'' m n l)
 where
  I : (Σ k ꞉ ℕ , succ k ℕ+ m ≡ n) → negsucc n < negsucc m
  I (k , e) = k , conclusion
   where
    II : pos (succ k ℕ+ succ m) ≡ pos (succ n)
    II = ap (λ p → pos (succ p)) e
    III : pos (succ k) + pos (succ m) ≡ pos (succ n)
    III = pos-addition-equiv-to-ℕ (succ k) (succ m) ∙ II
    IV : pos (succ k) + pos (succ m) + (negsucc n + negsucc m) ≡ pos (succ n) + (negsucc n + negsucc m)
    IV = ap (λ p → p + (negsucc n + negsucc m)) III
    conclusion : succℤ (negsucc n) + pos k ≡ negsucc m
    conclusion = succℤ (negsucc n) + pos k                             ≡⟨ ℤ-left-succ (negsucc n) (pos k) ⟩
                 negsucc n + pos (succ k)                              ≡⟨ ℤ+-comm (negsucc n) (pos (succ k)) ⟩
                 pos (succ k) + negsucc n                              ≡⟨ ℤ-zero-right-neutral (pos (succ k) + negsucc n) ⟩
                 pos (succ k) + negsucc n + pos 0                      ≡⟨ ap ((pos (succ k) + negsucc n) +_) (ℤ-sum-of-inverse-is-zero (pos (succ m)) ⁻¹) ⟩
                 pos (succ k) + negsucc n + (pos (succ m) + negsucc m) ≡⟨ ℤ+-assoc (pos (succ k) + negsucc n) (pos (succ m)) (negsucc m) ⁻¹ ⟩
                 pos (succ k) + negsucc n + pos (succ m) + negsucc m   ≡⟨ ap (_+ negsucc m) (ℤ+-assoc (pos (succ k)) (negsucc n) (pos (succ m))) ⟩
                 pos (succ k) + (negsucc n + pos (succ m)) + negsucc m ≡⟨ ap (λ p → pos (succ k) + p + negsucc m) (ℤ+-comm (negsucc n) (pos (succ m))) ⟩
                 pos (succ k) + (pos (succ m) + negsucc n) + negsucc m ≡⟨ ap (_+ negsucc m) (ℤ+-assoc (pos (succ k)) (pos (succ m)) (negsucc n) ⁻¹) ⟩
                 pos (succ k) + pos (succ m) + negsucc n + negsucc m   ≡⟨ ℤ+-assoc (pos (succ k) + pos (succ m)) (negsucc n) (negsucc m) ⟩
                 pos (succ k) + pos (succ m) + (negsucc n + negsucc m) ≡⟨ IV ⟩
                 pos (succ n) + (negsucc n + negsucc m)                ≡⟨ ℤ+-assoc (pos (succ n)) (negsucc n) (negsucc m) ⁻¹ ⟩
                 pos (succ n) + negsucc n + negsucc m                  ≡⟨ ap (_+ negsucc m) (ℤ-sum-of-inverse-is-zero (pos (succ n))) ⟩
                 pos 0 + negsucc m                                     ≡⟨ ℤ-zero-left-neutral (negsucc m) ⟩
                 negsucc m ∎

ℤ≤-swap : (x y : ℤ) → x ≤ y → - y ≤ - x
ℤ≤-swap x y (k , e) = k , ℤ+-lc ((- y) + pos k) (- x) (y + x) I
 where 
  I : y + x + ((- y) + pos k) ≡ y + x + (- x)
  I = y + x + ((- y) + pos k)         ≡⟨ ap (_+ ((- y) + pos k)) (ℤ+-comm y x) ⟩
      x + y + ((- y) + pos k)         ≡⟨ ℤ+-assoc (x + y) (- y) (pos k) ⁻¹ ⟩
      x + y + (- y) + pos k           ≡⟨ ap (_+ pos k) (ℤ+-assoc x y (- y)) ⟩
      x + (y + (- y)) + pos k         ≡⟨ ap (λ α → x + α + (pos k)) (ℤ-sum-of-inverse-is-zero y) ⟩
      x + pos 0 + pos k               ≡⟨ by-definition ⟩
      x + pos k                       ≡⟨ e ⟩
      y                               ≡⟨ by-definition ⟩
      y + pos 0                       ≡⟨ ap (y +_) (ℤ-sum-of-inverse-is-zero x ⁻¹) ⟩
      y + (x + (- x))                 ≡⟨ ℤ+-assoc y x (- x ) ⁻¹ ⟩
      y + x + (- x) ∎

ℕ≤-to-ℤ≤ : (x y : ℕ) → x ≤ y → pos x ≤ pos y
ℕ≤-to-ℤ≤ x y l = I (subtraction x y l) 
 where
  I : (Σ k ꞉ ℕ , k ℕ+ x ≡ y) → pos x ≤ pos y
  I (k , e) = k , II
   where
    II : pos x + pos k ≡ pos y
    II = pos x + pos k ≡⟨ pos-addition-equiv-to-ℕ x k ⟩
         pos (x ℕ+ k)  ≡⟨ ap pos (addition-commutativity x k) ⟩
         pos (k ℕ+ x)          ≡⟨ ap pos e ⟩
         pos y         ∎
         
ℤ-dichotomous : (x y : ℤ) → x ≤ y ∔ y ≤ x
ℤ-dichotomous (pos x) (pos y) = I (≤-dichotomous x y)
 where
  I : (x ≤ y) ∔ (y ≤ x) → (pos x ≤ pos y) ∔ (pos y ≤ pos x)
  I (inl l) = inl (ℕ≤-to-ℤ≤ x y l)
  I (inr r) = inr (ℕ≤-to-ℤ≤ y x r)
ℤ-dichotomous (pos x) (negsucc y) = inr (negative-less-than-positive (succ y) x)
ℤ-dichotomous (negsucc x) (pos y) = inl (negative-less-than-positive (succ x) y)
ℤ-dichotomous (negsucc x) (negsucc y) = I (≤-dichotomous x y)
 where
  I : (x ≤ y) ∔ (y ≤ x) → (negsucc x ≤ negsucc y) ∔ (negsucc y ≤ negsucc x)
  I (inl l) = inr (ℤ≤-swap (pos (succ x)) (pos (succ y)) (ℕ≤-to-ℤ≤ (succ x) (succ y) l))
  I (inr r) = inl (ℤ≤-swap (pos (succ y)) (pos (succ x)) (ℕ≤-to-ℤ≤ (succ y) (succ x) r))

ℤ-trichotomous : (x y : ℤ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
ℤ-trichotomous x y = I (ℤ-dichotomous x y) 
 where
  I : (x ≤ y) ∔ (y ≤ x) → (x < y) ∔ (x ≡ y) ∔ (y < x)
  I (inl l) = II (ℤ≤-split x y l)
   where
    II : (x < y) ∔ (x ≡ y) → (x < y) ∔ (x ≡ y) ∔ (y < x)
    II (inl l) = inl l
    II (inr r) = inr (inl r)
  I (inr r) = II (ℤ≤-split y x r)
   where
    II : (y < x) ∔ (y ≡ x) → (x < y) ∔ (x ≡ y) ∔ (y < x) 
    II (inl l) = inr (inr l)
    II (inr r) = inr (inl (r ⁻¹))
{-
ℤ-trichotomous : (x y : ℤ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
ℤ-trichotomous (pos x) (pos y) = I (nat-order-trichotomous x y)
 where
  I : (x < y) ∔ (x ≡ y) ∔ (y < x) → (pos x < pos y) ∔ (pos x ≡ pos y) ∔ (pos y < pos x)
  I (inl l) = inl (ℕ-order-respects-ℤ-order x y l)
  I (inr (inl e)) = inr (inl (ap pos e))
  I (inr (inr l)) = inr (inr (ℕ-order-respects-ℤ-order y x l))
ℤ-trichotomous (pos x) (negsucc y) = inr (inr (negative-less-than-positive y x))
ℤ-trichotomous (negsucc x) (pos y) = inl (negative-less-than-positive x y)
ℤ-trichotomous (negsucc x) (negsucc y) = I (nat-order-trichotomous x y)
 where
  I : (x < y) ∔ (x ≡ y) ∔ (y < x)
    → (negsucc x < negsucc y) ∔ (negsucc x ≡ negsucc y) ∔ (negsucc y < negsucc x)
  I (inl l) = inr (inr (ℕ-order-respects-ℤ-order' x y l))
  I (inr (inl e)) = inr (inl (ap negsucc e))
  I (inr (inr l)) = inl (ℕ-order-respects-ℤ-order' y x l)
-}
ℤ≤-adding : (a b c d : ℤ) → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
ℤ≤-adding a b c d (p , β) (q , β') = (p ℕ+ q) , I
 where
  I : a + c + pos (p ℕ+ q) ≡ b + d
  I = a + c + pos (p ℕ+ q) ≡⟨ ap ((a + c) +_) (pos-addition-equiv-to-ℕ p q ⁻¹) ⟩
      (a + c) + (pos p + pos q)      ≡⟨ ℤ+-assoc (a + c) (pos p) (pos q) ⁻¹              ⟩
      ((a + c) + pos p) + pos q      ≡⟨ ap (λ z → (z + pos p) + pos q) (ℤ+-comm a c) ⟩
      ((c + a) + pos p) + pos q      ≡⟨ ap (_+ pos q) (ℤ+-assoc c a (pos p))           ⟩
      (c + (a + pos p)) + pos q      ≡⟨ ap (λ z → (c + z) + pos q) β             ⟩
      (c + b) + pos q                ≡⟨ ap (_+ pos q) (ℤ+-comm c b)              ⟩
      (b + c) + pos q                ≡⟨ ℤ+-assoc b c (pos q)                       ⟩
      b + (c + pos q)                ≡⟨ ap (b +_) β'                         ⟩
      b + d                          ∎

ℤ<-adding : (a b c d : ℤ) → a < b → c < d → (a + c) < (b + d)
ℤ<-adding a b c d (p , β) (q , β') = ℤ<-trans (a + c) (a + succℤ c) (b + d) II III
 where
  I : (succℤ a + succℤ c) ≤ (b + d)
  I = ℤ≤-adding (succℤ a) b (succℤ c) d (p , β) (q , β')
  II : (a + c) < (a + succℤ c)
  II = 0 , (ℤ-right-succ a c ⁻¹)
  III : (a + succℤ c) < (b + d)
  III = transport (_≤ (b + d)) (ℤ-left-succ a (succℤ c)) I

ℤ≤-adding' :  (a b c : ℤ) → a ≤ b → a + c ≤ b + c
ℤ≤-adding' a b c (k , p) = k , I
 where
  I : a + c + pos k ≡ b + c
  I = a + c + pos k   ≡⟨ ℤ+-assoc a c (pos k) ⟩
      a + (c + pos k) ≡⟨ ap (a +_) (ℤ+-comm c (pos k)) ⟩
      a + (pos k + c) ≡⟨ ℤ+-assoc a (pos k) c ⁻¹ ⟩
      a + pos k + c   ≡⟨ ap (_+ c) p ⟩
      b + c ∎

ℤ<-adding' : (a b c : ℤ) → a < b → a + c < b + c
ℤ<-adding' a b c (k , p) = I (ℤ≤-adding' (succℤ a) b c (k , p))
 where
  I : (succℤ a + c) ≤ (b + c) → (a + c) < (b + c)
  I (h , q) = h , II
   where
    II : succℤ (a + c) + pos h ≡ b + c
    II = succℤ (a + c) + pos h ≡⟨ ap (_+ (pos h)) (ℤ-left-succ a c ⁻¹) ⟩
         succℤ a + c + pos h   ≡⟨ q ⟩
         b + c ∎

ℤ<-adding'' : (a b c : ℤ) → a < b → c + a < c + b
ℤ<-adding'' a b c l = transport₂ _<_ (ℤ+-comm a c) (ℤ+-comm b c) I
 where
  I : (a + c) < (b + c)
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

positive-multiplication-preserves-order : (a b c : ℤ) → greater-than-zero c → a < b → (a * c) < (b * c)
positive-multiplication-preserves-order a b (negsucc x)    p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos 0)        p l = 𝟘-elim p
positive-multiplication-preserves-order a b (pos (succ x)) p l = pmpo-lemma a b x l

nmco-lemma : (a b : ℤ) → (c : ℕ) → a < b → (b * (negsucc c)) < (a * (negsucc c))
nmco-lemma a b = induction base step
 where
  base : a < b → (b * negsucc 0) < (a * negsucc 0)
  base (α , γ) = α , I
   where
    III : (- b) + pos α + (a + (- a)) ≡ a + pos α + ((- b) + (- a))
    III = (- b) + pos α + (a + (- a))   ≡⟨ ap (_+ (a + (- a))) (ℤ+-comm (- b) (pos α)) ⟩
          pos α + (- b) + (a + (- a))   ≡⟨ ℤ+-assoc (pos α + (- b)) a (- a) ⁻¹ ⟩ 
          pos α + (- b) + a + (- a)     ≡⟨ ap (_+ (- a)) (ℤ+-comm (pos α + (- b)) a) ⟩
          a + (pos α + (- b)) + (- a)   ≡⟨ ap (_+ (- a)) (ℤ+-assoc a (pos α) (- b) ⁻¹) ⟩
          a + pos α + (- b) + (- a)     ≡⟨ ℤ+-assoc (a + pos α) (- b) (- a) ⟩
          a + pos α + ((- b) + (- a))   ∎
    II : succℤ a + pos α + ((- b) + (- a)) ≡ b + ((- b) + (- a))
    II = ap (_+ ((- b) + (- a))) γ
    I : succℤ (b * negsucc 0) + pos α ≡ a * negsucc 0
    I = succℤ (b * negsucc 0) + pos α         ≡⟨ by-definition ⟩
        succℤ (- b) + pos α                   ≡⟨ ℤ-left-succ (- b) (pos α) ⟩
        succℤ ((- b) + pos α)                 ≡⟨ ℤ-zero-right-neutral (succℤ ((- b) +pos α)) ⟩
        succℤ ((- b) + pos α) + pos 0         ≡⟨ ap (succℤ ((- b) + pos α) +_) (ℤ-sum-of-inverse-is-zero a ⁻¹) ⟩
        succℤ ((- b) + pos α) + ((a + (- a))) ≡⟨ ℤ-left-succ ((- b) + pos α) (a + (- a)) ⟩
        succℤ (((- b) + pos α) + (a + (- a))) ≡⟨ ap succℤ III ⟩
        succℤ (a + pos α + ((- b) + (- a)))   ≡⟨ ℤ-left-succ (a + pos α) ((- b) + (- a)) ⁻¹ ⟩
        succℤ (a + pos α) + ((- b) + (- a))   ≡⟨ ap (_+ ((- b) + (- a))) (ℤ-left-succ a (pos α) ⁻¹) ⟩
        succℤ a + pos α + ((- b) + (- a))     ≡⟨ II ⟩
        b + ((- b) + (- a))                   ≡⟨ ℤ+-assoc b (- b) (- a) ⁻¹ ⟩
        b + (- b) + (- a)                     ≡⟨ ap (_+ (- a)) (ℤ-sum-of-inverse-is-zero b) ⟩
        pos 0 + (- a)                         ≡⟨ ℤ-zero-left-neutral (- a) ⟩
        - a                                   ≡⟨ by-definition ⟩
        a * negsucc 0 ∎

  step : (k : ℕ)
       → (a < b → (b * negsucc k) < (a * negsucc k))
       →  a < b → (b * negsucc (succ k)) < (a * negsucc (succ k))
  step k IH l = ℤ<-adding (- b) (- a) (b * negsucc k) (a * negsucc k) (base l) (IH l)

negative-multiplication-changes-order : (a b c : ℤ) → negative c → a < b → (b * c) < (a * c)
negative-multiplication-changes-order a b (pos c)     g l = 𝟘-elim g
negative-multiplication-changes-order a b (negsucc c) g l = nmco-lemma a b c l

ℤ-mult-right-cancellable : (x y z : ℤ) → not-zero z → (x * z) ≡ (y * z) → x ≡ y
ℤ-mult-right-cancellable x y (pos 0)        nz e = 𝟘-elim (nz ⋆)
ℤ-mult-right-cancellable x y (pos (succ z)) nz e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
  tri-split (inl l) = 𝟘-elim (ℤ-equal-not-less-than (x * pos (succ z)) (transport (x * pos (succ z) <_) (e ⁻¹) I))
   where
    I : (x * pos (succ z)) < (y * pos (succ z))
    I = positive-multiplication-preserves-order x y (pos (succ z)) ⋆ l
  tri-split (inr (inl m)) = m
  tri-split (inr (inr r)) = 𝟘-elim (ℤ-equal-not-less-than (y * pos (succ z)) (transport (y * pos (succ z) <_) e I))
   where
    I : (y * pos (succ z)) < (x * pos (succ z))
    I = positive-multiplication-preserves-order y x (pos (succ z)) ⋆ r
ℤ-mult-right-cancellable x y (negsucc z)    nz e = tri-split (ℤ-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
  tri-split (inl l) = 𝟘-elim (ℤ-equal-not-less-than (y * negsucc z) (transport (y * negsucc z <_) e I))
   where
    I : (y * negsucc z) < (x * negsucc z) 
    I = nmco-lemma x y z l
  tri-split (inr (inl r)) = r
  tri-split (inr (inr r)) = 𝟘-elim (ℤ-equal-not-less-than (x * negsucc z) (transport (x * negsucc z <_) (e ⁻¹) I))
   where
    I : (x * negsucc z) < (y * negsucc z)
    I = nmco-lemma y x z r

ℤ-mult-left-cancellable : (x y z : ℤ) → not-zero z → (z * x) ≡ (z * y) → x ≡ y
ℤ-mult-left-cancellable x y z nz e = ℤ-mult-right-cancellable x y z nz I
 where
  I : x * z ≡ y * z
  I = x * z   ≡⟨ ℤ*-comm x z ⟩
      z * x   ≡⟨ e ⟩
      z * y   ≡⟨ ℤ*-comm z y ⟩
      y * z   ∎

orcl : (a b : ℤ) → (n : ℕ) → (a * (pos (succ n))) ≤ (b * (pos (succ n))) → a ≤ b
orcl a b = induction base step
 where
  base : (a * pos 1) ≤ (b * pos 1) → a ≤ b
  base = λ z → z

  step : (k : ℕ)
       → ((a * pos (succ k)) ≤ (b * pos (succ k)) → a ≤ b)
       → (a * pos (succ (succ k))) ≤ (b * pos (succ (succ k)))
       → a ≤ b
  step k IH (α , γ) = I (ℤ-trichotomous a b)
   where
    I : (a < b) ∔ (a ≡ b) ∔ (b < a) → a ≤ b
    I (inl l) = <-is-≤ a b l
    I (inr (inl e)) = 0 , e
    I (inr (inr (β , δ))) = 𝟘-elim (ℤ-bigger-or-equal-not-less (a * pos (succ (succ k))) (b * pos (succ (succ k))) II III)
     where
      II : (a * pos (succ (succ k))) ≤ (b * pos (succ (succ k)))
      II = α , γ

      III : (b * pos (succ (succ k))) < (a * pos (succ (succ k)))
      III = positive-multiplication-preserves-order b a (pos (succ (succ k))) ⋆ (β , δ)

orcl' : (a b : ℤ) → (n : ℕ) → (a * (pos (succ n))) < (b * (pos (succ n))) → a < b
orcl' a b n l = II (ℤ≤-split a b I)
 where
  I : a ≤ b
  I = orcl a b n (<-is-≤ (a * pos (succ n)) (b * pos (succ n)) l)
  II : (a < b) ∔ (a ≡ b) → a < b
  II (inl l) = l
  II (inr e) = 𝟘-elim (ℤ-equal-not-less-than (a * pos (succ n)) III)
   where
    III : (a * pos (succ n)) < (a * pos (succ n))
    III = transport (λ - → (a * pos (succ n)) < (- * pos (succ n))) (e ⁻¹) l

ordering-right-cancellable : (a b c : ℤ) → greater-than-zero c → (a * c) < (b * c) → a < b
ordering-right-cancellable a b (negsucc x) p l    = 𝟘-elim p
ordering-right-cancellable a b (pos 0) p l        = 𝟘-elim p
ordering-right-cancellable a b (pos (succ x)) p l = orcl' a b x l

ℤ≤-ordering-right-cancellable : (a b c : ℤ) → greater-than-zero c → (a * c) ≤ (b * c) → a ≤ b
ℤ≤-ordering-right-cancellable a b (pos zero) p l = 𝟘-elim p
ℤ≤-ordering-right-cancellable a b (pos (succ x)) p l = orcl a b x l
ℤ≤-ordering-right-cancellable a b (negsucc x) p l = 𝟘-elim p
      
 
\end{code}
