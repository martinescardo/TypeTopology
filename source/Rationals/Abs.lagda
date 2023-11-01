Andrew Sneap, 10 March 2022

In this file I define the absolute value for rational numbers,
and prove properties of the absolute value.

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Type hiding (abs)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (abs to 𝔽-abs) renaming (-_ to 𝔽-_) hiding (_+_) hiding (_*_)
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Multiplication

module Rationals.Abs where

abs : ℚ → ℚ
abs (q , _) = toℚ (𝔽-abs q)

ℚ-abs-zero : 0ℚ ＝ abs 0ℚ
ℚ-abs-zero = by-definition

toℚ-abs : (q : 𝔽) → abs (toℚ q) ＝ toℚ (𝔽-abs q)
toℚ-abs (x , a) = equiv→equality (𝔽-abs (x' , a')) (𝔽-abs (x , a)) γ
 where
  x'  = numℚ (x , a)
  a'  = dnomℚ (x , a)
  h   = hcf𝔽 (x , a)
  pa  = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'
  ph  = (pos ∘ succ) h

  γ' : ph ℤ* (absℤ x' ℤ* pa) ＝ ph ℤ* (absℤ x ℤ* pa')
  γ' = ph ℤ* (absℤ x' ℤ* pa)    ＝⟨ ℤ*-assoc ph (absℤ x') pa ⁻¹               ⟩
       ph ℤ* absℤ x' ℤ* pa      ＝⟨ refl                                      ⟩
       absℤ ph ℤ* absℤ x' ℤ* pa ＝⟨ ap (_ℤ* pa) (abs-over-mult' ph x' ⁻¹)     ⟩
       absℤ (ph ℤ* x') ℤ* pa    ＝⟨ ap (λ - → absℤ - ℤ* pa) (numr (x , a) ⁻¹) ⟩
       absℤ x ℤ* pa             ＝⟨ ℤ*-comm (absℤ x) pa                       ⟩
       pa ℤ* absℤ x             ＝⟨ ap (_ℤ* absℤ x) (dnomrP' (x , a))         ⟩
       ph ℤ* pa' ℤ* absℤ x      ＝⟨ ℤ*-assoc ph pa' (absℤ x)                  ⟩
       ph ℤ* (pa' ℤ* absℤ x)    ＝⟨ ap (ph ℤ*_) (ℤ*-comm pa' (absℤ x))        ⟩
       ph ℤ* (absℤ x ℤ* pa')    ∎

  γ : 𝔽-abs (x' , a') ≈ 𝔽-abs (x , a)
  γ = ℤ-mult-left-cancellable (absℤ x' ℤ* pa) (absℤ x ℤ* pa') ph id γ'

abs-of-pos-is-pos : (p : ℚ) → 0ℚ ≤ p → abs p ＝ p
abs-of-pos-is-pos ((pos x , a) , α) l = toℚ-to𝔽 ((pos x , a) , α) ⁻¹
abs-of-pos-is-pos ((negsucc x , a) , α) l = 𝟘-elim (ℚ-num-neg-not-pos x a α l)

abs-of-pos-is-pos' : (p : ℚ) → 0ℚ < p → abs p ＝ p
abs-of-pos-is-pos' p l = abs-of-pos-is-pos p (ℚ<-coarser-than-≤ 0ℚ p l)

ℚ-abs-neg-equals-pos : (q : ℚ) → abs q ＝ abs (- q)
ℚ-abs-neg-equals-pos (q , p) = γ
 where
  I : 𝔽-abs q ≈ 𝔽-abs (𝔽- q) → toℚ (𝔽-abs q) ＝ toℚ (𝔽-abs (𝔽- q))
  I = equiv→equality (𝔽-abs q) (𝔽-abs (𝔽- q))

  II : 𝔽-abs q ≈ 𝔽-abs (𝔽- q)
  II = 𝔽-abs-neg-equals-pos q

  γ : abs (q , p) ＝ abs (- (q , p))
  γ = abs (q , p)        ＝⟨ by-definition     ⟩
      toℚ (𝔽-abs q)      ＝⟨ I II              ⟩
      toℚ (𝔽-abs (𝔽- q)) ＝⟨ toℚ-abs (𝔽- q) ⁻¹ ⟩
      abs (toℚ (𝔽- q))   ＝⟨ by-definition     ⟩
      abs (- (q , p))    ∎

ℚ-abs-inverse : (q : ℚ) → (abs q ＝ q) ∔ (abs q ＝ - q)
ℚ-abs-inverse ((pos x , a) , q)     = inl (toℚ-to𝔽 ((pos x , a) , q) ⁻¹)
ℚ-abs-inverse ((negsucc x , a) , q) = inr refl

ℚ-abs-is-positive : (q : ℚ) → 0ℚ ≤ abs q
ℚ-abs-is-positive ((pos zero , a) , _)     = 0 , refl
ℚ-abs-is-positive ((pos (succ x) , a) , q) = γ
 where
  I : 0ℚ < toℚ (pos (succ x) , a)
  I = ℚ-zero-less-than-positive x a

  γ : 0ℚ ≤ abs ((pos (succ x) , a) , q)
  γ = ℚ<-coarser-than-≤ 0ℚ (abs ((pos (succ x) , a) , q)) I
ℚ-abs-is-positive ((negsucc x , a) , q) = γ
 where
  I : 0ℚ < abs ((negsucc x , a) , q)
  I = ℚ-zero-less-than-positive x a

  γ : 0ℚ ≤ abs ((negsucc x , a) , q)
  γ = ℚ<-coarser-than-≤ 0ℚ (abs (((negsucc x , a) , q))) I

ℚ-abs-zero-is-zero : (q : ℚ) → abs q ＝ 0ℚ → q ＝ 0ℚ
ℚ-abs-zero-is-zero ((pos 0 , a) , p) e = γ
 where
  γ : (pos 0 , a) , p ＝ 0ℚ
  γ = numerator-zero-is-zero ((pos 0 , a) , p) refl
ℚ-abs-zero-is-zero ((pos (succ x) , a) , p) e = 𝟘-elim γ
 where
  γ : 𝟘
  γ = ℚ-positive-not-zero x a e
ℚ-abs-zero-is-zero ((negsucc x , a) , p) e = 𝟘-elim (ℚ-positive-not-zero x a e)

ℚ-abs-≤ : (q : ℚ) → (- abs q ≤ q) × (q ≤ abs q)
ℚ-abs-≤ q = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : - abs q ≤ 0ℚ
  II = ℚ≤-swap 0ℚ (abs q) I

  III : - abs q ≤ abs q
  III = ℚ≤-trans (- abs q) 0ℚ (abs q) II I

  γ₁ : abs q ＝ q → (- abs q ≤ q) × (q ≤ abs q)
  γ₁ e = l , r
   where
    l : - abs q ≤ q
    l = transport (- abs q ≤_) e III

    r : q ≤ abs q
    r = transport (q ≤_) (e ⁻¹) (ℚ≤-refl q)

  γ₂ : abs q ＝ - q → (- abs q ≤ q) × (q ≤ abs q)
  γ₂ e = l , r
   where
    IV : q ＝ - abs q
    IV = q       ＝⟨ ℚ-minus-minus q ⟩
         - (- q) ＝⟨ ap -_ (e ⁻¹) ⟩
         - abs q ∎

    l : - abs q ≤ q
    l = transport (_≤ q) IV (ℚ≤-refl q)

    r : q ≤ abs q
    r = transport (_≤ abs q) (IV ⁻¹) III

ℚ≤-to-abs : (x y : ℚ) → (- y ≤ x) × (x ≤ y) → abs x ≤ y
ℚ≤-to-abs x y (l₁ , l₂) = γ (ℚ-abs-inverse x)
 where
  α : - x ≤ - (- y)
  α = ℚ≤-swap (- y) x l₁

  γ : (abs x ＝ x) ∔ (abs x ＝ - x) → abs x ≤ y
  γ (inl l) = transport (_≤ y) (l ⁻¹) l₂
  γ (inr r) = transport₂ _≤_ (r ⁻¹) (ℚ-minus-minus y ⁻¹) α

ℚ<-to-abs : (x y : ℚ) → (- y < x) × (x < y) → abs x < y
ℚ<-to-abs x y (l₁ , l₂) = γ
 where
  I : - y ≤ x
  I = ℚ<-coarser-than-≤ (- y) x l₁

  II : x ≤ y
  II = ℚ<-coarser-than-≤ x y l₂

  III : abs x ≤ y
  III = ℚ≤-to-abs x y (I , II)

  IV : abs x < y → abs x < y
  IV = id

  V : abs x ＝ y → abs x < y
  V e = 𝟘-elim (cases Vγ₁ Vγ₂ (ℚ-abs-inverse x))
   where
    Vγ₁ : ¬ (abs x ＝ x)
    Vγ₁ e' = ℚ<-irrefl x (transport (x <_) (e ⁻¹ ∙ e') l₂)

    Vγ₂ : ¬ (abs x ＝ - x)
    Vγ₂ e' = ℚ<-irrefl x (transport (_< x) VI l₁)
     where
      VI : - y ＝ x
      VI = - y     ＝⟨ ap -_ (e ⁻¹)       ⟩
           - abs x ＝⟨ ap -_ e'           ⟩
           - (- x) ＝⟨ ℚ-minus-minus x ⁻¹ ⟩
           x       ∎

  γ : abs x < y
  γ = cases IV V (ℚ≤-split (abs x) y III)

ℚ-abs-<-unpack :  (q ε : ℚ) → abs q < ε → (- ε < q) × (q < ε)
ℚ-abs-<-unpack q ε o = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : 0ℚ < ε
  II = ℚ≤-<-trans 0ℚ (abs q) ε I o

  III : - ε < 0ℚ
  III = ℚ<-swap 0ℚ ε II

  IV : - ε < abs q
  IV = ℚ<-≤-trans (- ε) 0ℚ (abs q) III I

  γ₁ : abs q ＝ q → (- ε < q) × (q < ε)
  γ₁ e = l , r
   where
    l : - ε < q
    l = transport (- ε <_) e IV

    r : q < ε
    r = transport (_< ε) e o

  γ₂ : abs q ＝ - q → (- ε < q) × (q < ε)
  γ₂ e = l , r
   where
    α : q ＝ - abs q
    α = q       ＝⟨ ℚ-minus-minus q ⟩
        - (- q) ＝⟨ ap -_ (e ⁻¹)    ⟩
        - abs q ∎

    l : - ε < q
    l = transport (- ε <_) (α ⁻¹) (ℚ<-swap (abs q) ε o)

    r : q < ε
    r = ℚ<-swap''' q ε (transport (- ε <_) e IV)

ℚ-abs-≤-unpack : (q ε : ℚ) → abs q ≤ ε → (- ε ≤ q) × (q ≤ ε)
ℚ-abs-≤-unpack q ε l' = cases γ₁ γ₂ (ℚ-abs-inverse q)
 where
  I : 0ℚ ≤ abs q
  I = ℚ-abs-is-positive q

  II : 0ℚ ≤ ε
  II = ℚ≤-trans 0ℚ (abs q) ε I l'

  III : - ε ≤ 0ℚ
  III = ℚ≤-swap 0ℚ ε II

  IV : - ε ≤ abs q
  IV = ℚ≤-trans (- ε) 0ℚ (abs q) III I

  γ₁ : abs q ＝ q → (- ε ≤ q) × (q ≤ ε)
  γ₁ e = l , r
   where
    l : - ε ≤ q
    l = transport (- ε ≤_) e IV

    r : q ≤ ε
    r = transport (_≤ ε) e l'

  γ₂ : abs q ＝ - q → (- ε ≤ q) × (q ≤ ε)
  γ₂ e = l , r
   where
    α : q ＝ - abs q
    α = q       ＝⟨ ℚ-minus-minus q ⟩
        - (- q) ＝⟨ ap -_ (e ⁻¹)    ⟩
        - abs q ∎

    l : - ε ≤ q
    l = transport (- ε ≤_) (α ⁻¹) (ℚ≤-swap (abs q) ε l')

    r : q ≤ ε
    r = ℚ≤-swap''' q ε (transport (- ε ≤_) e IV)

ℚ-triangle-inequality : (x y : ℚ) → abs (x + y) ≤ abs x + abs y
ℚ-triangle-inequality x y = ℚ≤-to-abs (x + y) (abs x + abs y) (γ I II)
 where
  I : - abs x ≤ x ≤ abs x
  I = ℚ-abs-≤ x

  II : - abs y ≤ y ≤ abs y
  II = ℚ-abs-≤ y

  γ : - abs x ≤ x ≤ abs x
    → - abs y ≤ y ≤ abs y
    → - (abs x + abs y) ≤ x + y ≤ abs x + abs y
  γ (l₁ , l₂) (l₃ , l₄) = (transport (_≤ x + y) IV III) , V
   where
    III : (- abs x) - abs y ≤ x + y
    III = ℚ≤-adding (- abs x) x (- abs y) y l₁ l₃

    IV : (- abs x) - abs y ＝ - (abs x + abs y)
    IV = ℚ-minus-dist (abs x) (abs y)

    V : x + y ≤ abs x + abs y
    V = ℚ≤-adding x (abs x) y (abs y) l₂ l₄

ℚ-triangle-inequality' : (x y z : ℚ) → abs (x - z) ≤ abs (x - y) + abs (y - z)
ℚ-triangle-inequality' x y z = γ
 where
  I : x - z ＝ x - y + (y - z)
  I = ℚ-add-zero x (- z) y

  II : abs (x - z) ＝ abs (x - y + (y - z))
  II = ap abs I

  III : abs (x - y + (y - z)) ≤ abs (x - y) + abs (y - z)
  III = ℚ-triangle-inequality (x - y) (y - z)

  γ : abs (x - z) ≤ abs (x - y) + abs (y - z)
  γ = transport (_≤ abs (x - y) + abs (y - z)) (II ⁻¹) III

pos-abs-no-increase : (q ε : ℚ) → (0ℚ < q) × (q < ε) → abs q < ε
pos-abs-no-increase q ε (l₁ , l₂) = γ
 where
  I : 0ℚ < ε
  I = ℚ<-trans 0ℚ q ε l₁ l₂

  II : - ε < - 0ℚ
  II = ℚ<-swap 0ℚ ε I

  III : - ε < q
  III = ℚ<-trans (- ε) 0ℚ q II l₁

  γ : abs q < ε
  γ = ℚ<-to-abs q ε (III , l₂)

abs-mult : (x y : ℚ) → abs x * abs y ＝ abs (x * y)
abs-mult x y = γ (ℚ-dichotomous' x 0ℚ) (ℚ-dichotomous' y 0ℚ)
 where
  γ₁ : 0ℚ ≤ x → 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  γ₁ l₁ l₂ = abs x * abs y  ＝⟨ ap (_* abs y) (abs-of-pos-is-pos x l₁) ⟩
                x * abs y   ＝⟨ ap (x *_) (abs-of-pos-is-pos y l₂)     ⟩
                x * y       ＝⟨ abs-of-pos-is-pos (x * y) I ⁻¹         ⟩
                abs (x * y) ∎
   where
    I : 0ℚ ≤ x * y
    I = ℚ≤-pos-multiplication-preserves-order x y l₁ l₂

  γ₂ : (0ℚ > x) → (0ℚ > y) → abs x * abs y ＝ abs (x * y)
  γ₂ l₁ l₂ = VI
   where
    I : 0ℚ < - x
    I = ℚ<-swap'' x l₁

    II : 0ℚ < - y
    II = ℚ<-swap'' y l₂

    III : (- x) * (- y) ＝ x * y
    III = (- x) * (- y) ＝⟨ ℚ-negation-dist-over-mult x (- y)     ⟩
          - x * (- y)   ＝⟨ ap -_ (ℚ*-comm x (- y))               ⟩
          - (- y) * x   ＝⟨ ap -_ (ℚ-negation-dist-over-mult y x) ⟩
          - (- y * x)   ＝⟨ ℚ-minus-minus (y * x) ⁻¹              ⟩
          y * x         ＝⟨ ℚ*-comm y x                           ⟩
          x * y         ∎

    IV : 0ℚ < (- x) * (- y)
    IV = ℚ<-pos-multiplication-preserves-order (- x) (- y) I II

    V : 0ℚ < x * y
    V = transport (0ℚ <_) III IV

    VI : abs x * abs y ＝ abs (x * y)
    VI = abs x * abs y     ＝⟨ ap (_* abs y) (ℚ-abs-neg-equals-pos x)      ⟩
         abs (- x) * abs y ＝⟨ ap (_* abs y) (abs-of-pos-is-pos' (- x) I)  ⟩
         (- x) * abs y     ＝⟨ ap ((- x) *_) (ℚ-abs-neg-equals-pos y)      ⟩
         (- x) * abs (- y) ＝⟨ ap ((- x) *_) (abs-of-pos-is-pos' (- y) II) ⟩
         (- x) * (- y)     ＝⟨ III                                         ⟩
         x * y             ＝⟨ abs-of-pos-is-pos' (x * y) V ⁻¹             ⟩
         abs (x * y)       ∎

  γ₃ : (a b : ℚ) → 0ℚ ≤ a → b < 0ℚ → abs a * abs b ＝ abs (a * b)
  γ₃ a b l₁ l₂ =
   abs a * abs b ＝⟨ ap (_* abs b) (abs-of-pos-is-pos a l₁)                ⟩
   a * abs b     ＝⟨ ap (a *_) (ℚ-abs-neg-equals-pos b)                    ⟩
   a * abs (- b) ＝⟨ ap (a *_) (abs-of-pos-is-pos' (- b) (ℚ<-swap'' b l₂)) ⟩
   a * (- b)     ＝⟨ ℚ*-comm a (- b)                                       ⟩
   (- b) * a     ＝⟨ ℚ-negation-dist-over-mult b a                         ⟩
   - b * a       ＝⟨ ap -_ (ℚ*-comm b a)                                   ⟩
   - a * b       ＝⟨ abs-of-pos-is-pos (- a * b) (ℚ≤-swap' (a * b) V) ⁻¹   ⟩
   abs (- a * b) ＝⟨ ℚ-abs-neg-equals-pos (a * b) ⁻¹                       ⟩
   abs (a * b)   ∎
   where
    I : 0ℚ ≤ - b
    I = ℚ≤-swap' b (ℚ<-coarser-than-≤ b 0ℚ l₂)

    II : 0ℚ ≤ a * (- b)
    II = ℚ≤-pos-multiplication-preserves-order a (- b) l₁ I

    III : - (a * (- b)) ≤ - 0ℚ
    III = ℚ≤-swap 0ℚ (a * (- b)) II

    IV : - (a * (- b)) ＝ a * b
    IV = - a * (- b) ＝⟨ ap -_ (ℚ*-comm a (- b))               ⟩
        - (- b) * a  ＝⟨ ap -_ (ℚ-negation-dist-over-mult b a) ⟩
        - (- b * a)  ＝⟨ ℚ-minus-minus (b * a) ⁻¹              ⟩
        b * a        ＝⟨ ℚ*-comm b a                           ⟩
        a * b        ∎

    V : a * b ≤ 0ℚ
    V = transport₂ _≤_ IV ℚ-minus-zero-is-zero III

  γ₄ : x < 0ℚ → 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  γ₄ l₁ l₂ = abs x * abs y ＝⟨ ℚ*-comm (abs x) (abs y) ⟩
             abs y * abs x ＝⟨ γ₃ y x l₂ l₁            ⟩
             abs (y * x)   ＝⟨ ap abs (ℚ*-comm y x)    ⟩
             abs (x * y)   ∎

  γ : x < 0ℚ ∔ 0ℚ ≤ x → y < 0ℚ ∔ 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  γ (inl l₁) (inl l₂) = γ₂ l₁ l₂
  γ (inl l₁) (inr l₂) = γ₄ l₁ l₂
  γ (inr l₁) (inl l₂) = γ₃ x y l₁ l₂
  γ (inr l₁) (inr l₂) = γ₁ l₁ l₂

ℚ≤-abs-neg : (p : ℚ) → - abs p ≤ abs p
ℚ≤-abs-neg p = γ (ℚ-abs-≤ p)
 where
  γ : - abs p ≤ p ≤ abs p → - abs p ≤ abs p
  γ (l₁ , l₂) = ℚ≤-trans (- abs p) p (abs p) l₁ l₂

ℚ≤-abs-all : (p : ℚ) → p ≤ abs p
ℚ≤-abs-all p = pr₂ (ℚ-abs-≤ p)

abs-comm : (p q : ℚ) → abs (p - q) ＝ abs (q - p)
abs-comm p q = γ
 where
  γ : abs (p - q) ＝ abs (q - p)
  γ = abs (p - q)         ＝⟨ ℚ-abs-neg-equals-pos (p - q)                ⟩
      abs (- (p - q))     ＝⟨ ap (λ z → abs (- z)) (ℚ+-comm p (- q))      ⟩
      abs (- ((- q) + p)) ＝⟨ ap abs (ℚ-minus-dist (- q) p ⁻¹)            ⟩
      abs ((- (- q)) - p) ＝⟨ ap (λ z → abs (z - p)) (ℚ-minus-minus q ⁻¹) ⟩
      abs (q - p)         ∎

ℚ<-to-abs' : (p q : ℚ) → p < q → abs (p - q) ＝ q - p
ℚ<-to-abs' p q l = γ
 where
  I : 0ℚ < q - p
  I = ℚ<-difference-positive p q l

  γ : abs (p - q) ＝ q - p
  γ = abs (p - q) ＝⟨ abs-comm p q                  ⟩
      abs (q - p) ＝⟨ abs-of-pos-is-pos' (q -  p) I ⟩
      q - p       ∎

ℚ≤-to-abs' : (p q : ℚ) → p ≤ q → abs (p - q) ＝ q - p
ℚ≤-to-abs' p q l = γ
 where
  I : 0ℚ ≤ q - p
  I = ℚ≤-difference-positive p q l

  γ : abs (p - q) ＝ q - p
  γ = abs (p - q) ＝⟨ abs-comm p q                 ⟩
      abs (q - p) ＝⟨ abs-of-pos-is-pos (q - p) I  ⟩
      q - p       ∎

ℚ-abs-≤-pos : (p q : ℚ) → p ≤ q → 0ℚ < p → 0ℚ < q → abs p ≤ abs q
ℚ-abs-≤-pos p q l 0<p 0<q = γ
 where
  I : p ＝ abs p
  I = abs-of-pos-is-pos p (ℚ<-coarser-than-≤ 0ℚ p 0<p) ⁻¹

  II : q ＝ abs q
  II = abs-of-pos-is-pos q (ℚ<-coarser-than-≤ 0ℚ q 0<q) ⁻¹

  γ : abs p ≤ abs q
  γ = transport₂ _≤_ I II l

\end{code}
