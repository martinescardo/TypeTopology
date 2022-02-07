Andrew Sneap - 26/11/21

In this file, I define addition of integers, and prove some common properties of multiplication.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsMultiplication renaming (_*_ to _ℕ*_)

open import IntegersB
open import IntegersAddition
open import IntegersNegation

module IntegersMultiplication where

_*_ : ℤ → ℤ → ℤ
x * pos 0            = pos 0
x * pos (succ y)     = x + (x * pos y)
x * negsucc 0        = - x
x * negsucc (succ y) = (- x) + (x * negsucc y)

infixl 32 _*_

pos-multiplication-equiv-to-ℕ : (x y : ℕ) → pos x * pos y ≡ pos (x ℕ* y)
pos-multiplication-equiv-to-ℕ x = induction base step
  where
    base : (pos x * pos 0) ≡ pos (x ℕ* 0)
    base = refl

    step : (k : ℕ) →
             (pos x * pos k) ≡ pos (x ℕ* k) →
             (pos x * pos (succ k)) ≡ pos (x ℕ* succ k)
    step k IH = (pos x * pos (succ k))   ≡⟨ ap (pos x +_) IH                    ⟩
                (pos x + pos (x ℕ* k))   ≡⟨ pos-addition-equiv-to-ℕ x (x ℕ* k) ⟩
                pos (x ℕ* succ k) ∎

ℤ-zero-right-is-zero : (x : ℤ) → x * pos 0 ≡ pos 0
ℤ-zero-right-is-zero x = refl

ℤ-zero-left-is-zero : (x : ℤ) → pos 0 * x ≡ pos 0
ℤ-zero-left-is-zero = ℤ-induction base step₁ step₂
 where
  base : pos 0 * pos 0 ≡ pos 0
  base = refl

  step₁ : (k : ℤ)
        → pos 0 * k       ≡ pos 0
        → pos 0 * succℤ k ≡ pos 0
  step₁ (pos x)            IH = I
   where
    I : pos 0 * succℤ (pos x) ≡ pos 0
    I = pos 0 * succℤ (pos x) ≡⟨ refl             ⟩
        pos 0 + pos 0 * pos x ≡⟨ ap (pos 0 +_) IH ⟩
        pos 0 + pos 0         ≡⟨ refl             ⟩
        pos 0                 ∎
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = I
   where
    I : pos 0 * negsucc x ≡ pos 0
    I = pos 0 * negsucc x            ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⁻¹ ⟩
        pos 0 + pos 0 * negsucc x    ≡⟨ refl                                       ⟩
        pos 0 * negsucc (succ x)     ≡⟨ IH                                         ⟩
        pos 0                        ∎

  step₂ : (k : ℤ)
        → pos 0 * succℤ k ≡ pos 0
        → pos 0 * k       ≡ pos 0
  step₂ (pos x)            IH = I
   where
    I : pos 0 * pos x ≡ pos 0
    I = pos 0 * pos x         ≡⟨ ℤ-zero-left-neutral (pos 0 * pos x) ⁻¹ ⟩
        pos 0 + pos 0 * pos x ≡⟨ IH                                     ⟩
        pos 0                 ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos 0 + pos 0 * negsucc x ≡ pos 0
    I = pos 0 + pos 0 * negsucc x ≡⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⟩
        pos 0 * negsucc x         ≡⟨ IH                                      ⟩
        pos 0                     ∎

ℤ-mult-right-id : (x : ℤ) → x * pos 1 ≡ x
ℤ-mult-right-id x = refl

ℤ-mult-left-id : (x : ℤ) → pos 1 * x ≡ x
ℤ-mult-left-id = ℤ-induction base step₁ step₂
 where
  base : pos 1 * pos 0 ≡ pos 0
  base = refl

  step₁ : (k : ℤ)
        → pos 1 * k       ≡ k
        → pos 1 * succℤ k ≡ succℤ k
  step₁ (pos x) IH = I
   where
    I : pos 1 * succℤ (pos x) ≡ succℤ (pos x)
    I = pos 1 * succℤ (pos x) ≡⟨ ap (pos 1 +_) IH        ⟩
        pos 1 + pos x         ≡⟨ ℤ+-comm (pos 1) (pos x) ⟩
        succℤ (pos x)         ∎
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = I
   where
    I : pos 1 * negsucc x ≡ negsucc x
    I = ℤ+-lc (pos 1 * negsucc x) (negsucc x) (negsucc 0) II
     where
      II : negsucc 0 + pos 1 * negsucc x ≡ negsucc 0 + negsucc x
      II = negsucc 0 + pos 1 * negsucc x ≡⟨ IH                                 ⟩
           negsucc (succ x)              ≡⟨ ℤ+-comm (negsucc x) (negsucc 0)    ⟩
           negsucc 0 + negsucc x         ∎

  step₂ : (k : ℤ)
        → pos 1 * succℤ k ≡ succℤ k
        → pos 1 * k       ≡ k
  step₂ (pos x)            IH = ℤ+-lc (pos 1 * pos x) (pos x) (pos 1) I
   where
    I : pos 1 + pos 1 * pos x ≡ pos 1 + pos x
    I = pos 1 + pos 1 * pos x ≡⟨ IH                      ⟩
        succℤ (pos x)         ≡⟨ ℤ+-comm (pos x) (pos 1) ⟩
        pos 1 + pos x         ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos 1 * negsucc (succ x) ≡ negsucc (succ x)
    I = pos 1 * negsucc (succ x) ≡⟨ ap (negsucc 0 +_) IH            ⟩
        negsucc 0 + negsucc x    ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
        negsucc (succ x)         ∎

distributivity-mult-over-ℤ₀ : (x y : ℤ) → (z : ℕ) → (x + y) * (pos z) ≡ (x * pos z) + (y * pos z)
distributivity-mult-over-ℤ₀ x y = induction base step
 where
  base : (x + y) * pos 0 ≡ (x * pos 0) + (y * pos 0)
  base = refl

  step : (k : ℕ)
       → (x + y) * pos k        ≡ x * pos k + y * pos k
       → (x + y) * pos (succ k) ≡ x * pos (succ k) + y * pos (succ k)
  step k IH = (x + y) * pos (succ k)             ≡⟨ ap ((x + y) +_) IH                   ⟩
              (x + y) + (u + v)                  ≡⟨ ℤ+-assoc (x + y) u v ⁻¹              ⟩
              ((x + y) + u) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x y u)           ⟩
              (x + (y + u)) + v                  ≡⟨ ap (λ z → (x + z) + v) (ℤ+-comm y u) ⟩
              (x + (u + y)) + v                  ≡⟨ ap (_+ v) (ℤ+-assoc x u y ⁻¹)        ⟩
              ((x + u) + y) + v                  ≡⟨ ℤ+-assoc (x + u) y v                 ⟩
              (x + u) + (y + v)                  ∎
     where
       u v : ℤ
       u = x * pos k
       v = y * pos k

distributivity-mult-over-ℤ₁ : (x y : ℤ) → (z : ℕ) → (x + y) * (negsucc z) ≡ (x * negsucc z) + (y * negsucc z)
distributivity-mult-over-ℤ₁ x y = induction base step
 where
  base : (x + y) * negsucc 0 ≡ x * negsucc 0 + y * negsucc 0
  base = (x + y) * negsucc 0           ≡⟨ refl                    ⟩
         - (x + y)                     ≡⟨ negation-dist x y ⁻¹    ⟩
         (- x) + (- y)                 ≡⟨ refl                    ⟩
         x * negsucc 0 + y * negsucc 0 ∎

  step : (k : ℕ)
       → (x + y) * negsucc k               ≡ x * negsucc k + y * negsucc k
       → (- (x + y)) + (x + y) * negsucc k ≡ (- x) + x * negsucc k + ((- y) + y * negsucc k)
  step k IH = (- (x + y)) + (x + y) * negsucc k                   ≡⟨ ap ((- (x + y)) +_) IH                                                   ⟩
              (- (x + y)) + (x * negsucc k + y * negsucc k)       ≡⟨ ap (_+ (((x * negsucc k) + (y * negsucc k)))) (negation-dist x y ⁻¹) ⟩
              (- x) + (- y) + (x * negsucc k + y * negsucc k)   ≡⟨ ℤ+-assoc (- x) (- y) (u + v)                                            ⟩
              (- x) + ((- y) + (x * negsucc k + y * negsucc k)) ≡⟨ ap ((- x) +_) (ℤ+-assoc (- y) u v ⁻¹)                                   ⟩
              (- x) + ((- y) + x * negsucc k + y * negsucc k)   ≡⟨ ap (λ z → (- x) + (z + v)) (ℤ+-comm (- y) u)                            ⟩
              (- x) + (x * negsucc k + (- y) + y * negsucc k)   ≡⟨ ap ((- x) +_) (ℤ+-assoc u (- y) v)                                      ⟩
              (- x) + (x * negsucc k + ((- y) + y * negsucc k)) ≡⟨ ℤ+-assoc (- x) u ((- y) + v) ⁻¹                                         ⟩
              (- x) + x * negsucc k + ((- y) + y * negsucc k) ∎
    where
      u v : ℤ
      u = x * negsucc k
      v = y * negsucc k
    
distributivity-mult-over-ℤ : (x y z : ℤ) → (x + y) * z ≡ (x * z) + (y * z)
distributivity-mult-over-ℤ x y (pos z)     = distributivity-mult-over-ℤ₀ x y z
distributivity-mult-over-ℤ x y (negsucc z) = distributivity-mult-over-ℤ₁ x y z

mult-inverse : (x : ℤ) → (- x) ≡ (negsucc 0 * x)
mult-inverse = ℤ-induction base step₁ step₂
 where
  base : (- pos 0) ≡ (negsucc 0 * pos 0)
  base = refl

  step₁ : (k : ℤ)
        → (- k)     ≡ negsucc 0 * k
        → - succℤ k ≡ negsucc 0 * succℤ k
  step₁ (pos 0)            IH = refl 
  step₁ (pos (succ x))     IH = predℤ (negsucc x)                ≡⟨ ap predℤ IH                                           ⟩
                                predℤ (negsucc 0 * pos (succ x)) ≡⟨ ℤ-pred-is-minus-one (negsucc 0 + (negsucc 0 * pos x)) ⟩
                                negsucc 0 * succℤ (pos (succ x)) ∎ 
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH = ℤ+-lc (- succℤ (negsucc (succ x))) (negsucc 0 * succℤ (negsucc (succ x))) (pos 1) I
   where
    I : pos 1 + (- succℤ (negsucc (succ x))) ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos 1 + (- succℤ (negsucc (succ x))) ≡⟨ ap succℤ (ℤ+-comm (pos 1) (pos x)) ⟩
        succℤ (pos x + pos 1)                ≡⟨ IH ⟩
        negsucc 0 * negsucc (succ x)         ∎

  step₂ : (k : ℤ)
        → - succℤ k ≡ negsucc 0 * succℤ k
        → - k       ≡ negsucc 0 * k
  step₂ (pos 0)        IH = refl
  step₂ (pos (succ x)) IH = ℤ+-lc (- pos (succ x)) (negsucc 0 * pos (succ x)) (negsucc 0) I
   where
    I : negsucc 0 + (- pos (succ x)) ≡ negsucc 0 + negsucc 0 * pos (succ x)
    I = negsucc 0 + (- pos (succ x))     ≡⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
        negsucc x + negsucc 0            ≡⟨ IH ⟩
        negsucc 0 * succℤ (pos (succ x)) ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos (succ x) + pos 1 ≡ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos (succ x) + pos 1                         ≡⟨ ℤ+-comm (pos (succ x)) (pos 1) ⟩
        pos 1 + pos (succ x)                         ≡⟨  ap (pos (succ 0) +_) IH    ⟩
        pos 1 + negsucc 0 * succℤ (negsucc (succ x)) ∎
    
ℤ*-comm₀ : (x : ℤ) → (y : ℕ) → x * pos y ≡ pos y * x
ℤ*-comm₀ x = induction base step
 where
  base : (x * pos 0) ≡ (pos 0 * x)
  base = x * pos 0 ≡⟨ ℤ-zero-left-is-zero x ⁻¹ ⟩
         pos 0 * x ∎

  step : (k : ℕ)
       → x * pos k     ≡ pos k * x
       → x + x * pos k ≡ (pos k + pos 1) * x
  step k IH = x + x * pos k         ≡⟨ ap (x +_) IH                                    ⟩
              x + pos k * x         ≡⟨ ap (_+ (pos k * x)) (ℤ-mult-left-id x ⁻¹)       ⟩
              pos 1 * x + pos k * x ≡⟨ distributivity-mult-over-ℤ (pos 1) (pos k) x ⁻¹ ⟩
              (pos 1 + pos k) * x   ≡⟨ ap (_* x) (ℤ+-comm (pos 1) (pos k))             ⟩
              (pos k + pos 1) * x   ∎

ℤ*-comm₁ : (x : ℤ) → (y : ℕ) → x * (negsucc y) ≡ (negsucc y) * x
ℤ*-comm₁ x = induction base step
 where
  base : (x * negsucc 0) ≡ (negsucc 0 * x)
  base = mult-inverse x

  step : (k : ℕ)
       → x * negsucc k        ≡ negsucc k * x
       → x * negsucc (succ k) ≡ negsucc (succ k) * x
  step k IH = x * negsucc (succ k)              ≡⟨ refl                                                       ⟩
              (- x) + x * negsucc k             ≡⟨ ap ((- x) +_) IH                                           ⟩
              (- x) + negsucc k * x             ≡⟨ ap (_+ (negsucc k * x)) (mult-inverse x)                   ⟩
              (negsucc 0) * x + negsucc k * x   ≡⟨ distributivity-mult-over-ℤ (negsucc 0) (negsucc k) x ⁻¹ ⟩
              (negsucc 0 + negsucc k) * x       ≡⟨ ap (_* x) (ℤ+-comm (negsucc 0) (negsucc k))             ⟩ 
              negsucc (succ k) * x              ∎

ℤ*-comm : (x y : ℤ) → x * y ≡ y * x
ℤ*-comm x (pos y)     = ℤ*-comm₀ x y
ℤ*-comm x (negsucc y) = ℤ*-comm₁ x y

distributivity-mult-over-ℤ' : (x y z : ℤ) → z * (x + y) ≡ (z * x) + (z * y)
distributivity-mult-over-ℤ' x y z = z * (x + y)      ≡⟨ ℤ*-comm z (x + y)                                 ⟩
                                    (x + y) * z      ≡⟨ distributivity-mult-over-ℤ x y z                  ⟩
                                    x * z + y * z    ≡⟨ ap (_+ (y * z)) (ℤ*-comm x z)  ⟩
                                    z * x + y * z    ≡⟨ ap ((z * x) +_ ) (ℤ*-comm y z) ⟩
                                    z * x + z * y    ∎

subtraction-dist-over-mult₀ : (x : ℤ) → (y : ℕ) → x * (- pos y) ≡ - x * pos y
subtraction-dist-over-mult₀ x = induction base step
  where
    base : x * (- pos 0) ≡ - (x * pos 0)
    base = refl

    step : (k : ℕ)
         → x * (- pos k)        ≡ - (x * pos k)
         → x * (- pos (succ k)) ≡ - (x * pos (succ k))
    step 0        IH = refl
    step (succ k) IH = x * (- pos (succ (succ k)))  ≡⟨ ap ((- x) +_) IH                     ⟩
                       (- x) + (- x * pos (succ k)) ≡⟨ negation-dist x (x + (x * pos k)) ⟩
                       - (x + (x + x * pos k))        ∎

subtraction-dist-over-mult₁ : (x : ℤ) → (y : ℕ) → x * (- negsucc y) ≡ - x * negsucc y
subtraction-dist-over-mult₁ x = induction base step
 where
  base : x * (- negsucc 0) ≡ - x * negsucc 0
  base = minus-minus-is-plus x ⁻¹

  step : (k : ℕ)
       → x * (- negsucc k) ≡ - x * negsucc k
       → x + x * (- negsucc k) ≡ - ((- x) + x * negsucc k)
  step k IH = x + x * (- negsucc k)         ≡⟨ ap (x +_) IH                                            ⟩
              x + (- x * negsucc k)         ≡⟨ ap (_+ (- (x * negsucc k)) ) (minus-minus-is-plus x ⁻¹) ⟩
              (- (- x)) + (- x * negsucc k) ≡⟨ negation-dist (- x) (x * negsucc k)                  ⟩
              - ((- x) + x * negsucc k)       ∎

subtraction-dist-over-mult : (x y : ℤ) → x * (- y) ≡ - (x * y)
subtraction-dist-over-mult x (pos y)     = subtraction-dist-over-mult₀ x y 
subtraction-dist-over-mult x (negsucc y) = subtraction-dist-over-mult₁ x y

subtraction-dist-over-mult' : (x y : ℤ) → (- x) * y ≡ - (x * y)
subtraction-dist-over-mult' x y = II
 where
  I : y * (- x) ≡ - (y * x)
  I = subtraction-dist-over-mult y x

  II : (- x) * y ≡ - x * y
  II = (- x) * y ≡⟨ ℤ*-comm (- x) y     ⟩
       y * (- x) ≡⟨ I                   ⟩
       - (y * x) ≡⟨ ap -_ (ℤ*-comm y x) ⟩
       - (x * y)   ∎

minus-times-minus-is-positive : (x y : ℤ) → (- x) * (- y) ≡ x * y
minus-times-minus-is-positive x y = (- x) * (- y) ≡⟨ subtraction-dist-over-mult' x (- y) ⟩
                                    - (x * (- y)) ≡⟨ ap -_ (subtraction-dist-over-mult x y) ⟩
                                    - (- (x * y)) ≡⟨ minus-minus-is-plus (x * y) ⟩
                                    x * y ∎

ℤ*-assoc₀ : (x y : ℤ) → (z : ℕ ) → x * (y * pos z) ≡ (x * y) * pos z
ℤ*-assoc₀ x y = induction base step
  where
    base : x * (y * pos 0) ≡ (x * y) * pos 0
    base = refl

    step : (k : ℕ)
         → x * (y * pos k)         ≡ (x * y) * pos k
         → x * (y * pos (succ k))  ≡ (x * y) * pos (succ k)
    step k IH = x * (y * pos (succ k))        ≡⟨ distributivity-mult-over-ℤ' y (y * pos k) x ⟩
                x * y + x * (y * pos k)       ≡⟨ ap ((x * y) +_) IH                          ⟩
                x * y + (x * y) * pos k       ∎

ℤ*-assoc₁ : (x y : ℤ) → (z : ℕ) → x * (y * negsucc z) ≡ (x * y) * negsucc z
ℤ*-assoc₁ x y = induction base step
 where
  base : x * (y * negsucc 0) ≡ (x * y) * negsucc 0
  base = subtraction-dist-over-mult x y

  step : (k : ℕ)
       → x * (y * negsucc k) ≡ (x * y) * negsucc k
       → x * (y * negsucc (succ k)) ≡ (x * y) * negsucc (succ k)
  step k IH = x * (y * negsucc (succ k))        ≡⟨ distributivity-mult-over-ℤ' (- y) (y * negsucc k) x            ⟩
              x * (- y) + x * (y * negsucc k)   ≡⟨ ap ((x * (- y)) +_) IH                                         ⟩
              x * (- y) + x * y * negsucc k     ≡⟨ ap (_+ ((x * y) * negsucc k)) (subtraction-dist-over-mult x y) ⟩ 
              (- x * y) + x * y * negsucc k     ∎

ℤ*-assoc : (x y z : ℤ) → x * y * z ≡ x * (y * z)
ℤ*-assoc x y (pos z)     = ℤ*-assoc₀ x y z ⁻¹
ℤ*-assoc x y (negsucc z) = ℤ*-assoc₁ x y z ⁻¹

ℤ-mult-rearrangement : (x y z : ℤ) → (x * y) * z ≡ (x * z) * y
ℤ-mult-rearrangement x y z = x * y * z   ≡⟨ ℤ*-assoc x y z          ⟩
                             x * (y * z) ≡⟨ ap (x *_) (ℤ*-comm y z) ⟩
                             x * (z * y) ≡⟨ ℤ*-assoc x z y ⁻¹       ⟩
                             x * z * y   ∎

ℤ-mult-rearrangement' : (x y z : ℤ) → z * (x * y) ≡ y * (x * z)
ℤ-mult-rearrangement' x y z = z * (x * y) ≡⟨ ℤ*-comm z (x * y)          ⟩
                              x * y * z   ≡⟨ ℤ-mult-rearrangement x y z ⟩
                              x * z * y   ≡⟨ ℤ*-comm (x * z) y          ⟩
                              y * (x * z) ∎

ℤ-mult-rearrangement'' : (w x y z : ℤ) → (x * y) * (w * z) ≡ (w * y) * (x * z)
ℤ-mult-rearrangement'' w x y z = (x * y) * (w * z)     ≡⟨ ℤ-mult-rearrangement x y (w * z)     ⟩
                                (x * (w * z)) * y      ≡⟨ ap (_* y) (ℤ*-assoc x w z ⁻¹)        ⟩
                                ((x * w) * z) * y      ≡⟨ ap (λ a → (a * z) * y) (ℤ*-comm x w) ⟩
                                ((w * x) * z) * y      ≡⟨ ℤ*-assoc (w * x) z y                 ⟩
                                (w * x) * (z * y)      ≡⟨ ap ((w * x) *_) (ℤ*-comm z y)        ⟩
                                (w * x) * (y * z)      ≡⟨ ℤ*-assoc (w * x) y z ⁻¹              ⟩
                                ((w * x) * y) * z      ≡⟨ ap (_* z) (ℤ*-assoc w x y )          ⟩
                                (w * (x * y)) * z      ≡⟨ ap (λ a → (w * a) * z) (ℤ*-comm x y) ⟩
                                (w * (y * x)) * z      ≡⟨ ap (_* z) (ℤ*-assoc w y x ⁻¹)        ⟩
                                ((w * y) * x) * z      ≡⟨ ℤ*-assoc (w * y) x z                 ⟩
                                (w * y) * (x * z) ∎

ℤ-mult-rearrangement''' : (x y z : ℤ) → x * (y * z) ≡ y * (x * z)
ℤ-mult-rearrangement''' x y z = x * (y * z) ≡⟨ ℤ*-assoc x y z ⁻¹       ⟩
                                x * y * z   ≡⟨ ap (_* z) (ℤ*-comm x y) ⟩
                                y * x * z   ≡⟨ ℤ*-assoc y x z          ⟩
                                y * (x * z) ∎





