Andrew Sneap, 26 November 2021

In this file, I define addition of integers, and prove some common
properties of multiplication.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Integers.Type
open import Integers.Addition
open import Integers.Negation

module Integers.Multiplication where

\end{code}

Instead of defining auxiliary functions with a natural number
argument, multiplication is defined by pattern matching.

\begin{code}

_*_ : ℤ → ℤ → ℤ
x * pos 0            = pos 0
x * pos (succ y)     = x + (x * pos y)
x * negsucc 0        = - x
x * negsucc (succ y) = (- x) + (x * negsucc y)

infixl 32 _*_

pos-multiplication-equiv-to-ℕ : (x y : ℕ) → pos x * pos y ＝ pos (x ℕ* y)
pos-multiplication-equiv-to-ℕ x = ℕ-induction base step
  where
    base : pos x * pos 0 ＝ pos (x ℕ* 0)
    base = refl

    step : (k : ℕ)
         → pos x * pos k ＝ pos (x ℕ* k)
         → pos x * pos (succ k) ＝ pos (x ℕ* succ k)
    step k IH = pos x * pos (succ k) ＝⟨ ap (pos x +_) IH                       ⟩
                pos x + pos (x ℕ* k) ＝⟨ distributivity-pos-addition x (x ℕ* k) ⟩
                pos (x ℕ* succ k)    ∎


\end{code}

The following proofs that 0 is the base and 1 is the identity for
multiplication exemplify the "induction on both positives and
negatives" strategy.

To choose a specific example, the left identity element of multiplication is 1.
The two bases cases are 0 and -1, and definitionally we have that 1 * 0 = 0, and
1 * (- 1) = (- 1).

Induction on positives:
 1 * pos (succ x) ＝ 1 + 1 * pos x (by definition)
                  ＝ 1 + pos x     (by applying (_+ 1) to the IH)
                  ＝ pos (succ x)  (by commutativity of addition).

Induction on negatives:
 1 * negsucc (succ x) ＝ (- 1) + 1 * negsucc x (by definition)
                      ＝ (- 1) + negsucc x     (by applying (_- 1) to the IH)
                      ＝ negsucc (succ x)      (by  commutativity of addition).
\begin{code}

ℤ-zero-right-is-zero : (x : ℤ) → x * pos 0 ＝ pos 0
ℤ-zero-right-is-zero x = refl

ℤ-zero-left-base : (x : ℤ) → pos 0 * x ＝ pos 0
ℤ-zero-left-base (pos 0) = refl
ℤ-zero-left-base (pos (succ x)) =
 pos 0 * pos (succ x) ＝⟨ ℤ-zero-left-neutral (pos 0 * pos x) ⟩
 pos 0 * pos x        ＝⟨ ℤ-zero-left-base (pos x)            ⟩
 pos 0                ∎
ℤ-zero-left-base (negsucc 0) = refl
ℤ-zero-left-base (negsucc (succ x)) =
 pos 0 * negsucc (succ x) ＝⟨ ℤ-zero-left-neutral (pos 0 * negsucc x) ⟩
 pos 0 * negsucc x        ＝⟨ ℤ-zero-left-base (negsucc x)            ⟩
 pos 0 ∎

ℤ-mult-right-id : (x : ℤ) → x * pos 1 ＝ x
ℤ-mult-right-id x = refl

ℤ-mult-left-id : (x : ℤ) → pos 1 * x ＝ x
ℤ-mult-left-id (pos 0) = refl
ℤ-mult-left-id (pos (succ x)) =
 pos 1 * pos (succ x)  ＝⟨ ℤ+-comm (pos 1) (pos 1 * pos x)   ⟩
 pos 1 * pos x + pos 1 ＝⟨ ap succℤ (ℤ-mult-left-id (pos x)) ⟩
 succℤ (pos x)         ∎
ℤ-mult-left-id (negsucc 0) = refl
ℤ-mult-left-id (negsucc (succ x)) =
 pos 1 * negsucc (succ x)      ＝⟨ ℤ+-comm (negsucc 0) (pos 1 * negsucc x) ⟩
 pos 1 * negsucc x + negsucc 0 ＝⟨ ap predℤ (ℤ-mult-left-id (negsucc x))   ⟩
 predℤ (negsucc x)             ∎

\end{code}

Now we have an example where the positive and negative inductions are separated
into subfunctions, for readability, since the individual proofs are
lengthy. Distributivity of addition relies on commutativity and associativity
(and distributivity of negation).

\begin{code}

distributivity-mult-ℤ₀ : (x y : ℤ) (z : ℕ)
                            → (x + y) * pos z ＝ x * pos z + y * pos z
distributivity-mult-ℤ₀ x y = ℕ-induction base step
 where
  base : (x + y) * pos 0 ＝ x * pos 0 + y * pos 0
  base = refl

  step : (k : ℕ)
       → (x + y) * pos k ＝ x * pos k + y * pos k
       → (x + y) * pos (succ k) ＝ x * pos (succ k) + y * pos (succ k)
  step k IH = (x + y) * pos (succ k)              ＝⟨ i    ⟩
              (x + y) + (u + w)                   ＝⟨ ii   ⟩
              (x + y) + u + w                     ＝⟨ iii  ⟩
              x + (y + u) + w                     ＝⟨ iv   ⟩
              x + (u + y) + w                     ＝⟨ v    ⟩
              x + u + y + w                       ＝⟨ vi   ⟩
              x + u + (y + w)                     ＝⟨refl⟩
              x * pos (succ k) + y * pos (succ k) ∎
     where
       u w : ℤ
       u = x * pos k
       w = y * pos k
       i   = ap ((x + y) +_) IH
       ii  = ℤ+-assoc (x + y) u w ⁻¹
       iii = ap (_+ w) (ℤ+-assoc x y u)
       iv  = ap (λ z → (x + z) + w) (ℤ+-comm y u)
       v   = ap (_+ w) (ℤ+-assoc x u y ⁻¹)
       vi  = ℤ+-assoc (x + u) y w

distributivity-mult-ℤ₁ : (x y : ℤ) → (z : ℕ)
                       → (x + y) * negsucc z ＝ x * negsucc z + y * negsucc z
distributivity-mult-ℤ₁ x y = ℕ-induction base step
 where
  base : (x + y) * negsucc 0 ＝ x * negsucc 0 + y * negsucc 0
  base = (x + y) * negsucc 0           ＝⟨ refl                  ⟩
         - (x + y)                     ＝⟨ negation-dist x y ⁻¹  ⟩
         (- x) + (- y)                 ＝⟨ refl                  ⟩
         x * negsucc 0 + y * negsucc 0 ∎

  step : (k : ℕ)
       → (x + y) * negsucc k               ＝ x * negsucc k + y * negsucc k
       → (- (x + y)) + (x + y) * negsucc k ＝ (- x) + x * negsucc k + ((- y) + y * negsucc k)
  step k IH = (- (x + y)) + (x + y) * negsucc k               ＝⟨ i    ⟩
              (- (x + y)) + (u + w)                           ＝⟨ ii   ⟩
              (- x) - y + (u + w)                             ＝⟨ iii  ⟩
              (- x) + ((- y) + (u + w))                       ＝⟨ iv   ⟩
              (- x) + ((- y) + u + w)                         ＝⟨ v    ⟩
              (- x) + (u - y + w)                             ＝⟨ vi   ⟩
              (- x) + (u + ((- y) + w))                       ＝⟨ vii  ⟩
              (- x) + u + ((- y) + w)                         ＝⟨refl⟩
              (- x) + x * negsucc k + ((- y) + y * negsucc k) ∎
    where
      u w : ℤ
      u   = x * negsucc k
      w   = y * negsucc k
      i   = ap ((- (x + y)) +_) IH
      ii  = ap (_+ ((u + w))) (negation-dist x y ⁻¹)
      iii = ℤ+-assoc (- x) (- y) (u + w)
      iv  = ap ((- x) +_) (ℤ+-assoc (- y) u w ⁻¹)
      v   = ap (λ z → (- x) + (z + w)) (ℤ+-comm (- y) u)
      vi  = ap ((- x) +_) (ℤ+-assoc u (- y) w)
      vii = ℤ+-assoc (- x) u ((- y) + w) ⁻¹

distributivity-mult-over-ℤ : (x y z : ℤ) → (x + y) * z ＝ (x * z) + (y * z)
distributivity-mult-over-ℤ x y (pos z)     = distributivity-mult-ℤ₀ x y z
distributivity-mult-over-ℤ x y (negsucc z) = distributivity-mult-ℤ₁ x y z

\end{code}

Following the same strategy as distributivity, we have proofs that
relate multiplication and negation, commutativity of integers, and how
negation distributes over multiplication.

\begin{code}

mult-negation : (x : ℤ) → - x ＝ negsucc 0 * x
mult-negation = ℤ-induction base step₁ step₂
 where
  base : - pos 0 ＝ negsucc 0 * pos 0
  base = refl

  step₁ : (k : ℤ)
        → - k       ＝ negsucc 0 * k
        → - succℤ k ＝ negsucc 0 * succℤ k
  step₁ (pos 0)            IH = refl
  step₁ (pos (succ x))     IH
   = predℤ (negsucc x)                ＝⟨ i  ⟩
     predℤ (negsucc 0 * pos (succ x)) ＝⟨ ii ⟩
     negsucc 0 * succℤ (pos (succ x)) ∎
   where
    i  = ap predℤ IH
    ii = ℤ-pred-is-minus-one (negsucc 0 * pos (succ x))
  step₁ (negsucc 0)        IH = refl
  step₁ (negsucc (succ x)) IH =
   ℤ+-lc (- succℤ (negsucc (succ x)))
          (negsucc 0 * succℤ (negsucc (succ x))) (pos 1) I
   where
    I : pos 1 + (- succℤ (negsucc (succ x))) ＝ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos 1 + (- succℤ (negsucc (succ x))) ＝⟨ i  ⟩
        succℤ (pos x + pos 1)                ＝⟨ IH ⟩
        negsucc 0 * negsucc (succ x)         ∎
     where
      i = ap succℤ (ℤ+-comm (pos 1) (pos x))

  step₂ : (k : ℤ)
        → - succℤ k ＝ negsucc 0 * succℤ k
        → - k       ＝ negsucc 0 * k
  step₂ (pos 0)        IH = refl
  step₂ (pos (succ x)) IH = ℤ+-lc (- pos (succ x))
                                   (negsucc 0 * pos (succ x))
                                    (negsucc 0) I
   where
    I : negsucc 0 - pos (succ x) ＝ negsucc 0 * pos (succ (succ x))
    I = negsucc 0 - pos (succ x)         ＝⟨ ℤ+-comm (negsucc 0) (negsucc x) ⟩
        negsucc x + negsucc 0            ＝⟨ IH                              ⟩
        negsucc 0 * succℤ (pos (succ x)) ∎
  step₂ (negsucc 0)        IH = refl
  step₂ (negsucc (succ x)) IH = I
   where
    I : pos (succ x) + pos 1 ＝ pos 1 + negsucc 0 * succℤ (negsucc (succ x))
    I = pos (succ x) + pos 1                         ＝⟨ i  ⟩
        pos 1 + pos (succ x)                         ＝⟨ ii ⟩
        pos 1 + negsucc 0 * succℤ (negsucc (succ x)) ∎
     where
      i  = ℤ+-comm (pos (succ x)) (pos 1)
      ii = ap (pos (succ 0) +_) IH

ℤ*-comm₀ : (x : ℤ) → (y : ℕ) → x * pos y ＝ pos y * x
ℤ*-comm₀ x = ℕ-induction base step
 where
  base : x * pos 0 ＝ pos 0 * x
  base = x * pos 0 ＝⟨ ℤ-zero-left-base x ⁻¹ ⟩
         pos 0 * x ∎

  step : (k : ℕ)
       → x * pos k ＝ pos k * x
       → x * pos (succ k) ＝ (pos k + pos 1) * x
  step k IH = x + x * pos k         ＝⟨ i   ⟩
              x + pos k * x         ＝⟨ ii  ⟩
              pos 1 * x + pos k * x ＝⟨ iii ⟩
              (pos 1 + pos k) * x   ＝⟨ iv  ⟩
              (pos k + pos 1) * x   ∎
   where
    i   = ap (x +_) IH
    ii  = ap (_+ (pos k * x)) (ℤ-mult-left-id x ⁻¹)
    iii = distributivity-mult-over-ℤ (pos 1) (pos k) x ⁻¹
    iv  = ap (_* x) (ℤ+-comm (pos 1) (pos k))

ℤ*-comm₁ : (x : ℤ) → (y : ℕ) → x * negsucc y ＝ negsucc y * x
ℤ*-comm₁ x = ℕ-induction base step
 where
  base : x * negsucc 0 ＝ negsucc 0 * x
  base = mult-negation x

  step : (k : ℕ)
       → x * negsucc k        ＝ negsucc k * x
       → x * negsucc (succ k) ＝ negsucc (succ k) * x
  step k IH = x * negsucc (succ k)             ＝⟨refl⟩
              (- x) + x * negsucc k            ＝⟨ i    ⟩
              (- x) + negsucc k * x            ＝⟨ ii   ⟩
              negsucc 0 * x + negsucc k * x    ＝⟨ iii  ⟩
              (negsucc 0 + negsucc k) * x      ＝⟨ iv   ⟩
              negsucc (succ k) * x             ∎
   where
    i   = ap ((- x) +_) IH
    ii  = ap (_+ (negsucc k * x)) (mult-negation x)
    iii = distributivity-mult-over-ℤ (negsucc 0) (negsucc k) x ⁻¹
    iv  = ap (_* x) (ℤ+-comm (negsucc 0) (negsucc k))

ℤ*-comm : (x y : ℤ) → x * y ＝ y * x
ℤ*-comm x (pos y)     = ℤ*-comm₀ x y
ℤ*-comm x (negsucc y) = ℤ*-comm₁ x y

distributivity-mult-over-ℤ' : (x y z : ℤ) → z * (x + y) ＝ z * x + z * y
distributivity-mult-over-ℤ' x y z = γ
 where
  γ : z * (x + y) ＝ z * x + z * y
  γ = z * (x + y)      ＝⟨ ℤ*-comm z (x + y)                 ⟩
      (x + y) * z      ＝⟨ distributivity-mult-over-ℤ x y z  ⟩
      x * z + y * z    ＝⟨ ap (_+ (y * z)) (ℤ*-comm x z)     ⟩
      z * x + y * z    ＝⟨ ap ((z * x) +_ ) (ℤ*-comm y z)    ⟩
      z * x + z * y    ∎


negation-dist-over-mult₀ : (x : ℤ) → (y : ℕ) → x * (- pos y) ＝ - x * pos y
negation-dist-over-mult₀ x = ℕ-induction base step
  where
    base : x * (- pos 0) ＝ - (x * pos 0)
    base = refl

    step : (k : ℕ)
         → x * (- pos k)        ＝ - (x * pos k)
         → x * (- pos (succ k)) ＝ - (x * pos (succ k))
    step 0        IH = refl
    step (succ k) IH = x * (- pos (succ (succ k)))  ＝⟨ i  ⟩
                       (- x) + (- x * pos (succ k)) ＝⟨ ii ⟩
                       - (x + (x + x * pos k))      ∎
     where
      i  = ap ((- x) +_) IH
      ii = negation-dist x (x + (x * pos k))

negation-dist-over-mult₁ : (x : ℤ) → (y : ℕ)
                         → x * (- negsucc y) ＝ - x * negsucc y
negation-dist-over-mult₁ x = ℕ-induction base step
 where
  base : x * (- negsucc 0) ＝ - x * negsucc 0
  base = minus-minus-is-plus x ⁻¹

  step : (k : ℕ)
       → x * (- negsucc k) ＝ - x * negsucc k
       → x + x * (- negsucc k) ＝ - ((- x) + x * negsucc k)
  step k IH = x + x * (- negsucc k)         ＝⟨ i   ⟩
              x + (- x * negsucc k)         ＝⟨ ii  ⟩
              (- (- x)) + (- x * negsucc k) ＝⟨ iii ⟩
              - ((- x) + x * negsucc k)     ∎
   where
    i   = ap (x +_) IH
    ii  = ap (_+ (- (x * negsucc k)) ) (minus-minus-is-plus x ⁻¹)
    iii = negation-dist (- x) (x * negsucc k)

negation-dist-over-mult : (x y : ℤ) → x * (- y) ＝ - (x * y)
negation-dist-over-mult x (pos y)     = negation-dist-over-mult₀ x y
negation-dist-over-mult x (negsucc y) = negation-dist-over-mult₁ x y

negation-dist-over-mult' : (x y : ℤ) → (- x) * y ＝ - (x * y)
negation-dist-over-mult' x y = II
 where
  I : y * (- x) ＝ - (y * x)
  I = negation-dist-over-mult y x

  II : (- x) * y ＝ - x * y
  II = (- x) * y ＝⟨ ℤ*-comm (- x) y     ⟩
       y * (- x) ＝⟨ I                   ⟩
       - (y * x) ＝⟨ ap -_ (ℤ*-comm y x) ⟩
       - (x * y) ∎

minus-times-minus-is-positive : (x y : ℤ) → (- x) * (- y) ＝ x * y
minus-times-minus-is-positive x y = γ
 where
  γ : (- x) * (- y) ＝ x * y
  γ = (- x) * (- y) ＝⟨ negation-dist-over-mult' x (- y)    ⟩
      - (x * (- y)) ＝⟨ ap -_ (negation-dist-over-mult x y) ⟩
      - (- (x * y)) ＝⟨ minus-minus-is-plus (x * y)         ⟩
      x * y         ∎

ℤ*-assoc₀ : (x y : ℤ) → (z : ℕ ) → x * (y * pos z) ＝ x * y * pos z
ℤ*-assoc₀ x y = ℕ-induction base step
  where
    base : x * (y * pos 0) ＝ x * y * pos 0
    base = refl

    step : (k : ℕ)
         → x * (y * pos k)         ＝ x * y * pos k
         → x * (y * pos (succ k))  ＝ x * y * pos (succ k)
    step k IH = x * (y * pos (succ k))        ＝⟨ i  ⟩
                x * y + x * (y * pos k)       ＝⟨ ii ⟩
                x * y + x * y * pos k         ∎
     where
      i  = distributivity-mult-over-ℤ' y (y * pos k) x
      ii = ap ((x * y) +_) IH

ℤ*-assoc₁ : (x y : ℤ) → (z : ℕ) → x * (y * negsucc z) ＝ x * y * negsucc z
ℤ*-assoc₁ x y = ℕ-induction base step
 where
  base : x * (y * negsucc 0) ＝ x * y * negsucc 0
  base = negation-dist-over-mult x y

  step : (k : ℕ)
       → x * (y * negsucc k) ＝ x * y * negsucc k
       → x * (y * negsucc (succ k)) ＝ x * y * negsucc (succ k)
  step k IH = x * (y * negsucc (succ k))        ＝⟨ i   ⟩
              x * (- y) + x * (y * negsucc k)   ＝⟨ ii  ⟩
              x * (- y) + x * y * negsucc k     ＝⟨ iii ⟩
              (- x * y) + x * y * negsucc k     ∎
   where
    i   = distributivity-mult-over-ℤ' (- y) (y * negsucc k) x
    ii  = ap ((x * (- y)) +_) IH
    iii = ap (_+ ((x * y) * negsucc k)) (negation-dist-over-mult x y)

ℤ*-assoc : (x y z : ℤ) → x * y * z ＝ x * (y * z)
ℤ*-assoc x y (pos z)     = ℤ*-assoc₀ x y z ⁻¹
ℤ*-assoc x y (negsucc z) = ℤ*-assoc₁ x y z ⁻¹

is-pos-succ-addition : (x y : ℤ)
                     → is-pos-succ x
                     → is-pos-succ y
                     → is-pos-succ (x + y)
is-pos-succ-addition x (negsucc y)           x>0 y>0 = 𝟘-elim y>0
is-pos-succ-addition x (pos 0)               x>0 y>0 = 𝟘-elim y>0
is-pos-succ-addition x (pos (succ 0))        x>0 y>0 = is-pos-succ-succℤ x x>0
is-pos-succ-addition x (pos (succ (succ y))) x>0 y>0 =
 is-pos-succ-succℤ
  (x + pos (succ y))
   (is-pos-succ-addition x (pos (succ y)) x>0 y>0)

is-pos-succ-mult : (x y : ℤ)
                 → is-pos-succ x
                 → is-pos-succ y
                 → is-pos-succ (x * y)
is-pos-succ-mult x (negsucc y)           x>0 y>0 = 𝟘-elim y>0
is-pos-succ-mult x (pos 0)               x>0 y>0 = 𝟘-elim y>0
is-pos-succ-mult x (pos (succ 0))        x>0 y>0 = x>0
is-pos-succ-mult x (pos (succ (succ y))) x>0 y>0 =
 is-pos-succ-addition x (x * pos (succ y)) x>0
  (is-pos-succ-mult x (pos (succ y)) x>0 y>0)

pos-times-negative : (n k : ℕ) → Σ m ꞉ ℕ , pos (succ n) * negsucc k ＝ negsucc m
pos-times-negative n 0        = n , refl
pos-times-negative n (succ k) = I IH
 where
  IH : Σ m ꞉ ℕ , pos (succ n) * negsucc k ＝ negsucc m
  IH = pos-times-negative n k
  I : Σ m ꞉ ℕ , pos (succ n) * negsucc k ＝ negsucc m
    → Σ m ꞉ ℕ , pos (succ n) * negsucc (succ k) ＝ negsucc m
  I (m , e) = succ n ℕ+ m , II
   where
    II : pos (succ n) * negsucc (succ k) ＝ negsucc (succ n ℕ+ m)
    II = pos (succ n) * negsucc (succ k)      ＝⟨refl⟩
         negsucc n + pos (succ n) * negsucc k ＝⟨ i    ⟩
         negsucc n + negsucc m                ＝⟨ ii   ⟩
         - (succℤ (pos (succ n) + pos m))     ＝⟨ iii  ⟩
         - succℤ (pos (succ n ℕ+ m))          ＝⟨refl⟩
         negsucc (succ n ℕ+ m)                ∎
     where
      i   = ap (negsucc n +_) e
      ii  = negation-dist (pos (succ n)) (pos (succ m))
      iii = ap (λ z → - (succℤ z)) (distributivity-pos-addition (succ n) m)

negatives-equal : (x y : ℤ) → (- x) ＝ (- y) → x ＝ y
negatives-equal x y e = I
 where
  I : x ＝ y
  I = x       ＝⟨ minus-minus-is-plus x ⁻¹ ⟩
      - (- x) ＝⟨ ap -_ e                  ⟩
      - (- y) ＝⟨ minus-minus-is-plus y    ⟩
      y       ∎

ppnnp-lemma : (a b : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc b ＝ negsucc c
ppnnp-lemma a = ℕ-induction base step
 where
  base : Σ c ꞉ ℕ , negsucc a + negsucc 0 ＝ negsucc c
  base = succ a , refl

  step : (k : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc k ＝ negsucc c
                 → Σ c ꞉ ℕ , negsucc a + negsucc (succ k) ＝ negsucc c
  step k (c , IH) = succ c , ap predℤ IH

product-positive-negative-not-positive : (a b c : ℕ)
                                       → ¬ (pos a * negsucc b ＝ pos (succ c))
product-positive-negative-not-positive 0 0 c e = 𝟘-elim (positive-not-zero c I)
 where
  I : succ c ＝ 0
  I = pos-lc e ⁻¹
product-positive-negative-not-positive 0 (succ b) c e = 𝟘-elim II
 where
  I : pos 0 ＝ pos (succ c)
  I = pos 0                     ＝⟨ ℤ-zero-left-base (negsucc (succ b)) ⁻¹ ⟩
      pos 0 * negsucc (succ b)  ＝⟨ e                                      ⟩
      pos (succ c)              ∎

  II : 𝟘
  II = positive-not-zero c (pos-lc I ⁻¹)
product-positive-negative-not-positive (succ a) (succ b) c e₁ = γ I
 where
  I : Σ z ꞉ ℕ , succ z ＝ succ a ℕ* succ b
  I = pos-mult-is-succ a b

  γ : ¬ (Σ z ꞉ ℕ , succ z ＝ succ a ℕ* succ b)
  γ (z , e₂) = γ' II
   where
    II : Σ d ꞉ ℕ  , negsucc a + negsucc z ＝ negsucc d
    II = ppnnp-lemma a z

    γ' : ¬ (Σ d ꞉ ℕ , negsucc a + negsucc z ＝ negsucc d)
    γ' (d , e₃) = negsucc-not-pos IV
     where
      III : negsucc z ＝ pos (succ a) * negsucc b
      III = negsucc z                     ＝⟨refl⟩
            - pos (succ z)                ＝⟨ i    ⟩
            - pos (succ a ℕ* succ b)      ＝⟨ ii   ⟩
            - pos (succ a) * pos (succ b) ＝⟨ iii  ⟩
            pos (succ a) * negsucc b      ∎
       where
        i   = ap (λ α → -_ (pos α)) e₂
        ii  = ap -_ (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⁻¹
        iii =  negation-dist-over-mult (pos (succ a)) (pos (succ b)) ⁻¹

      IV : negsucc d ＝ pos (succ c)
      IV = negsucc d                            ＝⟨ e₃ ⁻¹                 ⟩
           negsucc a + negsucc z                ＝⟨ ap (negsucc a +_) III ⟩
           negsucc a + pos (succ a) * negsucc b ＝⟨ refl                  ⟩
           pos (succ a) * negsucc (succ b)      ＝⟨ e₁                    ⟩
           pos (succ c)                         ∎

\end{code}

Finally, we have equivalences of various re-arrangements of
multiplication of integers, which can be useful to reduce the size of
larger proofs.

\begin{code}

ℤ-mult-rearrangement : (x y z : ℤ) → x * y * z ＝ x * z * y
ℤ-mult-rearrangement x y z = x * y * z   ＝⟨ ℤ*-assoc x y z          ⟩
                             x * (y * z) ＝⟨ ap (x *_) (ℤ*-comm y z) ⟩
                             x * (z * y) ＝⟨ ℤ*-assoc x z y ⁻¹       ⟩
                             x * z * y   ∎

ℤ-mult-rearrangement' : (x y z : ℤ) → z * (x * y) ＝ y * (x * z)
ℤ-mult-rearrangement' x y z = z * (x * y) ＝⟨ ℤ*-comm z (x * y)          ⟩
                              x * y * z   ＝⟨ ℤ-mult-rearrangement x y z ⟩
                              x * z * y   ＝⟨ ℤ*-comm (x * z) y          ⟩
                              y * (x * z) ∎

ℤ-mult-rearrangement'' : (w x y z : ℤ) → x * y * (w * z) ＝ w * y * (x * z)
ℤ-mult-rearrangement'' w x y z = γ
 where
  γ : x * y * (w * z) ＝ w * y * (x * z)
  γ = x * y * (w * z)     ＝⟨ ℤ-mult-rearrangement x y (w * z)     ⟩
      x * (w * z) * y     ＝⟨ ap (_* y) (ℤ*-assoc x w z ⁻¹)        ⟩
      x * w * z * y       ＝⟨ ap (λ a → (a * z) * y) (ℤ*-comm x w) ⟩
      w * x * z * y       ＝⟨ ℤ*-assoc (w * x) z y                 ⟩
      w * x * (z * y)     ＝⟨ ap ((w * x) *_) (ℤ*-comm z y)        ⟩
      w * x * (y * z)     ＝⟨ ℤ*-assoc (w * x) y z ⁻¹              ⟩
      w * x * y * z       ＝⟨ ap (_* z) (ℤ*-assoc w x y )          ⟩
      w * (x * y) * z     ＝⟨ ap (λ a → (w * a) * z) (ℤ*-comm x y) ⟩
      w * (y * x) * z     ＝⟨ ap (_* z) (ℤ*-assoc w y x ⁻¹)        ⟩
      w * y * x * z       ＝⟨ ℤ*-assoc (w * y) x z                 ⟩
      w * y * (x * z)     ∎

ℤ-mult-rearrangement''' : (x y z : ℤ) → x * (y * z) ＝ y * (x * z)
ℤ-mult-rearrangement''' x y z = x * (y * z) ＝⟨ ℤ*-assoc x y z ⁻¹       ⟩
                                x * y * z   ＝⟨ ap (_* z) (ℤ*-comm x y) ⟩
                                y * x * z   ＝⟨ ℤ*-assoc y x z          ⟩
                                y * (x * z) ∎

\end{code}
