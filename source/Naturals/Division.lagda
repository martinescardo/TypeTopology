Andrew Sneap - October - November 2021
Updated May - July 2022

This file defines division of natural numbers as a Σ type. Many common
proofs of properties of division are also provided.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition
open import Naturals.Multiplication
open import Naturals.Properties
open import Naturals.Subtraction
open import Naturals.Order
open import Notation.Order
open import UF.DiscreteAndSeparated
open import UF.Subsingletons

module Naturals.Division where

\end{code}

First, we have the definition of division. Division can also be
defined inductively, but as with most definitions I have instead
chosen to express division as a Σ type.

\begin{code}

_∣_ : ℕ → ℕ → 𝓤₀ ̇
x ∣ y = Σ a ꞉ ℕ , (x * a ＝ y)

\end{code}

Notice that we cannot prove that (x y : ℕ) → is-prop (x ∣ y).
When x ＝ 0, and y ＝ 0, we can choose any factor a and the identity type holds.

On the other hand, for values x > 0, it is a proposition that x | y.
This is proved using the cancellative property of multiplication of
factors greater than 0.

\begin{code}

_∣_-is-prop : (x y : ℕ) → is-prop (succ x ∣ y)
_∣_-is-prop x y (a , p) (b , p') = to-subtype-＝ (λ _ → ℕ-is-set) II
 where
  I : succ x * a ＝ succ x * b
  I = p ∙ p' ⁻¹

  II : a ＝ b
  II = mult-left-cancellable a b x I

\end{code}

Clearly, 1 divides anything, which is easily proved since 1 is the
multiplicative identity of naturals.

0 does not divide any value greater than 0. If this was the case, then
we would have that 0 * a ＝ 0 ＝ succ x, which is a contradiction.

Also, any number divides itself, and divides zero.

\begin{code}

1-divides-all : (x : ℕ) → 1 ∣ x
1-divides-all x = x , mult-left-id x

zero-does-not-divide-positive : (x : ℕ) → ¬(0 ∣ succ x)
zero-does-not-divide-positive x (a , p) = positive-not-zero x γ
 where
  γ : succ x ＝ 0
  γ = succ x ＝⟨ p ⁻¹             ⟩
      0 * a  ＝⟨ zero-left-base a ⟩
      0      ∎

∣-refl : {x : ℕ} → x ∣ x
∣-refl = 1 , refl

everything-divides-zero : {x : ℕ} → x ∣ 0
everything-divides-zero = 0 , refl

\end{code}

For natural numbers, division has the property that if x | y and
y | x, then x ＝ y.  This property is used to prove that if the
numerator a of a rational is 0, then the rational is 0.  In order to
prove this, we first need two lemmas.

The first is that if x < y, and x < z, then x < y * z.
This follows as a corollary of <-+.

\begin{code}

∣-anti-lemma : (x y z : ℕ) → x < y → x < z → x < y * z
∣-anti-lemma x 0        z        l₁ l₂ = 𝟘-elim (zero-least' z l₁)
∣-anti-lemma x (succ y) 0        l₁ l₂ = 𝟘-elim (zero-least' y l₂)
∣-anti-lemma x (succ y) (succ z) l₁ l₂ = <-+ x (succ y) (succ y * z) l₁

\end{code}

The second is that if the product of two naturals is 1, then the left
argument is 1. Of course, both arguments are 1 by commutativity of
multiplication.

The proof is by case analysis. When x ＝ 1, we are done.
If x ＝ 0, then x * y ＝ 0 ＝ 1, which is a contradiction.
If x > 1, the consider y. In each case, we find a contradiction.

\begin{code}

left-factor-one : (x y : ℕ) → x * y ＝ 1 → x ＝ 1
left-factor-one 0 y e = 𝟘-elim (zero-not-positive 0 γ)
 where
  γ : 0 ＝ 1
  γ = zero-left-base y ⁻¹ ∙ e
left-factor-one 1 y e = refl
left-factor-one (succ (succ x)) 0 e = 𝟘-elim (zero-not-positive 0 e)
left-factor-one (succ (succ x)) 1 e = 𝟘-elim (zero-not-positive x γ)
 where
  γ : 0 ＝ succ x
  γ = succ-lc (e ⁻¹)
left-factor-one (succ (succ x)) (succ (succ y)) e = 𝟘-elim γ
 where
  l₁ : 0 < succ x
  l₁ = zero-least (succ x)

  l₂ : 0 < succ y
  l₂ = zero-least (succ y)

  l₃ : 1 < succ (succ x) * succ (succ y)
  l₃ = ∣-anti-lemma 1 (succ (succ x)) (succ (succ y)) l₁ l₂

  γ : 𝟘
  γ = less-than-not-equal _ _ l₃ (e ⁻¹)

division-refl-right-unit : (x y : ℕ) → succ x * y ∣ succ x → y ＝ 1
division-refl-right-unit x y (k , e) = left-factor-one y k II
 where
  I : succ x * (y * k) ＝ succ x * 1
  I = mult-associativity (succ x) y k ⁻¹ ∙ e

  II : y * k ＝ 1
  II = mult-left-cancellable (y * k) 1 x I

division-refl-right-factor : (x y : ℕ) → succ x * y ∣ succ x → y ∣ 1
division-refl-right-factor x y (k , e) = γ
 where
  I : y ＝ 1
  I = division-refl-right-unit x y (k , e)

  II : 1 ∣ 1
  II = 1-divides-all 1

  γ : y ∣ 1
  γ = transport (_∣ 1) (I ⁻¹) II

\end{code}

And we can finally prove that division is anti-symmetric property,
using the two lemmas, and case analysis on y. In the case y ＝ 0, we
have 0 * b ＝ x, and hence x ＝ y ＝ 0.

In the case y > 0, we can use the fact that multiplication is
cancellable, and the hypothesis x * a ＝ succ y, succ y * b ＝ x to
prove that b ＝ 1, and conclude that division is anti-symmetric.


\begin{code}

∣-anti : (x y : ℕ) → x ∣ y → y ∣ x → x ＝ y
∣-anti x 0        (a , e₁) (b , e₂) = e₂ ⁻¹ ∙ zero-left-base b
∣-anti x (succ y) (a , e₁) (b , e₂) = e₂ ⁻¹ ∙ ap (succ y *_) b-is-1
 where
  I : succ y * (b * a) ＝ succ y * 1
  I = succ y * (b * a) ＝⟨ mult-associativity (succ y) b a ⁻¹ ⟩
      succ y * b * a   ＝⟨ ap (_* a) e₂ ∙ e₁                  ⟩
      succ y ∎

  b*a-is-1 : b * a ＝ 1
  b*a-is-1 = mult-left-cancellable (b * a) 1 y I

  b-is-1 : b ＝ 1
  b-is-1 = left-factor-one b a b*a-is-1

\end{code}

Division distributes over addition, over multiples, and is
transitive. The proofs are simple and corollaries of the properties of
multiplication.

\begin{code}

∣-respects-addition : (x y z : ℕ) → x ∣ y → x ∣ z → x ∣ (y + z)
∣-respects-addition x y z (a , p) (b , q) = (a + b , I)
 where
  I : x * (a + b) ＝ y + z
  I = x * (a + b)   ＝⟨ distributivity-mult-over-addition x a b ⟩
      x * a + x * b ＝⟨ ap (_+ x * b) p                         ⟩
      y + x * b     ＝⟨ ap (y +_) q                             ⟩
      y + z         ∎

∣-divisor-divides-multiple : (a b k : ℕ) → a ∣ b → a ∣ k * b
∣-divisor-divides-multiple a b k (x , p) = (x * k) , I
 where
  I : a * (x * k) ＝ k * b
  I = a * (x * k) ＝⟨ mult-associativity a x k ⁻¹ ⟩
      a * x * k   ＝⟨ ap (_* k) p                 ⟩
      b * k       ＝⟨ mult-commutativity b k      ⟩
      k * b       ∎

∣-respects-multiples : (a b c k l : ℕ) → a ∣ b → a ∣ c → a ∣ (k * b + l * c)
∣-respects-multiples a b c k l p₁ p₂ = ∣-respects-addition a (k * b) (l * c) I II
 where
  I : a ∣ (k * b)
  I = ∣-divisor-divides-multiple a b k p₁
  II : a ∣ (l * c)
  II = ∣-divisor-divides-multiple a c l p₂

∣-trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
∣-trans a b c (x , p) (y , q) = (x * y) , I
 where
  I : a * (x * y) ＝ c
  I = a * (x * y)  ＝⟨ mult-associativity a x y ⁻¹ ⟩
      (a * x) * y  ＝⟨ ap ( _* y) p                ⟩
      b * y        ＝⟨ q                           ⟩
      c            ∎

\end{code}

Now we state the division theorem for natural numbers. This states
that for a natural number a and d, there exists a quotient q and
remainder r with a ＝ q * (d + 1) + r, with the remainder r less than
succ d.

\begin{code}

division-theorem : (a d : ℕ) → 𝓤₀ ̇
division-theorem a d = Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ＝ q * succ d + r) × (r < succ d)

\end{code}

There are many ways to compute division on natural numbers. The chosen
method here (mainly to satisfy the termination checker) is to use
natural induction.

To compute (succ d) | a, we do induction on a.

Base: If a ＝ 0, then the quotient and remainder are both 0.

Inductive step: Suppose that (succ d) | k, then there exists q , r
such that k = q * succ d + r, and r < succ d.

We want to show that (succ d) | (succ k).
Since r < succ d, we have that either r < d or r ＝ d.

If r < d, then the quotient remains the same and the remainder
increases by 1. Since r < d, (succ r) < (succ d), and we are done.

If r ＝ d, then the quotient increases by 1 and the remainder is 0.
Clearly, 0 < succ d.  Proving that succ k ＝ succ q + succ q * d
follows from the inductive hypothesis and r ＝ d.

\begin{code}

division : (a d : ℕ) → division-theorem a d
division a d = ℕ-induction base step a
 where
  base : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (0 ＝ q * succ d + r) × (r < succ d)
  base = 0 , (0 , (I , II))
   where
    I : 0 ＝ 0 * succ d + 0
    I = 0         ＝⟨ refl                               ⟩
        0 + 0     ＝⟨ ap (0 +_) (zero-left-base d ⁻¹) ⟩
        0 + 0 * d ∎

    II : 0 < succ d
    II = zero-least d

  step : (k : ℕ)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (k ＝ q * succ d + r) × (r < succ d)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ＝ q * succ d + r) × (r < succ d)
  step k (q , r , e , l) = γ (<-split r d l)
   where
    γ : (r < d) ∔ (r ＝ d)
      →  Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ＝ q * succ d + r) × (r < succ d)
    γ (inl l) = q , succ r , ap succ e , l
    γ (inr e') = succ q , 0 , I , unique-to-𝟙 (0 < succ d)
     where
      I : succ k ＝ succ q + succ q * d
      I = succ k                        ＝⟨ i   ⟩
          succ (q + q * d + r)          ＝⟨ ii  ⟩
          succ (q + q * d + d)          ＝⟨ iii ⟩
          succ (q + (q * d + d))        ＝⟨ iv  ⟩
          succ q + (q * d + d)          ＝⟨ v   ⟩
          succ q + (d * q + d)          ＝⟨ vi  ⟩
          succ q + (d + d * q)          ＝⟨ vii ⟩
          succ q + succ q * d           ∎
       where
        i   = ap succ e
        ii  = ap succ (ap (q + q * d +_) e')
        iii = ap succ (addition-associativity q (q * d) d)
        iv  = succ-left q (q * d + d) ⁻¹
        v   = ap (succ q +_) (ap (_+ d) (mult-commutativity q d))
        vi  = ap (succ q +_) (addition-commutativity (d * q) d)
        vii = ap (succ q +_) (mult-commutativity d (succ q))

\end{code}

The division theorem is clearly a proposition.

First, we fix the quotient, and prove that the remainder is unique.

That is, if we have that a ＝ q * succ d + r, and
                         a ＝ q * succ d + r', then r ＝ r'.
This is easy to prove using cancellation of addition.

\begin{code}

division-is-prop' : (a d q : ℕ)
                  → is-prop (Σ r ꞉ ℕ , (a ＝ q * succ d + r) × r < succ d)
division-is-prop' a d q (r₀ , e₀ , l₀) (r₁ , e₁ , l₁) = γ
  where
   γ₁ : (r : ℕ) → is-prop ((a ＝ q * succ d + r) × r < succ d)
   γ₁ r = ×-is-prop ℕ-is-set (<-is-prop-valued r (succ d))

   I : q * succ d + r₀ ＝ q * succ d + r₁
   I = q * succ d + r₀ ＝⟨ e₀ ⁻¹ ⟩
       a               ＝⟨ e₁    ⟩
       q * succ d + r₁ ∎

   γ₂ : r₀ ＝ r₁
   γ₂ = addition-left-cancellable r₀ r₁ (q * succ d) I

   γ : r₀ , e₀ , l₀ ＝ r₁ , e₁ , l₁
   γ = to-subtype-＝ γ₁ γ₂

\end{code}

To conclude that the division theorem is a proposition, we use
trichotomy on the two quotient values q₀ and q₁.

When q₀ ＝ q₁, we are done.

In either of two cases, we can generalise a contradiction proof, which
is done in division-is-prop-lemma.

The idea of the proof is as follows:

We have that:
r₀ ≤ d,
r₁ ≤ d,
q₀ < q₁

a ＝ q₀ * succ d + r₀,
a ＝ q₁ * succ d + r₁,

Hence we have that

q₀ + k ＝ q₁, with k > 0
q₀ * succ d + r₀ ＝ q₁ * succ d + r₁
                 ＝ (q₀ + k) * succ d + r₁
                 ＝ (q₀ * d) + k * succ d + r₁
Now, r₀ ＝ k * succ d + r₁
   ⇒ k * succ d + r₁ ≤ d    (since r₀ ≤ d)
   ⇒ k * succ d ≤ d
   ⇒ succ d ≤ d, and hence we have a contradiction.

\begin{code}

division-is-prop-lemma : (a d q₀ q₁ r₀ r₁ : ℕ)
                       → r₀ ≤ d
                       → a ＝ q₀ * succ d + r₀
                       → a ＝ q₁ * succ d + r₁
                       → ¬ (q₀ < q₁)
division-is-prop-lemma a d q₀ q₁ r₀ r₁ l₁ e₁ e₂ l₂ = not-less-than-itself d γ
 where
  t : Σ k ꞉ ℕ , k + succ q₀ ＝ q₁
  t = subtraction (succ q₀) q₁ l₂

  k = pr₁ t
  e₃ = pr₂ t

  I : q₀ * succ d + r₀ ＝ q₀ * succ d + (succ k * succ d + r₁)
  I = q₀ * succ d + r₀                     ＝⟨ e₁ ⁻¹ ⟩
      a                                    ＝⟨ e₂    ⟩
      q₁ + q₁ * d + r₁                     ＝⟨refl⟩
      q₁ * succ d + r₁                     ＝⟨ i     ⟩
      succ (k + q₀) * succ d + r₁          ＝⟨ ii    ⟩
      (q₀ + succ k) * succ d + r₁          ＝⟨ iii   ⟩
      q₀ * succ d + succ k * succ d + r₁   ＝⟨ iv    ⟩
      q₀ * succ d + (succ k * succ d + r₁) ∎
   where
    i   = ap (λ - → - * succ d + r₁) (e₃ ⁻¹)
    ii  = ap (λ - → succ - * succ d + r₁) (addition-commutativity k q₀)
    iii = ap (_+ r₁) (distributivity-mult-over-addition' q₀ (succ k) (succ d))
    iv  = addition-associativity (q₀ * succ d) (succ k * succ d) r₁

  II : r₀ ＝ succ k * succ d + r₁
  II = addition-left-cancellable r₀ (succ k * succ d + r₁) (q₀ * succ d)  I

  III : succ k * succ d + r₁ ≤ d
  III = transport (_≤ d) II l₁

  IV : succ k * succ d ≤ succ k * succ d + r₁
  IV = ≤-+ (succ k * succ d) r₁

  V : succ k * succ d ≤ d
  V = ≤-trans (succ k * succ d) (succ k * succ d + r₁) d IV III

  VI : succ d * succ k ≤ d
  VI = transport (_≤ d) (mult-commutativity (succ k) (succ d)) V

  γ : succ d ≤ d
  γ = product-order-cancellable (succ d) k d VI

division-is-prop : (a d : ℕ) → is-prop (division-theorem a d)
division-is-prop a d (q₀ , r₀ , e₀ , l₀) (q₁ , r₁ , e₁ , l₁) = γ I
 where
  I : (q₀ < q₁) ∔ (q₀ ＝ q₁) ∔ (q₁ < q₀)
  I = <-trichotomous q₀ q₁

  γ : (q₀ < q₁) ∔ (q₀ ＝ q₁) ∔ (q₁ < q₀)
    → q₀ , r₀ , e₀ , l₀ ＝ q₁ , r₁ , e₁ , l₁
  γ (inl l)       = 𝟘-elim (division-is-prop-lemma a d q₀ q₁ r₀ r₁ l₀ e₀ e₁ l)
  γ (inr (inl e)) = to-subtype-＝ (division-is-prop' a d) e
  γ (inr (inr l)) = 𝟘-elim (division-is-prop-lemma a d q₁ q₀ r₁ r₀ l₁ e₁ e₀ l)

\end{code}

A property of division which is sometimes useful is the following.
If a * b ＝ a * c + d. If we were considering integers, this would be
easy to prove by simply by rewriting the equation as a * (b - c) ＝
d. With natural numbers, instead use induction on b and c.

If c ＝ 0, we are done, since a * b ∣ d.
If b ＝ 0, then 0 ＝ a * c + d, and hence d ＝ 0, and a * 0 ＝ 0, and we are done.
If b , c > 0, then we use induction.
The inductive hypothesis is: a * b       ＝ a * c       + d → a ∣ d,
                 and we have a * (b + 1) ＝ a * (c + 1) + d.

Since addition is left cancellable, we can find that a * b ＝ a * c + d and we
are done.

\begin{code}

factor-of-sum-consequence : (a b c d : ℕ) → a * b ＝ a * c + d → a ∣ d
factor-of-sum-consequence a b 0 d e = b , γ
 where
  γ : a * b ＝ d
  γ = a * b     ＝⟨ e                   ⟩
      a * 0 + d ＝⟨ zero-left-neutral d ⟩
      d         ∎
factor-of-sum-consequence a 0 (succ c) d e = 0 , γ
 where
  γ : 0 ＝ d
  γ = sum-to-zero-gives-zero (a * succ c) d (e ⁻¹) ⁻¹
factor-of-sum-consequence a (succ b) (succ c) d e = γ
  where
   I : a * succ b ＝ a + (a * c + d)
   I = a * succ b      ＝⟨ e                                  ⟩
       a * succ c + d  ＝⟨ addition-associativity a (a * c) d ⟩
       a + (a * c + d) ∎

   II : a * b ＝ a * c + d
   II = addition-left-cancellable (a * b) (a * c + d) a I

   γ : a ∣ d
   γ = factor-of-sum-consequence a b c d II

\end{code}
