Andrew Sneap - 12/05/2022

This file defines division of natural numbers as a Σ type. Many common
proofs of properties of division are also provided.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) 

open import NaturalsAddition
open import NaturalsMultiplication
open import NaturalNumbers-Properties
open import NaturalsOrder
open import OrderNotation
open import UF-Base
open import UF-Miscelanea
open import UF-Subsingletons

module NaturalsDivision where

\end{code}

First, we have the definition of division. Division can also be
defined inductively, but as with most definitions I have instead
chosen to express division as a Σ type.

\begin{code}

_∣_ : ℕ → ℕ → 𝓤₀ ̇
x ∣ y = Σ a ꞉ ℕ , (x * a ≡ y)

\end{code}

Notice that we cannot prove that (x y : ℕ) → is-prop (x ∣ y).
When x ≡ 0, and y ≡ 0, we can choose any factor a and the identity type holds.

On the other hand, for values x > 0, it is a proposition that x | y.
This is proved using the cancellative property of multiplication of
factors greater than 0.

\begin{code}

_∣_-is-prop : (x y : ℕ) → is-prop (succ x ∣ y)
_∣_-is-prop x y (a , p) (b , p') = to-subtype-≡ (λ _ → ℕ-is-set) II
 where
  I : succ x * a ≡ succ x * b
  I = p ∙ p' ⁻¹
  
  II : a ≡ b
  II = mult-left-cancellable a b x I

\end{code}

Clearly, 1 divides anything, which is easily proved since 1 is the
multiplicative identity of naturals.

0 does not divide any value greater than 0. If this was the case, then
we would have that 0 * a ≡ 0 ≡ succ x, which is a contradiction. 

\begin{code}

1-divides-all : (x : ℕ) → 1 ∣ x
1-divides-all x = x , mult-left-id x

zero-does-not-divide-positive : (x : ℕ) → ¬(0 ∣ succ x)
zero-does-not-divide-positive x (a , p) = positive-not-zero x (p ⁻¹ ∙ zero-left-base a)

\end{code}

For natural numbers, division has the property that if x | y and
y | x, then x ≡ y.  This property is used to prove that if the
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

The proof is by case analysis. When x ≡ 1, we are done.
If x ≡ 0, then x * y ≡ 0 ≡ 1, which is a contradiction.
If x > 0, the consider y. In each case, we find a contradiction.

\begin{code}

product-one-gives-one : (x y : ℕ) → x * y ≡ 1 → x ≡ 1
product-one-gives-one 0               y               e = 𝟘-elim (zero-not-positive 0 (zero-left-base y ⁻¹ ∙ e))
product-one-gives-one 1               y               e = refl
product-one-gives-one (succ (succ x)) 0               e = 𝟘-elim (zero-not-positive 0 e)
product-one-gives-one (succ (succ x)) 1               e = 𝟘-elim (zero-not-positive x (succ-lc (e ⁻¹)))
product-one-gives-one (succ (succ x)) (succ (succ y)) e = 𝟘-elim (less-than-not-equal _ _ l (e ⁻¹))
 where
  l : 1 < succ (succ x) * succ (succ y)
  l = ∣-anti-lemma 1 (succ (succ x)) (succ (succ y)) (zero-least (succ x)) (zero-least (succ y))

\end{code}

And we can finally prove the division anti property, using the two
lemmas, and case analysis on x.

\begin{code}

∣-anti : (x y : ℕ) → x ∣ y → y ∣ x → x ≡ y
∣-anti 0        y (a , p) (b , q) = δ
 where
  δ : zero ≡ y
  δ = zero     ≡⟨ zero-left-base a ⁻¹ ⟩
      zero * a ≡⟨ p                      ⟩
      y        ∎ 
∣-anti (succ x) y (a , p) (b , q) = δ
 where
  a*b-is-one : a * b ≡ 1
  a*b-is-one = mult-left-cancellable (a * b) 1 x I
   where
    I : succ x * (a * b) ≡ succ x * 1
    I = succ x * (a * b) ≡⟨ mult-associativity (succ x) a b ⁻¹ ⟩
        succ x * a * b   ≡⟨ ap (_* b) p                        ⟩
        y * b            ≡⟨ q                                  ⟩
        succ x           ≡⟨ refl ⟩
        succ x * 1       ∎

  b-is-1 : b ≡ 1
  b-is-1 = product-one-gives-one b a I
   where
    I : b * a ≡ 1
    I = b * a ≡⟨ mult-commutativity b a ⟩
        a * b ≡⟨ a*b-is-one             ⟩
        1     ∎                              

  δ : succ x ≡ y
  δ = succ x ≡⟨ q ⁻¹             ⟩
      y * b  ≡⟨ ap (y *_) b-is-1 ⟩
      y      ∎

\end{code}

Division distributes over addition, over multiples, and is
transitive. The proofs are simple and corollaries of the properties of
multiplication.

\begin{code}

∣-respects-addition : (x y z : ℕ) → x ∣ y → x ∣ z → x ∣ (y + z)
∣-respects-addition x y z (a , p) (b , q) = (a + b , I)
 where
  I : x * (a + b) ≡ y + z
  I = x * (a + b)   ≡⟨ distributivity-mult-over-addition x a b ⟩
      x * a + x * b ≡⟨ ap (_+ x * b) p                    ⟩
      y + x * b     ≡⟨ ap (y +_) q                        ⟩
      y + z         ∎

∣-divisor-divides-multiple : (a b k : ℕ) → a ∣ b → a ∣ k * b
∣-divisor-divides-multiple a b k (x , p) = (x * k) , I
 where
  I : a * (x * k) ≡ k * b
  I = a * (x * k) ≡⟨ mult-associativity a x k ⁻¹ ⟩
      a * x * k   ≡⟨ ap (_* k) p                 ⟩
      b * k       ≡⟨ mult-commutativity b k ⟩
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
  I : a * (x * y) ≡ c
  I = a * (x * y)  ≡⟨ mult-associativity a x y ⁻¹ ⟩
      (a * x) * y  ≡⟨ ap ( _* y) p                ⟩
      b * y        ≡⟨ q                           ⟩
      c            ∎

\end{code}

Now we state the division theorem for natural numbers. This states
that for a natural number a and d, there exists a quotient q and
remainder r with a ≡ q * (d + 1) + r, with the remainder r less than
succ d.

\begin{code}

division-theorem : (a d : ℕ) → 𝓤₀ ̇
division-theorem a d = Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * succ d + r) × (r < succ d)

\end{code}

There are many ways to compute division on natural numbers. The chosen
method here (mainly to satisfy the termination checker) is to use
natural induction.

To compute (succ d) | a, we do induction on a.

Base: If a ≡ 0, then the quotient and remainder are both 0.

Inductive step: Suppose that (succ d) | k, then there exists q , r
such that k = q * succ d + r, and r < succ d.

We want to show that (succ d) | (succ k).
Since r < succ d, we have that either r < d or r ≡ d.

If r < d, then the quotient remains the same and the remainder
increases by 1. Since r < d, (succ r) < (succ d), and we are done.

If r ≡ d, then the quotient increases by 1 and the remainder is 0.
Clearly, 0 < succ d.  Proving that succ k ≡ succ q + succ q * d
follows from the inductive hypothesis and r ≡ d.

\begin{code}

division : (a d : ℕ) → division-theorem a d
division a d = induction base step a
 where
  base : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (0 ≡ q * succ d + r) × (r < succ d)  
  base = 0 , (0 , (I , II))
   where
    I : 0 ≡ 0 * succ d + 0
    I = 0         ≡⟨ refl                               ⟩
        0 + 0     ≡⟨ ap (0 +_) (zero-left-base d ⁻¹) ⟩
        0 + 0 * d ∎

    II : 0 < succ d
    II = zero-least d

  step : (k : ℕ)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (k ≡ q * succ d + r) × (r < succ d)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
  step k (q , r , e , l) = helper (<-split r d l)
   where
    helper : (r < d) ∔ (r ≡ d) →  Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
    helper (inl x) = q , succ r , ap succ e , x
    helper (inr x) = succ q , 0 , I , unique-to-𝟙 (0 < succ d)
     where
      I : succ k ≡ succ q + succ q * d
      I = succ k                        ≡⟨ ap succ e                                           ⟩
          succ (q + q * d + r)          ≡⟨ ap succ (ap (q + q * d +_) x)                       ⟩
          succ (q + q * d + d)          ≡⟨ ap succ (addition-associativity q (q * d) d)        ⟩
          succ (q + (q * d + d))        ≡⟨ succ-left q (q * d + d) ⁻¹                          ⟩
          succ q + (q * d + d)          ≡⟨ ap (succ q +_) (ap (_+ d) (mult-commutativity q d)) ⟩
          succ q + (d * q + d)          ≡⟨ ap (succ q +_) (addition-commutativity (d * q) d)   ⟩ 
          succ q + (d + d * q)          ≡⟨ ap (succ q +_) (mult-commutativity d (succ q))      ⟩ 
          succ q + succ q * d           ∎

\end{code}

The proofs contained in the division theorem are clearly propositions
(equality and order of natural numbers).

Proving that the quotient and remainder are unique 

\begin{code}
{-
division-is-prop' : (a d q : ℕ) → is-prop (Σ r ꞉ ℕ , (a ≡ q * succ d + r) × r < succ d)
division-is-prop' a d q (r₀ , α , αₚ) (r₁ , β , βₚ)
 = to-subtype-≡
  (λ r → ×-is-prop ℕ-is-set (<-is-prop-valued r (succ d)))
   (addition-left-cancellable r₀ r₁ (q * succ d) (α ⁻¹ ∙ β))

division-is-prop : (a d : ℕ) → is-prop (division-theorem a d)
division-is-prop a d (q₀ , r₀ , α , αₚ) (q₁ , r₁ , β , βₚ) = to-subtype-≡ (λ q → division-is-prop' a d q) II
 where
  
  II : {!!}
  II = {!!}
-}
{-
division-is-prop : (a d : ℕ) → is-prop (division-theorem a d)
division-is-prop a d (q₀ , r₀ , α , αₚ) (q₁ , r₁ , β , βₚ) = to-subtype-≡ I II
 where
  I : (q : ℕ) → is-prop (Σ r ꞉ ℕ , (a ≡ q * d + r) × (r < d))
  I q (r₀ , δ) (r₁ , γ) = to-subtype-≡ (λ r → ×-is-prop ℕ-is-set (<-is-prop-valued r d)) remainders-equal
   where
    remainders-equal : r₀ ≡ r₁
    remainders-equal = addition-left-cancellable r₀ r₁ (q * d) i
     where
      i : q * d + r₀ ≡ q * d + r₁
      i = q * d + r₀ ≡⟨ pr₁ δ ⁻¹ ⟩
          a          ≡⟨ pr₁ γ ⟩
          q * d + r₁ ∎

  assumption : q₀ * d + r₀ ≡ q₁ * d + r₁
  assumption = α ⁻¹ ∙ β

  II-abstract : (q q' r r' : ℕ) → q * d + r ≡ q' * d + r' → q < q' → r < d → q ≡ q'
  II-abstract q q' r r' e l₁ l₂ = 𝟘-elim (not-less-than-itself (d * succ k) vii)
   where
    i : Σ k ꞉ ℕ , (succ k) + q ≡ q'
    i = subtraction'' q q' l₁

    k : ℕ
    k = pr₁ i

    μ : (succ k) + q ≡ q'
    μ = pr₂ i

    ii : q * d + r ≡ q * d + ((succ k) * d + r')
    ii = q * d + r                   ≡⟨ e ⟩
         q' * d + r'                 ≡⟨ ap (λ - → - * d + r') (μ ⁻¹) ⟩
         ((succ k) + q) * d + r'     ≡⟨ ap (_+ r') (distributivity-mult-over-nat' (succ k) q d) ⟩
         (succ k) * d + q * d + r'   ≡⟨ ap (_+ r') (addition-commutativity ((succ k) * d) (q * d)) ⟩
         q * d + (succ k) * d + r'   ≡⟨ addition-associativity (q * d) ((succ k) * d) r' ⟩
         q * d + ((succ k) * d + r') ∎

    iii : r' + d * (succ k) ≡ r
    iii = r' + d * succ k         ≡⟨ ap (r' +_) (mult-commutativity d (succ k)) ⟩
          r' + (succ k) * d       ≡⟨ addition-commutativity r' ((succ k) * d) ⟩
          (succ k) * d + r'       ≡⟨ addition-left-cancellable r ((succ k) * d + r') (q * d) ii ⁻¹ ⟩ 
          r                       ∎

    iv : d * (succ k) ≤ r
    iv = cosubtraction (d * succ k) r (r' , iii)

    v : r < d * succ k
    v = less-than-pos-mult r d k l₂
    
    vii : d * succ k < d * succ k
    vii = ≤-<-trans (d * succ k) r (d * succ k) iv v

  II : q₀ ≡ q₁
  II = f (<-trichotomous q₀ q₁)
   where
    f : (q₀ < q₁) ∔ (q₀ ≡ q₁) ∔ (q₁ < q₀) → q₀ ≡ q₁
    f (inl z)       = II-abstract q₀ q₁ r₀ r₁ assumption z αₚ
    f (inr (inl z)) = z
    f (inr (inr z)) = II-abstract q₁ q₀ r₁ r₀ (assumption ⁻¹) z βₚ ⁻¹
-}
\end{code}

The following section defines division by using bounded
maximisation. Also provided is a proof that these two versions of
division provide the same output, using the proof division is a prop.

\begin{code}
{-
division' : (a d : ℕ) → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * (succ d) + r) × (r < (succ d))
division' 0 d     = 0 , (0 , (I , II))
 where
  I : 0 ≡ 0 * succ d + 0
  I = 0         ≡⟨ refl                               ⟩
      0 + 0     ≡⟨ ap (0 +_) (zero-left-is-zero d ⁻¹) ⟩
      0 + 0 * d ∎

  II : 0 < succ d
  II = unique-to-𝟙 (0 < succ d)
division' (succ a) d = f (maximal-from-given' (λ - → - * succ d ≤ succ a) (succ a) (λ q → ≤-decidable (q * succ d) (succ a)) ii)
 where
  i : (0 + 0 * d) ≤ succ a
  i = transport (_≤ succ a) (zero-left-is-zero (succ d) ⁻¹) (zero-least (succ a))
    
  ii : Σ k ꞉ ℕ , (k * succ d ≤ succ a) × (k ≤ succ a)
  ii = 0 , i , zero-least (succ a)

  f : Σ q ꞉ ℕ , q ≤ succ a × (q * succ d) ≤ succ a × ((n : ℕ) → n ≤ succ a → n * succ d ≤ succ a → n ≤ q)
    → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
  f (q , l₁ , l₂ , qf) = g (subtraction (q * succ d) (succ a) l₂)
   where
    g : Σ r ꞉ ℕ , r + q * succ d ≡ succ a
      → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
    g (r , rf) = q , r , I , II (order-split r (succ d))
     where
      I : succ a ≡ q * succ d + r
      I = succ a         ≡⟨ rf ⁻¹                                 ⟩
          r + q * succ d ≡⟨ addition-commutativity r (q * succ d) ⟩
          q * succ d + r ∎

      II : r < succ d ∔ r ≥ succ d → r < succ d
      II (inl z) = z
      II (inr z) = 𝟘-elim (not-less-than-itself q IV)
       where
        III : succ q * succ d ≤ succ a
        III = transport₂ _≤_ α (addition-commutativity (q * succ d) r ∙ rf) β
         where
          α : q * succ d + succ d ≡ succ q * succ d
          α = q * succ d + succ d     ≡⟨ ap (q * succ d +_) (mult-left-id (succ d) ⁻¹) ⟩
              q * succ d + 1 * succ d ≡⟨ distributivity-mult-over-nat' q 1 (succ d) ⁻¹ ⟩
              (q + 1) * succ d        ≡⟨ refl ⟩
              succ q * succ d ∎

          β : q * succ d + succ d ≤ q * succ d + r
          β = ≤-n-monotone-left (succ d) r (q * succ d) z

        IV : q < q
        IV = qf (succ q) (product-less-than-cancellable (succ q) d (succ a) III) III

division-agrees-with-division' : (x y : ℕ) → division x y ≡ division' x y
division-agrees-with-division' a d = division-is-prop a (succ d) (division a d) (division' a d)
-}
\end{code}

