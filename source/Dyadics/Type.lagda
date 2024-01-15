Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Exponentiation
open import Integers.Multiplication
open import Integers.Order
open import Integers.Parity
open import Integers.Type
open import MLTT.Plus-Properties
open import Naturals.Addition
open import Naturals.Division
open import Naturals.Exponentiation
open import Naturals.HCF
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Order
open import Naturals.Parity
open import Naturals.Properties
open import Notation.Order
open import Rationals.Fractions hiding (_≈_ ; ≈-sym ; ≈-trans ; ≈-refl)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Type
open import TypeTopology.SigmaDiscreteAndTotallySeparated
open import UF.Base hiding (_≈_)
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

module Dyadics.Type where

\end{code}

We will define the dyadics as a sigma type. Hence, we begin by stating
the type of the property which defines a dyadic. The condition is that
either the denominator is zero, or the denominator is greater than
zero, but the numerator is odd. This type contains "simplified"
dyadics.

By properties of order, naturals, integers it follows that the dyadics
are a set.

\begin{code}

is-ℤ[1/2] : (z : ℤ) (n : ℕ) → 𝓤₀ ̇
is-ℤ[1/2] z n = (n ＝ 0) ∔ (n > 0 × ℤodd z)

is-ℤ[1/2]-is-prop : (z : ℤ) (n : ℕ) → is-prop (is-ℤ[1/2] z n)
is-ℤ[1/2]-is-prop z n = +-is-prop ℕ-is-set II I
 where
  I : n ＝ 0 → ¬ (0 < n × ℤodd z)
  I n＝0 (0<n , odd-z) = not-less-than-itself 0 (transport (0 <_) n＝0 0<n)

  II : is-prop (0 < n × ℤodd z)
  II = ×-is-prop (<-is-prop-valued 0 n) (ℤodd-is-prop z)

is-ℤ[1/2]-is-discrete : ((z , n) : ℤ × ℕ) → is-discrete (is-ℤ[1/2] z n)
is-ℤ[1/2]-is-discrete (z , n) = props-are-discrete (is-ℤ[1/2]-is-prop z n)

ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , is-ℤ[1/2] z n

ℤ[1/2]-is-discrete : is-discrete ℤ[1/2]
ℤ[1/2]-is-discrete = Σ-is-discrete I is-ℤ[1/2]-is-discrete
 where
  I : is-discrete (ℤ × ℕ)
  I = ×-is-discrete ℤ-is-discrete ℕ-is-discrete

ℤ[1/2]-is-set : is-set ℤ[1/2]
ℤ[1/2]-is-set = discrete-types-are-sets ℤ[1/2]-is-discrete

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , (inl refl)

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , (inl refl)

1/2ℤ[1/2] : ℤ[1/2]
1/2ℤ[1/2] = (pos 1 , 1) , (inr (⋆ , ⋆))

\end{code}

To define operations on dyadics, we need to consider how to normalise
dyadics into their simplified forms. For example, multiplication of
dyadics using standard rational multiplication gives
numerator/denominator combinations which are not always in lowest
terms. Hence, we must factor our operations through a "normalisation"
function, similarly to our approach to standard rationals.

Due to this normalisation, we introduce an equivalence relation, and
prove that equivalent dyadics are equal. In order to prove properties
of dyadic operations, we will prove that dyadics are equivalent.

\begin{code}

normalise-pos-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-pos-lemma z 0        = (z , 0) , (inl refl)
normalise-pos-lemma z (succ n) =
 Cases (ℤeven-or-odd z) case-even case-odd
 where
  case-even : ℤeven z → ℤ[1/2]
  case-even ez = (λ (k , e) → normalise-pos-lemma k n) divide-by-two
   where
    divide-by-two : Σ k ꞉ ℤ , z ＝ pos 2 * k
    divide-by-two = ℤeven-is-multiple-of-two z ez

  case-odd : ℤodd z → ℤ[1/2]
  case-odd oz = (z , succ n) , inr (⋆ , oz)

normalise-pos : ℤ × ℕ → ℤ[1/2]
normalise-pos (z , n) = normalise-pos-lemma z n

dnum : ℤ[1/2] → ℤ
dnum ((p , _) , _) = p

dden : ℤ[1/2] → ℕ
dden ((_ , a) , _) = a

\end{code}

We can now retrieve properties of a normalised dyadic rational by
pattern matching and evaluating cases. This requires a number of
lemmas, including finding the numerators and denominators for specific
values of p, and the inductive step of dividing through by a factor of
2.

\begin{code}

normalise-pos-odd-num : ((p , a) : ℤ × ℕ) → ℤodd p
                                          → dnum (normalise-pos (p , a)) ＝ p
normalise-pos-odd-num (p , 0)      odd-p = refl
normalise-pos-odd-num (p , succ a) odd-p = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p) → ℤeven-or-odd p ＝ inl ep
                     → dnum (normalise-pos (p , succ a)) ＝ p
  I ep _ = 𝟘-elim (ℤeven-not-odd p ep odd-p)

  II : (op : ℤodd p) → ℤeven-or-odd p ＝ inr op
                     → dnum (normalise-pos (p , succ a)) ＝ p
  II op e = ap dnum (Cases-equality-r _ _ (ℤeven-or-odd p) op e)

normalise-pos-odd-denom : ((p , a) : ℤ × ℕ) → ℤodd p
                                            → dden (normalise-pos (p , a)) ＝ a
normalise-pos-odd-denom (p , 0)      odd-p = refl
normalise-pos-odd-denom (p , succ a) odd-p = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p) → ℤeven-or-odd p ＝ inl ep
                      → dden (normalise-pos (p , succ a)) ＝ succ a
  I ep e = 𝟘-elim (ℤeven-not-odd p ep odd-p)

  II : (op : ℤodd p) → ℤeven-or-odd p ＝ inr op
                      → dden (normalise-pos (p , succ a)) ＝ succ a
  II op e = ap dden (Cases-equality-r _ _ (ℤeven-or-odd p) op e)

normalise-pos-even-prev : (p : ℤ) (a : ℕ)
                        → (ep : ℤeven p)
                        → ((p/2 , _) : Σ p/2 ꞉ ℤ , p ＝ pos 2 * p/2)
                        → normalise-pos (p/2 , a) ＝ normalise-pos (p , succ a)
normalise-pos-even-prev p a ep (p/2 , e) = equality-cases (ℤeven-or-odd p) I II
 where
  I : (even-p : ℤeven p)
    → ℤeven-or-odd p ＝ inl even-p
    → normalise-pos (p/2 , a) ＝ normalise-pos (p , succ a)
  I even-p e₂
   = normalise-pos (p/2 , a)        ＝⟨ refl ⟩
     normalise-pos-lemma p/2 a      ＝⟨ i ⟩
     normalise-pos-lemma p/2' a     ＝⟨ ii ⟩
     normalise-pos-lemma p (succ a) ＝⟨ refl ⟩
     normalise-pos (p , succ a)     ∎
   where
    p/2' : ℤ
    p/2' = pr₁ (ℤeven-is-multiple-of-two p even-p)

    e₃ : p ＝ pos 2 * p/2'
    e₃ = pr₂ (ℤeven-is-multiple-of-two p even-p)

    e₄ : pos 2 * p/2 ＝ pos 2 * p/2'
    e₄ = pos 2 * p/2 ＝⟨ e ⁻¹ ⟩
         p           ＝⟨ e₃ ⟩
         pos 2 * p/2' ∎

    halfs-of-p-equal : p/2 ＝ p/2'
    halfs-of-p-equal = ℤ-mult-left-cancellable p/2 p/2' (pos 2) id e₄

    i : normalise-pos-lemma p/2 a ＝ normalise-pos-lemma p/2' a
    i = ap (λ - → normalise-pos-lemma - a) halfs-of-p-equal

    ii : normalise-pos-lemma p/2' a ＝ normalise-pos-lemma p (succ a)
    ii = Cases-equality-l _ _ (ℤeven-or-odd p) even-p e₂ ⁻¹

  II : (op : ℤodd p) → ℤeven-or-odd p ＝ inr op
                     → normalise-pos (p/2 , a) ＝ normalise-pos (p , succ a)
  II op = 𝟘-elim (ℤeven-not-odd p ep op)

normalise-pos-info' : (p : ℤ) → (a : ℕ)
                    → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , a)) * pos (2^ k))
                    × (a ＝ dden (normalise-pos (p , a)) + k)
normalise-pos-info' p 0      = 0 , refl , refl
normalise-pos-info' p  (succ a) = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p)
    → ℤeven-or-odd p ＝ inl ep
    → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
              × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
  I ep e = γ₁ (ℤeven-is-multiple-of-two p ep)
   where
    γ₁ : Σ p/2 ꞉ ℤ , p ＝ pos 2 * p/2
       → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
                 × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
    γ₁ (p/2 , e₂) = γ₂ (normalise-pos-info' p/2 a)
     where
      γ₂ : (Σ k' ꞉ ℕ , (p/2 ＝ dnum (normalise-pos (p/2 , a)) * pos (2^ k')) ×
                         (a ＝ dden (normalise-pos (p/2 , a)) + k'))

          → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
                    × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
      γ₂ (k' , e₃ , e₄) = (succ k') , α , β
       where
        k'' = pos (2^ k')
        α : p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ (succ k'))
        α = p                                                      ＝⟨ e₂  ⟩
            pos 2 * p/2                                            ＝⟨ i   ⟩
            pos 2 * (dnum (normalise-pos (p/2 , a)) * k'')         ＝⟨ ii  ⟩
            pos 2 * dnum (normalise-pos (p/2 , a)) * k''           ＝⟨ iii ⟩
            dnum (normalise-pos (p/2 , a)) * pos 2 * k''           ＝⟨ iv  ⟩
            dnum (normalise-pos (p/2 , a)) * (pos 2 * k'')         ＝⟨ v   ⟩
            dnum (normalise-pos (p/2 , a)) * pos (2^ (succ k'))    ＝⟨ vi  ⟩
            dnum (normalise-pos (p , succ a)) * pos (2^ (succ k')) ∎
         where
          i   = ap (pos 2 *_) e₃
          ii  = ℤ*-assoc (pos 2) (dnum (normalise-pos (p/2 , a))) k'' ⁻¹
          iii = ap (_* k'') (ℤ*-comm (pos 2) (dnum (normalise-pos (p/2 , a))))
          iv  = ℤ*-assoc (dnum (normalise-pos (p/2 , a))) (pos 2) k''
          v   = ap (dnum (normalise-pos (p/2 , a)) *_)
                 (pos-multiplication-equiv-to-ℕ 2 (2^ k'))
          vi  = ap (λ - → dnum - * pos (2^ (succ k')))
                 (normalise-pos-even-prev p a ep (p/2 , e₂))

        β : succ a ＝ dden (normalise-pos (p , succ a)) + succ k'
        β = succ a                                       ＝⟨ i    ⟩
             succ (dden (normalise-pos (p/2 , a)) + k')  ＝⟨ refl ⟩
             dden (normalise-pos (p/2 , a)) + succ k'    ＝⟨ ii   ⟩
             dden (normalise-pos (p , succ a)) + succ k' ∎
         where
          i = ap succ e₄
          ii = ap (λ - → dden - + succ k')
                (normalise-pos-even-prev p a ep (p/2 , e₂))

  II : (op : ℤodd p)
    → ℤeven-or-odd p ＝ inr op
    → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
              × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
  II op e = 0 , i , ii
   where
    i : p ＝ dnum (normalise-pos (p , succ a))
    i = normalise-pos-odd-num (p , succ a) op ⁻¹

    ii : succ a ＝ dden (normalise-pos (p , succ a))
    ii = normalise-pos-odd-denom (p , succ a) op ⁻¹

\end{code}

This function finds the k value for which (2^k) is a common factor of
a dyadic rational. It is proved with it's arguments seperated in the
above function, to satisy Agda's termination checker.

\begin{code}

normalise-pos-info : ((p , a) : ℤ × ℕ)
                   → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , a)) * pos (2^ k))
                             × (a ＝ dden (normalise-pos (p , a)) + k)
normalise-pos-info (p , a) = normalise-pos-info' p a

\end{code}

We also defined a normalisation process for when an operation results
in a negative on the denominator (i.e 2^ (- k)) for some (k : ℕ). This
is not needed for the standard field operations but may be useful for
more exotic dyadic rational functions.

\begin{code}

normalise-neg-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-neg-lemma z 0        = (z * pos 2 , 0) , (inl refl)
normalise-neg-lemma z (succ n) = normalise-neg-lemma (z * pos 2) n

normalise-neg : ℤ × ℕ → ℤ[1/2]
normalise-neg (z , n) = normalise-neg-lemma z n

normalise : ℤ × ℤ → ℤ[1/2]
normalise (z , pos n)     = normalise-pos (z , n)
normalise (z , negsucc n) = normalise-neg (z , n)

from-ℤ[1/2] : ℤ[1/2] → ℤ × ℕ
from-ℤ[1/2] = pr₁

\end{code}

We define two equivalence relations. The first is by considering an
equivalence on a numerator / denominator pair only, without the proof
that they are simplified. The second defines an equivalence on two
dyadic rationals, and is defined in terms of the first.

Sometimes we have two dyadics rationals of the form (p , α) (q , β),
and we want to prove equality using an equivalence p ≈' q. In other
cases we may have dyadic rationals of the form (normalise-pos p)
(normalise-pos q), and we want to prove equality using the equivalence
using p ≈' q.

Usually, the first case isn't fruitful, and instead we prove that
 (p , α) ≈ normalise-pos p,
 (q , β) ≈ normalise-pos q.

Given an operation _⊙_, we then show that
 (p , α) ⊙ (q , β) ＝ (normalise-pos p) ⊙ (normalise-pos q)
                   ＝ normalise-pos (p ⊙' q)
for some operation _⊙'_ defined on (ℤ × ℕ) × (ℤ × ℕ).

All of this machinery, as well as the usual equivalence laws are
defined below.

\begin{code}

_≈'_ : (p q : ℤ × ℕ) → 𝓤₀ ̇
(x , n) ≈' (y , m) = x * pos (2^ m) ＝ y * pos (2^ n)

≈'-sym : (p q : ℤ × ℕ) → p ≈' q → q ≈' p
≈'-sym p q e = e ⁻¹

≈'-trans : (p q r : ℤ × ℕ) → p ≈' q → q ≈' r → p ≈' r
≈'-trans (x , n) (y , m) (z , p) e₁ e₂ = γ
 where
  p' m' n' : ℤ
  p' = pos (2^ p)
  m' = pos (2^ m)
  n' = pos (2^ n)

  I : x * p' * m' ＝ z * n' * m'
  I = x * p' * m' ＝⟨ ℤ-mult-rearrangement x p' m' ⟩
      x * m' * p' ＝⟨ ap (_* p') e₁                ⟩
      y * n' * p' ＝⟨ ℤ-mult-rearrangement y n' p' ⟩
      y * p' * n' ＝⟨ ap (_* n') e₂                ⟩
      z * m' * n' ＝⟨ ℤ-mult-rearrangement z m' n' ⟩
      z * n' * m' ∎

  VI : not-zero m'
  VI = exponents-not-zero' m

  γ : x * p' ＝ z * n'
  γ = ℤ-mult-right-cancellable (x * p') (z * n') m' VI I

≈'-refl : (p : ℤ × ℕ) → p ≈' p
≈'-refl p = refl

_≈_ : (p q : ℤ[1/2]) → 𝓤₀ ̇
(p , _) ≈ (q , _) = p ≈' q

infix 0 _≈_

≈-sym : (x y : ℤ[1/2]) → x ≈ y → y ≈ x
≈-sym (p , _) (q , _) e = ≈'-sym p q e

≈-trans : (x y z : ℤ[1/2]) → x ≈ y → y ≈ z → x ≈ z
≈-trans (p , _) (q , _) (r , _) e₁ e₂ = ≈'-trans p q r e₁ e₂

≈-refl : (p : ℤ[1/2]) → p ≈ p
≈-refl (p , _) = ≈'-refl p

≈'-to-＝-0 : ((x , m) (y , n) : ℤ × ℕ)
              → (x , m) ≈' (y , n)
              → m ＝ 0
              → n ＝ 0
              → (x , m) ＝ (y , n)
≈'-to-＝-0 (x , m) (y , n) e m＝0 n＝0 = to-×-＝ I (m＝0 ∙ n＝0 ⁻¹)
 where
  I : x ＝ y
  I = x              ＝⟨ refl                                  ⟩
      x * pos (2^ 0) ＝⟨ ap (λ z → x * (pos (2^ z))) (n＝0 ⁻¹) ⟩
      x * pos (2^ n) ＝⟨ e                                     ⟩
      y * pos (2^ m) ＝⟨ ap (λ z → y * (pos (2^ z))) m＝0      ⟩
      y * pos (2^ 0) ＝⟨ refl                                  ⟩
      y              ∎

≈'-lt-consequence : ((x , m) (y , n) : ℤ × ℕ)
                  → (x , m) ≈' (y , n) → m ＝ 0 → ¬ (n > 0 × ℤodd y)
≈'-lt-consequence (x , m) (y , 0)      e m＝0 (n>0 , oy) = 𝟘-elim n>0
≈'-lt-consequence (x , m) (y , succ n) e m＝0 (n>0 , oy) = γ
 where
  I : x * pos (2^ (succ n)) ＝ y
  I = x * pos (2^ (succ n)) ＝⟨ e ⟩
      y * pos (2^ m)        ＝⟨ ap (λ - → y * pos (2^ -)) m＝0 ⟩
      y * pos (2^ 0)        ＝⟨ refl ⟩
      y ∎

  II : ℤeven (x * pos (2^ (succ n)))
  II = ℤtimes-even-is-even' x (pos (2^ (succ n))) (2-exponents-even n)

  γ : 𝟘
  γ = ℤodd-not-even y oy (transport ℤeven I II)

≈'-reduce  : (x y : ℤ) (n : ℕ)
           → (x , 1) ≈' (y , succ (succ n))
           → (x , 0) ≈' (y , succ n)
≈'-reduce  x y n e
 = ℤ-mult-right-cancellable (x * n') (y * pos (2^ 0)) (pos 2) id I
 where
  n' = pos (2^ (succ n))
  I : x * n' * pos 2 ＝ y * pos (2^ 0) * pos 2
  I = x * n' * pos 2                  ＝⟨ i    ⟩
      x * (n' * pos 2)                ＝⟨ ii   ⟩
      x * pos (2^ (succ n) ℕ* 2)      ＝⟨ iii  ⟩
      x * pos (2^ (succ (succ n)))    ＝⟨ e    ⟩
      y * pos (2^ 1)                  ＝⟨ iv   ⟩
      y * (pos 2 * pos 1)             ＝⟨ refl ⟩
      y * pos (2^ 0) * pos 2          ∎

   where
    i   = ℤ*-assoc x n' (pos 2)
    ii  = ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)
    iii = ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)
    iv  = ap (y *_) (pos-multiplication-equiv-to-ℕ 2 1) ⁻¹

≈'-to-＝' : (x : ℤ) (m : ℕ) (y : ℤ) (n : ℕ)
          → (x , m) ≈' (y , n)
          → m > 0 × ℤodd x
          → n > 0 × ℤodd y
          → (x , m) ＝ (y , n)
≈'-to-＝' x m y 0 e (m>0 , ox) (n>0 , on)        = 𝟘-elim n>0
≈'-to-＝' x 0 y (succ n) e (m>0 , ox) (n>0 , on) = 𝟘-elim m>0
≈'-to-＝' x 1 y 1 e (m>0 , ox) (n>0 , on)
 = to-×-＝ (ℤ-mult-right-cancellable x y (pos (2^ 1)) id e) refl
≈'-to-＝' x 1 y (succ (succ n)) e (m>0 , ox) (n>0 , on)
 = 𝟘-elim i
  where
   ii : x * pos (2^ (succ n)) ＝ y * pos (2^ 0)
   ii = ≈'-reduce x y n e
   i : 𝟘
   i = ≈'-lt-consequence (x , 0) (y , succ n) ii refl (⋆ , on)
≈'-to-＝' x (succ (succ m)) y 1 e (m>0 , ox) (n>0 , on)
 = 𝟘-elim i
  where
   ii : (y , 0) ≈' (x , succ m)
   ii = ≈'-reduce y x m (e ⁻¹)
   i : 𝟘
   i = ≈'-lt-consequence (y , 0) (x , succ m) ii refl (⋆ , ox)
≈'-to-＝' x  (succ (succ m)) y  (succ (succ n)) e (m>0 , ox) (n>0 , on)
 = III (from-×-＝' (≈'-to-＝' x (succ m) y (succ n) II (⋆ , ox) (⋆ , on)))
  where
   n' = pos (2^ (succ n))
   m' = pos (2^ (succ m))
   I : x * n' * pos 2 ＝ y * m' * pos 2
   I = x * n' * pos 2               ＝⟨ i   ⟩
       x * (n' * pos 2)             ＝⟨ ii  ⟩
       x * pos (2^ (succ n) ℕ* 2)   ＝⟨ iii ⟩
       x * pos (2^ (succ (succ n))) ＝⟨ e   ⟩
       y * pos (2^ (succ (succ m))) ＝⟨ iv  ⟩
       y * pos (2^ (succ m) ℕ* 2)   ＝⟨ v   ⟩
       y * (m' * pos 2)             ＝⟨ vi  ⟩
       y * m' * pos 2               ∎
    where
     i   = ℤ*-assoc x (n') (pos 2)
     ii  = ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)
     iii = ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)
     iv  = ap (λ - → y * pos -) (mult-commutativity 2 (2^ (succ m)))
     v   = ap (y *_) (pos-multiplication-equiv-to-ℕ (2^ (succ m)) 2 ⁻¹)
     vi  = ℤ*-assoc y m' (pos 2) ⁻¹

   II : x * n' ＝ y * m'
   II = ℤ-mult-right-cancellable (x * n') (y * m') (pos 2) id I

   III : (x ＝ y) × (succ m ＝ succ n) → x , succ (succ m) ＝ y , succ (succ n)
   III (x＝y , m＝n) = to-×-＝ x＝y (ap succ m＝n)

≈'-to-＝'' : ((x , m) (y , n) : ℤ × ℕ)
           → (x , m) ≈' (y , n) → m > 0 × ℤodd x
           → n > 0 × ℤodd y
           → (x , m) ＝ (y , n)
≈'-to-＝'' (x , m) (y , n) e p q = ≈'-to-＝' x m y n e p q

≈-to-＝-lemma : ((x , m) (y , n) : ℤ × ℕ)
              → (x , m) ≈' (y , n)
              → is-ℤ[1/2] x m
              → is-ℤ[1/2] y n
              → (x , m) ＝ (y , n)
≈-to-＝-lemma x y e (inl p) (inl q) = ≈'-to-＝-0 x y e p q
≈-to-＝-lemma x y e (inl p) (inr q) = 𝟘-elim (≈'-lt-consequence x y e p q)
≈-to-＝-lemma x y e (inr p) (inl q) = 𝟘-elim (≈'-lt-consequence y x (e ⁻¹) q p)
≈-to-＝-lemma x y e (inr p) (inr q) = ≈'-to-＝'' x y e p q

≈-to-＝ : (x y : ℤ[1/2]) → x ≈ y → x ＝ y
≈-to-＝ ((x , n) , p) ((y , m) , q) eq = to-subtype-＝ I II
 where
  I : ((x , n) : ℤ × ℕ) → is-prop (is-ℤ[1/2] x n)
  I (x , n) = is-ℤ[1/2]-is-prop x n

  II : x , n ＝ y , m
  II = ≈-to-＝-lemma (x , n) (y , m) eq p q

＝-to-≈ : (x y : ℤ[1/2]) → x ＝ y → x ≈ y
＝-to-≈ ((x , a) , α) ((y , b) , β) e = γ
 where
  γ₁ : x ＝ y
  γ₁ = ap (pr₁ ∘ pr₁) e
  γ₂ : b ＝ a
  γ₂ = ap (pr₂ ∘ pr₁) (e ⁻¹)
  γ : ((x , a) , α) ≈ ((y , b) , β)
  γ = x * pos (2^ b) ＝⟨ ap (_* pos (2^ b)) γ₁ ⟩
      y * pos (2^ b) ＝⟨ ap (λ - → y * pos (2^ -)) γ₂ ⟩
      y * pos (2^ a) ∎

ℤ[1/2]-to-normalise-pos : ((p , e) : ℤ[1/2]) → (p , e) ＝ normalise-pos p
ℤ[1/2]-to-normalise-pos ((x , 0) , inl n＝0)
 = to-subtype-＝ (λ (x , n) → is-ℤ[1/2]-is-prop x n) refl
ℤ[1/2]-to-normalise-pos ((x , (succ n)) , inl n＝0)
 = 𝟘-elim (positive-not-zero n n＝0)
ℤ[1/2]-to-normalise-pos ((x , 0) , inr (0<0 , oz))
 = 𝟘-elim (not-less-than-itself 0 0<0)
ℤ[1/2]-to-normalise-pos ((x , succ n) , inr (0<n , oz)) = ap f e
 where
  e : inr oz ＝ ℤeven-or-odd x
  e = ℤeven-or-odd-is-prop x (inr oz) (ℤeven-or-odd x)

  f : ℤeven x ∔ ℤodd x → ℤ[1/2]
  f = dep-cases case-even case-odd
   where
    case-even : ℤeven x → ℤ[1/2]
    case-even ez = normalise-pos-lemma x/2 n
     where
      x/2 = pr₁ (ℤeven-is-multiple-of-two x ez)
    case-odd : ℤodd x → ℤ[1/2]
    case-odd oz = (x , succ n) , inr (⋆ , oz)

ℤ[1/2]-from-normalise-pos : (z : ℤ) (n : ℕ)
                          → Σ q ꞉ ℤ[1/2] , q ＝ normalise-pos (z , n)
ℤ[1/2]-from-normalise-pos z n = (normalise-pos (z , n)) , refl

≈'-normalise-pos : (p : ℤ × ℕ) → p ≈' from-ℤ[1/2] (normalise-pos p)
≈'-normalise-pos (p , a) = γ (normalise-pos-info (p , a))
 where
  p' : ℤ
  p' = dnum (normalise-pos (p , a))

  a' : ℕ
  a' = dden (normalise-pos (p , a))

  γ : Σ k ꞉ ℕ , (p ＝ p' * pos (2^ k))
              × (a ＝ a' + k)
    → (p , a) ≈' (p' , a')
  γ (k , e₁ , e₂) = p * pos (2^ a')                 ＝⟨ i   ⟩
                    p' * pos (2^ k) * pos (2^ a')   ＝⟨ ii  ⟩
                    p' * (pos (2^ k) * pos (2^ a')) ＝⟨ iii ⟩
                    p' * pos (2^ k ℕ* 2^ a')        ＝⟨ iv  ⟩
                    p' * pos (2^ (k + a'))          ＝⟨ v   ⟩
                    p' * pos (2^ (a' + k))          ＝⟨ vi  ⟩
                    p' * pos (2^ a) ∎
   where
    i   = ap (_* pos (2^ a')) e₁
    ii  = ℤ*-assoc p' (pos (2^ k)) (pos (2^ a'))
    iii = ap (p' *_) (pos-multiplication-equiv-to-ℕ (2^ k) (2^ a'))
    iv  = ap (λ - → p' * pos -) (prod-of-powers 2 k a')
    v   = ap (λ - → p' * pos (2^ -)) (addition-commutativity k a')
    vi  = ap (λ - → p' * pos (2^ -)) (e₂ ⁻¹)

≈-normalise-pos : ((z , α) : ℤ[1/2]) → (z , α) ≈ normalise-pos z
≈-normalise-pos (z , α)
 = ＝-to-≈ (z , α) (normalise-pos z) (ℤ[1/2]-to-normalise-pos (z , α))

≈-ap : (f : ℤ[1/2] → ℤ[1/2]) (x y : ℤ[1/2]) → x ≈ y → f x ≈ f y
≈-ap f x y e = ＝-to-≈ (f x) (f y) (ap f (≈-to-＝ x y e))

≈-transport : (A : ℤ[1/2] → 𝓤 ̇ ){x y : ℤ[1/2]} → x ≈ y → A x → A y
≈-transport A {x} {y} e = transport A (≈-to-＝ x y e)

≈'-to-＝ : (p q : ℤ × ℕ) → p ≈' q → normalise-pos p ＝ normalise-pos q
≈'-to-＝ p q e = ≈-to-＝ (normalise-pos p) (normalise-pos q) γ
 where
  I : from-ℤ[1/2] (normalise-pos p) ≈' p
  I = (≈'-normalise-pos p) ⁻¹

  II : q ≈' from-ℤ[1/2] (normalise-pos q)
  II = ≈'-normalise-pos q

  III : from-ℤ[1/2] (normalise-pos p) ≈' q
  III = ≈'-trans (from-ℤ[1/2] (normalise-pos p)) p q I e

  γ : from-ℤ[1/2] (normalise-pos p) ≈' from-ℤ[1/2] (normalise-pos q)
  γ = ≈'-trans
      (from-ℤ[1/2] (normalise-pos p))
      q
      (from-ℤ[1/2] (normalise-pos q))
      III II

ℤ[1/2]-numerator-zero-is-zero' : (a : ℕ) → normalise-pos (pos 0 , a) ＝ 0ℤ[1/2]
ℤ[1/2]-numerator-zero-is-zero' 0        = refl
ℤ[1/2]-numerator-zero-is-zero' (succ a) = I ⁻¹ ∙ IH
 where
  IH : normalise-pos (pos 0 , a) ＝ 0ℤ[1/2]
  IH = ℤ[1/2]-numerator-zero-is-zero' a

  I : normalise-pos (pos 0 , a) ＝ normalise-pos (pos 0 , succ a)
  I = normalise-pos-even-prev (pos 0) a ⋆ (pos 0 , refl)

ℤ[1/2]-numerator-zero-is-zero : ((x , a) : ℤ × ℕ)
                              → x ＝ pos 0
                              → normalise-pos (x , a) ＝ 0ℤ[1/2]
ℤ[1/2]-numerator-zero-is-zero (pos 0 , a) e = ℤ[1/2]-numerator-zero-is-zero' a
ℤ[1/2]-numerator-zero-is-zero (pos (succ x) , a) e
 = 𝟘-elim (pos-succ-not-zero x e)
ℤ[1/2]-numerator-zero-is-zero (negsucc x , a) e = 𝟘-elim (negsucc-not-pos e)

\end{code}

The following proofs relate dyadic rationals to rationals.

\begin{code}

ℤ[1/2]-lt-lemma : (x : ℤ) (n : ℕ)
                → ℤodd x
                → is-in-lowest-terms (x , pred (2^ (succ n)))
ℤ[1/2]-lt-lemma x n ox = coprime-to-coprime' _ _ γ₄
 where
  n' = 2^ (succ n)

  γ₁ : 1 ∣ abs x
  γ₁ = 1-divides-all (abs x)

  γ₂ : 1 ∣ succ (pred n')
  γ₂ = 1-divides-all (succ (pred n'))

  γ₃ : (d : ℕ) → is-common-divisor d (abs x) (succ (pred n')) → d ∣ 1
  γ₃ d icd-d = III II
   where
    i : succ (pred n') ＝ n'
    i = succ-pred' n' (exponents-not-zero (succ n))

    II : is-common-divisor d (abs x) n'
    II = transport (λ - → is-common-divisor d (abs x) -) i icd-d

    III : is-common-divisor d (abs x) n' → d ∣ 1
    III (d|x , d|n') = odd-power-of-two-coprime d (abs x) (succ n) ox d|x d|n'

  γ₄ : is-in-lowest-terms' (x , pred (2^ (succ n)))
  γ₄ = (γ₁ , γ₂) , γ₃

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((x , n)      , inl n＝0)       = (x , 0) , (denom-zero-lt x)
ℤ[1/2]-to-ℚ ((x , 0)      , inr (0<n , ox)) = 𝟘-elim 0<n
ℤ[1/2]-to-ℚ ((x , succ n) , inr (0<n , ox)) = (x , pred (2^ (succ n))) , I
 where
  I : is-in-lowest-terms (x , pred (2^ (succ n)))
  I = ℤ[1/2]-lt-lemma x n ox

\end{code}

Boilerplate transitivity proofs.

\begin{code}

≈-trans₂ : (x y z a : ℤ[1/2]) → x ≈ y → y ≈ z
                              → z ≈ a
                              → x ≈ a
≈-trans₂ x y z a p q r = ≈-trans x y a p (≈-trans y z a q r)

≈-trans₃ : (x y z a b : ℤ[1/2]) → x ≈ y → y ≈ z
                                → z ≈ a → a ≈ b
                                → x ≈ b
≈-trans₃ x y z a b p q r s = ≈-trans₂ x y z b p q (≈-trans z a b r s)

≈-trans₄ : (x y z a b c : ℤ[1/2]) → x ≈ y → y ≈ z
                                  → z ≈ a → a ≈ b
                                  → b ≈ c
                                  → x ≈ c
≈-trans₄ x y z a b c p q r s t = ≈-trans₃ x y z a c p q r (≈-trans a b c s t)

≈-trans₅ : (x y z a b c d : ℤ[1/2]) → x ≈ y → y ≈ z
                                    → z ≈ a → a ≈ b
                                    → b ≈ c → c ≈ d
                                    → x ≈ d
≈-trans₅ x y z a b c d p q r s t u =
 ≈-trans₄ x y z a b d p q r s (≈-trans b c d t u)

\end{code}
