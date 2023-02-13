1\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Type
open import Integers.Multiplication
open import Integers.Order
open import Integers.Parity
open import Rationals.Fractions hiding (_≈_ ; ≈-sym ; ≈-trans ; ≈-refl)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Type
open import Naturals.Addition
open import Naturals.Division
open import Naturals.Exponents
open import Naturals.HCF
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Order
open import Naturals.Parity
open import Naturals.Properties
open import Notation.Order
open import MLTT.Plus-Properties
open import UF.Base hiding (_≈_)
open import UF.Miscelanea
open import UF.Subsingletons
open import TypeTopology.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated

module Dyadics.Rationals where

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
is-ℤ[1/2]-is-prop z n = +-is-prop ℕ-is-set (×-is-prop (<-is-prop-valued 0 n) (ℤodd-is-prop z)) I
 where
  I : n ＝ 0 → ¬ (0 < n × ℤodd z)
  I n＝0 (0<n , odd-z) = not-less-than-itself 0 (transport (0 <_) n＝0 0<n)

is-ℤ[1/2]-is-discrete : ((z , n) : ℤ × ℕ) → is-discrete (is-ℤ[1/2] z n)
is-ℤ[1/2]-is-discrete (z , n) = +-is-discrete (λ x y → inl (ℕ-is-set x y))
                                   (×-is-discrete (λ x y → inl (<-is-prop-valued 0 n x y))
                                                  (λ x y → inl (ℤodd-is-prop z x y)))
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , is-ℤ[1/2] z n

ℤ[1/2]-is-discrete : is-discrete ℤ[1/2]
ℤ[1/2]-is-discrete = Σ-is-discrete (×-is-discrete ℤ-is-discrete ℕ-is-discrete) is-ℤ[1/2]-is-discrete

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
terms. Hence, we must factor our operations through a "normalisation",
similarly to our approach to standard rationals.

Due to this normalisation, we introduce an equivalence relation, and
prove that equivalent dyadics are equal. In order to prove properties
of dyadic operations, we will prove that dyadics are equivalent.

\begin{code}

normalise-pos-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-pos-lemma z 0        = (z , 0) , (inl refl)
normalise-pos-lemma z (succ n) =
 Cases (ℤeven-or-odd z) (λ ez → (λ (k , e) → normalise-pos-lemma k n) (ℤeven-is-multiple-of-two z ez))
                        (λ oz → (z , succ n) , inr (⋆ , oz))

normalise-pos : ℤ × ℕ → ℤ[1/2]
normalise-pos (z , n) = normalise-pos-lemma z n

dnum : ℤ[1/2] → ℤ
dnum ((p , _) , _) = p

dden : ℤ[1/2] → ℕ
dden ((_ , a) , _) = a

\end{code}

We can now retrieve properties of a normalised dyadic rational by
pattern matching and evaluating cases.

\begin{code}

normalise-pos-odd-num : ((p , a) : ℤ × ℕ) → ℤodd p → dnum (normalise-pos (p , a)) ＝ p
normalise-pos-odd-num (p , 0)      odd-p = refl
normalise-pos-odd-num (p , succ a) odd-p = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p) → ℤeven-or-odd p ＝ inl ep → dnum (normalise-pos (p , succ a)) ＝ p
  I ep _ = 𝟘-elim (ℤeven-not-odd p ep odd-p)
  
  II : (op : ℤodd p) → ℤeven-or-odd p ＝ inr op → dnum (normalise-pos (p , succ a)) ＝ p
  II op e = ap dnum (Cases-equality-r _ _ (ℤeven-or-odd p) op e)

normalise-pos-odd-denom : ((p , a) : ℤ × ℕ) → ℤodd p → dden (normalise-pos (p , a)) ＝ a
normalise-pos-odd-denom (p , 0)      odd-p = refl
normalise-pos-odd-denom (p , succ a) odd-p = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p) → ℤeven-or-odd p ＝ inl ep → dden (normalise-pos (p , succ a)) ＝ succ a
  I ep e = 𝟘-elim (ℤeven-not-odd p ep odd-p)
  
  II : (op : ℤodd p) → ℤeven-or-odd p ＝ inr op → dden (normalise-pos (p , succ a)) ＝ succ a
  II op e = ap dden (Cases-equality-r _ _ (ℤeven-or-odd p) op e)

-- (λ ep e →
--            (λ (p/2 , e) → (λ (k' , (e₁ , e₂)) → {!!})
--              (normalise-pos-info (p , a)))
--  (ℤeven-is-multiple-of-two p ep))
{-
normalise-pos-info : ((p , a) : ℤ × ℕ) → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , a)) * pos (2^ k))
                                                 × (a ＝ dden (normalise-pos (p , a)) + k)
normalise-pos-info (p , 0)      = 0 , refl , refl
normalise-pos-info (p , succ a) = equality-cases (ℤeven-or-odd p) I II
 where
  I : (ep : ℤeven p)
    → ℤeven-or-odd p ＝ inl ep
    → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
              × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
  I ep e = course-of-values-induction (λ a' → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a')) * pos (2^ k))
                                                 × (succ a' ＝ dden (normalise-pos (p , succ a')) + k)) i a
   where
    i : (n : ℕ) → ((m : ℕ) → m < n → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ m)) * pos (2^ k))
                                             × (succ m ＝ dden (normalise-pos (p , succ m)) + k))
      → {!!}
    i = {!!}
 
{-
t (ℤeven-is-multiple-of-two p ep)
   where
    t : (Σ p' ꞉ ℤ , p ＝ pos 2 * p') → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
                                               × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
    t (p' , e) = succ k , {!!}
     where
      IH : Σ k ꞉ ℕ , (p' ＝ dnum (normalise-pos (p' , a)) * pos (2^ k))
                   × (a ＝ dden (normalise-pos (p' , a)) + k)
      IH = normalise-pos-info (p' , a)
      k = pr₁ IH
-}
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
-}

{-
normalise-pos-info : ((p , a) : ℤ × ℕ) → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , a)) * pos (2^ k))
                                                 × (a ＝ dden (normalise-pos (p , a)) + k)
normalise-pos-info (p , 0)      = 0 , refl , refl
normalise-pos-info (p , succ a) = Cases (ℤeven-or-odd p) I II
 where
  I : ℤeven p → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
                        × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
  I even-p = {!!}

  II : ℤodd p → Σ k ꞉ ℕ , (p ＝ dnum (normalise-pos (p , succ a)) * pos (2^ k))
                        × (succ a ＝ dden (normalise-pos (p , succ a)) + k)
  II odd-p = 0 , i , ii
   where
    i : p ＝ dnum (normalise-pos (p , succ a))
    i = normalise-pos-odd-num (p , succ a) odd-p ⁻¹

    ii : succ a ＝ dden (normalise-pos (p , succ a))
    ii = {!!}
-}
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

{-
TODO : Introduce Integers Exponents File.
-}

exponents-not-zero' : (m : ℕ) → not-zero (pos (2^ m))
exponents-not-zero' m iz = exponents-not-zero m (pos-lc I)
 where
  I : pos (2^ m) ＝ pos 0
  I = from-is-zero (pos (2^ m)) iz

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
      x * m' * p' ＝⟨ ap (_* p') e₁ ⟩
      y * n' * p' ＝⟨ ℤ-mult-rearrangement y n' p' ⟩
      y * p' * n' ＝⟨ ap (_* n') e₂ ⟩
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

≈'-lt-consequence : ((x , m) (y , n) : ℤ × ℕ) → (x , m) ≈' (y , n) → m ＝ 0 → ¬ (n > 0 × ℤodd y)
≈'-lt-consequence (x , m) (y , 0)      e m＝0 (n>0 , oy) = 𝟘-elim n>0
≈'-lt-consequence (x , m) (y , succ n) e m＝0 (n>0 , oy) = ℤodd-not-even y oy (transport ℤeven I II)
 where
  I : x * pos (2^ (succ n)) ＝ y
  I = x * pos (2^ (succ n)) ＝⟨ e ⟩
      y * pos (2^ m)        ＝⟨ ap (λ - → y * pos (2^ -)) m＝0 ⟩
      y * pos (2^ 0)        ＝⟨ refl ⟩
      y ∎
  II : ℤeven (x * pos (2^ (succ n)))
  II = ℤtimes-even-is-even' x (pos (2^ (succ n))) (2-exponents-even n)

≈'-reduce  : (x y : ℤ) (n : ℕ) → (x , 1) ≈' (y , succ (succ n)) → (x , 0) ≈' (y , succ n)
≈'-reduce  x y n e = ℤ-mult-right-cancellable (x * pos (2^ (succ n))) (y * pos (2^ 0)) (pos 2) id I
 where
  I : x * pos (2^ (succ n)) * pos 2 ＝ y * pos (2^ 0) * pos 2
  I = x * pos (2^ (succ n)) * pos 2   ＝⟨ ℤ*-assoc x (pos (2^ (succ n))) (pos 2)                       ⟩
      x * (pos (2^ (succ n)) * pos 2) ＝⟨ ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ n) ℕ* 2)      ＝⟨ ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ (succ n)))    ＝⟨ e                                                            ⟩
      y * pos (2^ 1)                  ＝⟨ ap (y *_) (pos-multiplication-equiv-to-ℕ 2 1) ⁻¹             ⟩
      y * (pos 2 * pos 1)             ＝⟨ refl                                                         ⟩
      y * pos (2^ 0) * pos 2          ∎

≈'-to-＝' : (x : ℤ) (m : ℕ) (y : ℤ) (n : ℕ) → (x , m) ≈' (y , n) → m > 0 × ℤodd x → n > 0 × ℤodd y → (x , m) ＝ (y , n)
≈'-to-＝' x  m               y  0               e (m>0 , ox) (n>0 , on) = 𝟘-elim n>0
≈'-to-＝' x  0               y  (succ n)        e (m>0 , ox) (n>0 , on) = 𝟘-elim m>0
≈'-to-＝' x  1               y  1               e (m>0 , ox) (n>0 , on) = to-×-＝ (ℤ-mult-right-cancellable x y (pos (2^ 1)) id e) refl
≈'-to-＝' x  1               y  (succ (succ n)) e (m>0 , ox) (n>0 , on) = 𝟘-elim (≈'-lt-consequence (x , 0) (y , succ n) (≈'-reduce x y n e) refl (⋆ , on))
≈'-to-＝' x  (succ (succ m)) y  1               e (m>0 , ox) (n>0 , on) = 𝟘-elim (≈'-lt-consequence (y , 0) (x , succ m) (≈'-reduce y x m (e ⁻¹)) refl (⋆ , ox))
≈'-to-＝' x  (succ (succ m)) y  (succ (succ n)) e (m>0 , ox) (n>0 , on) = III (from-×-＝' (≈'-to-＝' x (succ m) y (succ n) II (⋆ , ox) (⋆ , on)))
 where
  I : x * pos (2^ (succ n)) * pos 2 ＝ y * pos (2^ (succ m)) * pos 2
  I = x * pos (2^ (succ n)) * pos 2   ＝⟨ ℤ*-assoc x (pos (2^ (succ n))) (pos 2)                       ⟩
      x * (pos (2^ (succ n)) * pos 2) ＝⟨ ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ n) ℕ* 2)      ＝⟨ ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ (succ n)))    ＝⟨ e                                                            ⟩
      y * pos (2^ (succ (succ m)))    ＝⟨ ap (λ - → y * pos -) (mult-commutativity 2 (2^ (succ m)))    ⟩
      y * pos (2^ (succ m) ℕ* 2)      ＝⟨ ap (y *_) (pos-multiplication-equiv-to-ℕ (2^ (succ m)) 2 ⁻¹) ⟩
      y * (pos (2^ (succ m)) * pos 2) ＝⟨ ℤ*-assoc y (pos (2^ (succ m))) (pos 2) ⁻¹ ⟩
      y * pos (2^ (succ m)) * pos 2   ∎

  II : x * pos (2^ (succ n)) ＝ y * pos (2^ (succ m))
  II = ℤ-mult-right-cancellable (x * pos (2^ (succ n))) (y * pos (2^ (succ m))) (pos 2) id I

  III : (x ＝ y) × (succ m ＝ succ n) → x , succ (succ m) ＝ y , succ (succ n)
  III (x＝y , m＝n) = to-×-＝ x＝y (ap succ m＝n)

≈'-to-＝'' : ((x , m) (y , n) : ℤ × ℕ) → (x , m) ≈' (y , n) → m > 0 × ℤodd x → n > 0 × ℤodd y → (x , m) ＝ (y , n)
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
≈-to-＝ ((x , n) , p) ((y , m) , q) eq =
 to-subtype-＝ (λ (x , n) → is-ℤ[1/2]-is-prop x n) (≈-to-＝-lemma (x , n) (y , m) eq p q)

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

ℤ[1/2]-to-normalise-pos : (((x , n) , e) : ℤ[1/2]) → ((x , n) , e) ＝ normalise-pos (x , n)
ℤ[1/2]-to-normalise-pos ((x , 0)        , inl n＝0)       = to-subtype-＝ (λ (x , n) → is-ℤ[1/2]-is-prop x n) refl
ℤ[1/2]-to-normalise-pos ((x , (succ n)) , inl n＝0)       = 𝟘-elim (positive-not-zero n n＝0)
ℤ[1/2]-to-normalise-pos ((x , 0)        , inr (0<0 , oz)) = 𝟘-elim (not-less-than-itself 0 0<0)
ℤ[1/2]-to-normalise-pos ((x , succ n)   , inr (0<n , oz)) =
 ap (λ zzz → dep-cases
     (λ ez → normalise-pos-lemma (pr₁ (ℤeven-is-multiple-of-two x ez)) n)
     (λ oz₁ → (x , succ n) , inr (⋆ , oz₁)) zzz)
      (ℤeven-or-odd-is-prop x (inr oz) (ℤeven-or-odd x))

ℤ[1/2]-from-normalise-pos : (z : ℤ) → (n : ℕ) → Σ q ꞉ ℤ[1/2] , q ＝ normalise-pos (z , n)
ℤ[1/2]-from-normalise-pos z n = (normalise-pos (z , n)) , refl
{-
≈'-normalise-pos' : (p : ℤ × ℕ) → p ≈' from-ℤ[1/2] (normalise-pos p)
≈'-normalise-pos' (p , a) = γ
 where
  find-dyadic : Σ q ꞉ ℤ[1/2] , q ＝ normalise-pos (p , a)
  find-dyadic = ℤ[1/2]-from-normalise-pos p a

  q' = pr₁ find-dyadic
  q = pr₁ (pr₁ q')
  b = pr₂ (pr₁ q')

  γ : (p , a) ≈' (q , b)
  γ = {!!}
-}
≈-normalise-pos : (((z , a) , p) : ℤ[1/2]) → (((z , a) , p)) ≈ normalise-pos (z , a)
≈-normalise-pos (z , α) = ＝-to-≈ (z , α) (normalise-pos z) (ℤ[1/2]-to-normalise-pos (z , α))

≈-ap : (f : ℤ[1/2] → ℤ[1/2]) (x y : ℤ[1/2]) → x ≈ y → f x ≈ f y
≈-ap f x y e = ＝-to-≈ (f x) (f y) (ap f (≈-to-＝ x y e))

≈-transport : (A : ℤ[1/2] → 𝓤 ̇) {x y : ℤ[1/2]} → x ≈ y → A x → A y
≈-transport A {x} {y} e = transport A (≈-to-＝ x y e)

-- normalise-pos-reduce : (z : ℤ) → (n : ℕ) → normalise-pos (z * pos 2 , succ n) ＝ normalise-pos (z , n)
-- normalise-pos-reduce = {!!}
  
\end{code}

The following proofs relate dyadic rationals to rationals.

\begin{code}

ℤ[1/2]-lt-lemma : (x : ℤ) → (n : ℕ) → ℤodd x → is-in-lowest-terms (x , pred (2^ (succ n)))
ℤ[1/2]-lt-lemma x n ox = (1-divides-all (abs x) , 1-divides-all (succ (pred (2^ (succ n))))) , I
 where
  I : (d : ℕ) → is-common-divisor d (abs x) (succ (pred (2^ (succ n)))) → d ∣ 1
  I d icd-d = III II
   where
    II : is-common-divisor d (abs x) (2^ (succ n))
    II = transport (λ - → is-common-divisor d (abs x) -) (succ-pred' (2^ (succ n)) (exponents-not-zero (succ n))) icd-d
    III : is-common-divisor d (abs x) (2^ (succ n)) → d ∣ 1
    III (d|x , d|2^sn) = odd-power-of-two-coprime d (abs x) (succ n) ox d|x d|2^sn

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((x , n)      , inl n＝0)       = (x , 0) , (denom-zero-lt x)
ℤ[1/2]-to-ℚ ((x , 0)      , inr (0<n , ox)) = 𝟘-elim 0<n
ℤ[1/2]-to-ℚ ((x , succ n) , inr (0<n , ox)) = (x , pred (2^ (succ n))) , (ℤ[1/2]-lt-lemma x n ox)

\end{code}

Boilerplate

\begin{code}

≈-trans₂ : (x y z a : ℤ[1/2]) → x ≈ y → y ≈ z → z ≈ a → x ≈ a
≈-trans₂ x y z a p q r = ≈-trans x y a p (≈-trans y z a q r)

≈-trans₃ : (x y z a b : ℤ[1/2]) → x ≈ y → y ≈ z → z ≈ a → a ≈ b → x ≈ b
≈-trans₃ x y z a b p q r s = ≈-trans₂ x y z b p q (≈-trans z a b r s)

≈-trans₄ : (x y z a b c : ℤ[1/2]) → x ≈ y → y ≈ z → z ≈ a → a ≈ b → b ≈ c → x ≈ c
≈-trans₄ x y z a b c p q r s t = ≈-trans₃ x y z a c p q r (≈-trans a b c s t)

≈-trans₅ : (x y z a b c d : ℤ[1/2]) → x ≈ y → y ≈ z → z ≈ a → a ≈ b → b ≈ c → c ≈ d → x ≈ d
≈-trans₅ x y z a b c d p q r s t u = ≈-trans₄ x y z a b d p q r s (≈-trans b c d t u)

\end{code}
