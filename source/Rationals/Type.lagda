Andrew Sneap, November 2020 - March 2021

In this file I define rational numbers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Integers.Abs
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Division
open import Naturals.HCF
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Rationals.Fractions
open import TypeTopology.SigmaDiscreteAndTotallySeparated
open import UF.Base hiding (_≈_)
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

module Rationals.Type where

ℚ : 𝓤₀ ̇
ℚ = Σ q ꞉ 𝔽 , is-in-lowest-terms q

ℚ⁴ = ℚ × ℚ × ℚ × ℚ

is-in-lowest-terms-is-discrete : (q : 𝔽)
                               → is-discrete (is-in-lowest-terms q)
is-in-lowest-terms-is-discrete q α β
 = inl (is-in-lowest-terms-is-prop q α β)

ℚ-is-discrete : is-discrete ℚ
ℚ-is-discrete = Σ-is-discrete 𝔽-is-discrete is-in-lowest-terms-is-discrete

ℚ-is-set : is-set ℚ
ℚ-is-set = discrete-types-are-sets ℚ-is-discrete

to𝔽 : ℚ → 𝔽
to𝔽 (q , _) = q

toℚlemma : ((x , a) : 𝔽)
         → Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ＝ (pos (succ h)) ℤ* x')
                                            × (succ a ＝ (succ h) ℕ* succ a'))
toℚlemma (pos a , b) = f (divbyhcf a (succ b))
 where
  f : Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ＝ a) × (h ℕ* y ＝ succ b))
                                  × coprime x y → _
  f (h , x , 0 , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (0 , x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b γ)
   where
    γ : succ b ＝ 0
    γ = succ b      ＝⟨ γ₂ ⁻¹                   ⟩
        0 ℕ* succ y ＝⟨ zero-left-base (succ y) ⟩
        0           ∎
  f (succ h , x , succ y , (γ₁ , γ₂) , r) = γ
   where
    I : pos a ＝ pos (succ h) ℤ* pos x
    I = pos a                 ＝⟨ ap pos γ₁ ⁻¹                                ⟩
        pos (succ h ℕ* x)     ＝⟨ pos-multiplication-equiv-to-ℕ (succ h) x ⁻¹ ⟩
        pos (succ h) ℤ* pos x ∎

    γ : _
    γ = ((pos x , y) , coprime-to-coprime' x (succ y) r) , h , I , (γ₂ ⁻¹)
toℚlemma (negsucc a , b) = f (divbyhcf (succ a) (succ b))
 where
  f : (Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ＝ (succ a))
                               × (h ℕ* y ＝ succ b))
                               × coprime x y) → _
  f (h , x , 0 , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (h , 0 , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero a (γ₁ ⁻¹))
  f (0 , succ x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b γ)
   where
    γ : succ b ＝ 0
    γ = succ b      ＝⟨ γ₂ ⁻¹                   ⟩
        0 ℕ* succ y ＝⟨ zero-left-base (succ y) ⟩
        0 ∎
  f (succ h , succ x , succ y , (γ₁ , γ₂) , r) = γ
   where
    I : pos (succ a) ＝ (pos (succ h) ℤ* pos (succ x))
    I = pos (succ a)                 ＝⟨ ap pos γ₁ ⁻¹ ⟩
        pos (succ h ℕ* succ x)       ＝⟨ i            ⟩
        pos (succ h) ℤ* pos (succ x) ∎
     where
      i = pos-multiplication-equiv-to-ℕ (succ h) (succ x) ⁻¹

    II : negsucc a ＝ pos (succ h) ℤ* negsucc x
    II = negsucc a                       ＝⟨ ap -_ I ⟩
        - (pos (succ h) ℤ* pos (succ x)) ＝⟨ i       ⟩
        pos (succ h) ℤ* (- pos (succ x)) ∎
     where
      i = negation-dist-over-mult (pos (succ h)) (pos (succ x)) ⁻¹

    q : ℚ
    q = (negsucc x , y) , coprime-to-coprime' (succ x) (succ y) r

    γ : _
    γ = q , h , II , (γ₂ ⁻¹)

toℚ : 𝔽 → ℚ
toℚ q = pr₁ (toℚlemma q)

numℚ : 𝔽 → ℤ
numℚ q = (pr₁ ∘ pr₁ ∘ pr₁) (toℚlemma q)

dnomℚ : 𝔽 → ℕ
dnomℚ q = (pr₂ ∘ pr₁ ∘ pr₁) (toℚlemma q)

hcf𝔽 : 𝔽 → ℕ
hcf𝔽 q = pr₁ (pr₂ (toℚlemma q))

iltℚ : (q : 𝔽) → is-in-lowest-terms (numℚ q , dnomℚ q)
iltℚ (x , a) = (pr₂ ∘ pr₁) (toℚlemma (x , a))

numr : ((x , a) : 𝔽) → x ＝ (pos (succ (hcf𝔽 (x , a)))) ℤ* numℚ (x , a)
numr (x , a) = pr₁ (pr₂ (pr₂ (toℚlemma (x , a))))

dnomr : ((x , a) : 𝔽) → succ a ＝ succ (hcf𝔽 (x , a)) ℕ* succ (dnomℚ (x , a))
dnomr (x , a) = pr₂ (pr₂ (pr₂ (toℚlemma (x , a))))

dnomrP : ((x , a) : 𝔽)
       → pos (succ a) ＝ pos (succ (hcf𝔽 (x , a)) ℕ* succ (dnomℚ (x , a)))
dnomrP (x , a) = ap pos (dnomr (x , a))

dnomrP' : ((x , a) : 𝔽)
        → pos (succ a) ＝ pos (succ (hcf𝔽 (x , a))) ℤ* pos (succ (dnomℚ (x , a)))
dnomrP' (x , a) = γ
 where
  h  = hcf𝔽 (x , a)
  a' = dnomℚ (x , a)

  γ : pos (succ a) ＝ pos (succ h) ℤ* pos (succ a')
  γ = pos (succ a)                  ＝⟨ i  ⟩
      pos (succ h ℕ* succ a')       ＝⟨ ii ⟩
      pos (succ h) ℤ* pos (succ a') ∎
   where
    i  = dnomrP (x , a)
    ii = pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹

0ℚ 1ℚ -1ℚ 1/3 2/3 1/2 1/5 2/5 3/5 1/4 3/4 : ℚ
-1ℚ = toℚ (negsucc 0 , 0)
0ℚ  = toℚ (pos 0 , 0)
1ℚ  = toℚ (pos 1 , 0)
1/3 = toℚ (pos 1 , 2)
2/3 = toℚ (pos 2 , 2)
1/2 = toℚ (pos 1 , 1)
1/5 = toℚ (pos 1 , 4)
2/5 = toℚ (pos 2 , 4)
3/5 = toℚ (pos 3 , 4)
4/5 = toℚ (pos 4 , 4)
1/4 = toℚ (pos 1 , 3)
3/4 = toℚ (pos 3 , 3)

equiv-equality : (p q : 𝔽) → p ≈ q ↔ toℚ p ＝ toℚ q
equiv-equality (x , a) (y , b) = γ₁ , γ₂
 where
  a' b' h h' : ℕ
  a' = dnomℚ (x , a)
  b' = dnomℚ (y , b)
  h  = hcf𝔽 (x , a)
  h' = hcf𝔽 (y , b)

  x' y' ph ph' pa' pb' : ℤ
  x'  = numℚ (x , a)
  y'  = numℚ (y , b)
  ph  = (pos ∘ succ) h
  ph' = (pos ∘ succ) h'
  pa  = (pos ∘ succ) a
  pa' = (pos ∘ succ) a'
  pb  = (pos ∘ succ) b
  pb' = (pos ∘ succ) b'

  γ-lemma : (p q r s : ℤ)
          → p ℤ* q ℤ* (r ℤ* s) ＝ p ℤ* r ℤ* (q ℤ* s)
  γ-lemma p q r s =
   p ℤ* q ℤ* (r ℤ* s)   ＝⟨ ℤ*-assoc p q (r ℤ* s)                  ⟩
   p ℤ* (q ℤ* (r ℤ* s)) ＝⟨ ap (p ℤ*_) (ℤ*-assoc q r s ⁻¹)         ⟩
   p ℤ* (q ℤ* r ℤ* s)   ＝⟨ ap (λ - → p ℤ* (- ℤ* s)) (ℤ*-comm q r) ⟩
   p ℤ* (r ℤ* q ℤ* s)   ＝⟨ ap (p ℤ*_) (ℤ*-assoc r q s)            ⟩
   p ℤ* (r ℤ* (q ℤ* s)) ＝⟨ ℤ*-assoc p r (q ℤ* s) ⁻¹               ⟩
   p ℤ* r ℤ* (q ℤ* s)   ∎

  γ₁ : (x , a) ≈ (y , b) → toℚ (x , a) ＝ toℚ (y , b)
  γ₁ e = to-subtype-＝ is-in-lowest-terms-is-prop γ
   where
    I : is-in-lowest-terms (x' , a')
    I = iltℚ (x , a)

    II : is-in-lowest-terms (y' , b')
    II = iltℚ (y , b)

    III : ph ℤ* ph' ℤ* (x' ℤ* pb') ＝ ph ℤ* ph' ℤ* (y' ℤ* pa')
    III = ph ℤ* ph' ℤ* (x' ℤ* pb') ＝⟨ γ-lemma ph ph' x' pb'                  ⟩
          ph ℤ* x' ℤ* (ph' ℤ* pb') ＝⟨ ap (ph ℤ* x' ℤ*_) (dnomrP' (y , b) ⁻¹) ⟩
          ph ℤ* x' ℤ* pb           ＝⟨ ap (_ℤ* pb) (numr (x , a) ⁻¹)          ⟩
          x ℤ* pb                  ＝⟨ e                                      ⟩
          y ℤ* pa                  ＝⟨ ap (_ℤ* pa) (numr (y , b))             ⟩
          ph' ℤ* y' ℤ* pa          ＝⟨ ap (ph' ℤ* y' ℤ*_) (dnomrP' (x , a))   ⟩
          ph' ℤ* y' ℤ* (ph ℤ* pa') ＝⟨ γ-lemma ph' ph y' pa' ⁻¹               ⟩
          ph' ℤ* ph ℤ* (y' ℤ* pa') ＝⟨ ap (_ℤ* (y' ℤ* pa')) (ℤ*-comm ph' ph)  ⟩
          ph ℤ* ph' ℤ* (y' ℤ* pa') ∎

    IV : not-zero (ph ℤ* ph')
    IV iz = non-zero-multiplication ph ph' hnz hnz' piz
     where
      hnz : ph ≠ pos 0
      hnz = pos-succ-not-zero h

      hnz' : ph' ≠ pos 0
      hnz' = pos-succ-not-zero h'

      piz : ph ℤ* ph' ＝ pos 0
      piz = from-is-zero (ph ℤ* ph') iz

    V : x' ℤ* pb' ＝ y' ℤ* pa'
    V = ℤ-mult-left-cancellable (x' ℤ* pb') (y' ℤ* pa') (ph ℤ* ph') IV III

    γ : (x' , a') ＝ (y' , b')
    γ = equiv-with-lowest-terms-is-equal (x' , a') (y' , b') V I II

  γ₂ : toℚ (x , a) ＝ toℚ (y , b) → (x , a) ≈ (y , b)
  γ₂ e = x ℤ* pos (succ b)        ＝⟨ ap (x ℤ*_) (dnomrP' (y , b))           ⟩
         x ℤ* (ph' ℤ* pb')        ＝⟨ ap (_ℤ* (ph' ℤ* pb')) (numr (x , a))   ⟩
         ph ℤ* x' ℤ* (ph' ℤ* pb') ＝⟨ γ-lemma ph x' ph' pb'                  ⟩
         ph ℤ* ph' ℤ* (x' ℤ* pb') ＝⟨ ap (_ℤ* (x' ℤ* pb')) (ℤ*-comm ph ph')  ⟩
         ph' ℤ* ph ℤ* (x' ℤ* pb') ＝⟨ ap (λ - → ph' ℤ* ph ℤ* (- ℤ* pb')) I   ⟩
         ph' ℤ* ph ℤ* (y' ℤ* pb') ＝⟨ ap (λ - → ph' ℤ* ph ℤ* (y' ℤ* -) ) II  ⟩
         ph' ℤ* ph ℤ* (y' ℤ* pa') ＝⟨ γ-lemma ph' y' ph pa' ⁻¹               ⟩
         ph' ℤ* y' ℤ* (ph ℤ* pa') ＝⟨ ap (_ℤ* (ph ℤ* pa')) (numr (y , b) ⁻¹) ⟩
         y ℤ* (ph ℤ* pa')         ＝⟨ ap (y ℤ*_) (dnomrP' (x , a) ⁻¹)        ⟩
         y ℤ* pos (succ a)        ∎
   where
    I : x' ＝ y'
    I = ap (pr₁ ∘ pr₁) e

    II : pb' ＝ pa'
    II = ap (pos ∘ succ ∘ pr₂ ∘ pr₁) (e ⁻¹)

equiv→equality : (p q : 𝔽) → p ≈ q → toℚ p ＝ toℚ q
equiv→equality p q = pr₁ (equiv-equality p q)

equality→equiv : (p q : 𝔽) → toℚ p ＝ toℚ q → p ≈ q
equality→equiv p q = pr₂ (equiv-equality p q)

toℚ-to𝔽 : ((p , α) : ℚ) → (p , α) ＝ toℚ p
toℚ-to𝔽 ((x , a) , α) = to-subtype-＝ is-in-lowest-terms-is-prop γ
 where
  x'  = numℚ (x , a)
  a'  = dnomℚ (x , a)
  h   = hcf𝔽 (x , a)
  pa' = (pos ∘ succ) a'
  pa  = (pos ∘ succ) a
  ph  = (pos ∘ succ) h

  I : coprime (abs x) (succ a)
  I = coprime'-to-coprime (abs x) (succ a) α

  II : (x , a) ≈ (x' , a')
  II = x ℤ* pa'          ＝⟨ ap (_ℤ* pa') (numr (x , a))      ⟩
       ph ℤ* x' ℤ* pa'   ＝⟨ ap (_ℤ* pa') (ℤ*-comm ph x')     ⟩
       x' ℤ* ph ℤ* pa'   ＝⟨ ℤ*-assoc x' ph pa'               ⟩
       x' ℤ* (ph ℤ* pa') ＝⟨ ap (x' ℤ*_) (dnomrP' (x , a) ⁻¹) ⟩
       x' ℤ* pa          ∎

  γ : (x , a) ＝ (x' , a')
  γ = equiv-with-lowest-terms-is-equal (x , a) (x' , a') II α (iltℚ (x , a))

ℚ-＝ : ((p , α) (q , β) : ℚ) → p ≈ q → (p , α) ＝ (q , β)
ℚ-＝ (p , α) (q , β) e = to-subtype-＝ is-in-lowest-terms-is-prop I
 where
  I : p ＝ q
  I = equiv-with-lowest-terms-is-equal p q e α β

≈-toℚ : (p : 𝔽) → p ≈ to𝔽 (toℚ p)
≈-toℚ p = equality→equiv p p' (toℚ-to𝔽 (toℚ p))
 where
  p' = to𝔽 (toℚ p)

q-has-qn : (q : ℚ) → Σ q' ꞉ 𝔽 , q ＝ toℚ q'
q-has-qn (q , α) =  q , toℚ-to𝔽 (q , α)

ℚ-zero-not-one :  ¬ (0ℚ ＝ 1ℚ)
ℚ-zero-not-one e = positive-not-zero 0 (pos-lc γ ⁻¹)
 where
  I : toℚ (pos 0 , 0) ＝ toℚ (pos 1 , 0) → (pos 0 , 0) ≈ (pos 1 , 0)
  I = equality→equiv (pos 0 , 0) (pos 1 , 0)

  γ : pos 0 ＝ pos 1
  γ = pos 0          ＝⟨ refl ⟩
      pos 0 ℤ* pos 1 ＝⟨ I e  ⟩
      pos 1 ℤ* pos 1 ＝⟨ refl ⟩
      pos 1          ∎

ℚ-positive-not-zero : (x a : ℕ) → ¬ (toℚ (pos (succ x) , a) ＝ 0ℚ)
ℚ-positive-not-zero x a e = pos-succ-not-zero x γ
 where
  I : (pos (succ x) , a) ≈ (pos 0 , 0)
  I = equality→equiv (pos (succ x) , a) (pos 0 , 0) e

  γ : pos (succ x) ＝ pos 0
  γ = pos (succ x)            ＝⟨ by-definition                    ⟩
      pos (succ x) ℤ* (pos 1) ＝⟨ I                                ⟩
      pos 0 ℤ* pos (succ a)   ＝⟨ ℤ-zero-left-base (pos (succ a))  ⟩
      pos 0                   ∎

ℚ-negative-not-zero : (x a : ℕ) → ¬ (toℚ (negsucc x , a) ＝ 0ℚ)
ℚ-negative-not-zero x a e = negsucc-not-zero x γ
 where
  I : (negsucc x , a) ≈ (pos 0 , 0)
  I = equality→equiv (negsucc x , a) (pos 0 , 0) e

  γ : negsucc x ＝ pos 0
  γ = negsucc x             ＝⟨ refl                            ⟩
      negsucc x ℤ* pos 1    ＝⟨ I                               ⟩
      pos 0 ℤ* pos (succ a) ＝⟨ ℤ-zero-left-base (pos (succ a)) ⟩
      pos 0                 ∎

numerator-zero-is-zero : (((x , a) , p) : ℚ) → x ＝ pos 0 → (x , a) , p ＝ 0ℚ
numerator-zero-is-zero ((negsucc x , a) , p) e = 𝟘-elim (negsucc-not-pos e)
numerator-zero-is-zero ((pos (succ x) , a) , p) e = 𝟘-elim γ
 where
  γ : 𝟘
  γ = positive-not-zero x (pos-lc e)
numerator-zero-is-zero ((pos 0 , a) , p) e = γ
 where
  I : (pos 0 , a) ≈ (pos 0 , 0)
  I = pos 0 ℤ* pos 1        ＝⟨ refl                               ⟩
      pos 0                 ＝⟨ ℤ-zero-left-base (pos (succ a)) ⁻¹ ⟩
      pos 0 ℤ* pos (succ a) ∎

  γ : (pos 0 , a) , p ＝ 0ℚ
  γ = (pos 0 , a) , p ＝⟨ toℚ-to𝔽 ((pos 0 , a) , p)                ⟩
      toℚ (pos 0 , a) ＝⟨ equiv→equality (pos 0 , a) (pos 0 , 0) I ⟩
      toℚ (pos 0 , 0) ＝⟨ refl                                     ⟩
      0ℚ ∎

instance
 canonical-map-𝔽-to-ℚ : Canonical-Map 𝔽 ℚ
 ι {{canonical-map-𝔽-to-ℚ}} = toℚ

ℤ-to-ℚ : ℤ → ℚ
ℤ-to-ℚ z = ι (ι z)

instance
 canonical-map-ℤ-to-ℚ : Canonical-Map ℤ ℚ
 ι {{canonical-map-ℤ-to-ℚ}} = ℤ-to-ℚ

ℕ-to-ℚ : ℕ → ℚ
ℕ-to-ℚ n = ι {{ canonical-map-ℤ-to-ℚ }} (ι n)

instance
 canonical-map-ℕ-to-ℚ : Canonical-Map ℕ ℚ
 ι {{canonical-map-ℕ-to-ℚ}} = ℕ-to-ℚ

\end{code}
