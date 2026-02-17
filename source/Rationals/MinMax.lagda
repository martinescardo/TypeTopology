Andrew Sneap, February-March 2022

In this file I define min and max for rationals.

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base
open import MLTT.Plus-Properties
open import Rationals.Type
open import Rationals.Order

module Rationals.MinMax where

max' : (x y : ℚ) → (x < y) ∔ (x ＝ y) ∔ (y < x) → ℚ
max' x y (inl _) = y
max' x y (inr _) = x

max : ℚ → ℚ → ℚ
max p q = max' p q (ℚ-trichotomous p q)

max'-to-max : (x y : ℚ)
            → (t : (x < y) ∔ (x ＝ y) ∔ (y < x))
            → max' x y t ＝ max x y
max'-to-max x y t = equality-cases t I II
 where
  I : (l : x < y) → t ＝ inl l → max' x y t ＝ max x y
  I l e = max' x y t                    ＝⟨ ap (max' x y) e                    ⟩
          max' x y (inl l)              ＝⟨ ap (max' x y) (ℚ-trich-a x y l ⁻¹) ⟩
          max' x y (ℚ-trichotomous x y) ＝⟨ by-definition                      ⟩
          max x y                       ∎

  II : (l : (x ＝ y) ∔ y < x) → t ＝ inr l → max' x y t ＝ max x y
  II r e = max' x y t                    ＝⟨ ap (max' x y) e                    ⟩
           max' x y (inr r)              ＝⟨ ap (max' x y) (ℚ-trich-b x y r ⁻¹) ⟩
           max' x y (ℚ-trichotomous x y) ＝⟨ by-definition                      ⟩
           max x y                       ∎

max'-refl : (q : ℚ) → (t : (q < q) ∔ (q ＝ q) ∔ (q < q)) → max' q q t ＝ q
max'-refl q (inl l) = 𝟘-elim (ℚ<-irrefl q l)
max'-refl q (inr (inl l)) = l
max'-refl q (inr (inr l)) = 𝟘-elim (ℚ<-irrefl q l)

max-refl : (q : ℚ) → max q q ＝ q
max-refl q = I (ℚ-trichotomous q q)
 where
  I : (q < q) ∔ (q ＝ q) ∔ (q < q) → max q q ＝ q
  I t = max q q    ＝⟨ max'-to-max q q t ⁻¹ ⟩
        max' q q t ＝⟨ max'-refl q t        ⟩
        q          ∎

max'-comm : (x y : ℚ)
            → (s : (x < y) ∔ (x ＝ y) ∔ (y < x))
            → (t : (y < x) ∔ (y ＝ x) ∔ (x < y))
            → max' x y s ＝ max' y x t
max'-comm x y (inl s) (inl t)             = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x s t))
max'-comm x y (inl s) (inr (inl t))       = 𝟘-elim (ℚ<-irrefl y (transport (_< y) (t ⁻¹) s))
max'-comm x y (inl s) (inr (inr t))       = refl
max'-comm x y (inr (inl s)) (inl t)       = refl
max'-comm x y (inr (inr s)) (inl t)       = refl
max'-comm x y (inr (inl s)) (inr (inl t)) = s
max'-comm x y (inr (inl s)) (inr (inr t)) = s
max'-comm x y (inr (inr s)) (inr (inl t)) = t ⁻¹
max'-comm x y (inr (inr s)) (inr (inr t)) = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x t s))

max-comm : (p q : ℚ) → max p q ＝ max q p
max-comm x y =
 max x y                       ＝⟨ max'-to-max x y (ℚ-trichotomous x y)                    ⟩
 max' x y (ℚ-trichotomous x y) ＝⟨ max'-comm x y (ℚ-trichotomous x y) (ℚ-trichotomous y x) ⟩
 max' y x (ℚ-trichotomous y x) ＝⟨ max'-to-max y x (ℚ-trichotomous y x)                    ⟩
 max y x                       ∎

max'-to-≤ : (p q : ℚ) → (t : (p < q) ∔ (p ＝ q) ∔ (q < p))
                      → (p ≤ q) × (max' p q t ＝ q)
                      ∔ (q ≤ p) × (max' p q t ＝ p)
max'-to-≤ p q (inl t) = Cases (ℚ-trichotomous p q) I II
 where
  I : p < q → (p ≤ q) × (max' p q (inl t) ＝ q) ∔ q ≤ p × (max' p q (inl t) ＝ p)
  I l = inl ((ℚ<-coarser-than-≤ p q l) , refl)

  II : (p ＝ q) ∔ q < p
     → (p ≤ q)
     × (max' p q (inl t) ＝ q) ∔ q ≤ p × (max' p q (inl t) ＝ p)
  II (inl e) = 𝟘-elim (ℚ<-irrefl p (transport (p <_) (e ⁻¹) t))
  II (inr l) = 𝟘-elim (ℚ<-irrefl p (ℚ<-trans p q p t l))
max'-to-≤ p q (inr t) = inr (I t , refl)
 where
  I : (p ＝ q) ∔ q < p → q ≤ p
  I (inl l) = transport (q ≤_) (l ⁻¹) (ℚ≤-refl q)
  I (inr l) = ℚ<-coarser-than-≤ q p l

max-to-≤ : (p q : ℚ) → (p ≤ q) × (max p q ＝ q) ∔ q ≤ p × (max p q ＝ p)
max-to-≤ p q = I (max'-to-≤ p q (ℚ-trichotomous p q))
 where
  I : (p ≤ q) × (max' p q (ℚ-trichotomous p q) ＝ q)
    ∔ (q ≤ p) × (max' p q (ℚ-trichotomous p q) ＝ p)
    → (p ≤ q) × (max p q ＝ q) ∔ (q ≤ p) × (max p q ＝ p)
  I (inl t) = inl t
  I (inr t) = inr t

decide-max : (p q : ℚ) → (max p q ＝ q) ∔ (max p q ＝ p)
decide-max p q = +functor pr₂ pr₂ (max-to-≤ p q)

max≤ : (p q : ℚ) → p ≤ max p q
max≤ p q = I (max-to-≤ p q)
 where
  I : (p ≤ q) × (max p q ＝ q) ∔ (q ≤ p) × (max p q ＝ p) → p ≤ max p q
  I (inl (p≤q , e)) = transport (p ≤_) (e ⁻¹) p≤q
  I (inr (q≤p , e)) = transport (p ≤_) (e ⁻¹) (ℚ≤-refl p)

max≤' : (p q : ℚ) → q ≤ max p q
max≤' p q = transport (q ≤_) (max-comm q p) (max≤ q p)

min' : (x y : ℚ) → (x < y) ∔ (x ＝ y) ∔ (y < x) → ℚ
min' x y (inl _) = x
min' x y (inr _) = y

min : ℚ → ℚ → ℚ
min p q = min' p q (ℚ-trichotomous p q)

min'-to-min : (x y : ℚ)
            → (t : (x < y) ∔ (x ＝ y) ∔ (y < x)) → min' x y t ＝ min x y
min'-to-min x y t = equality-cases t I II
 where
  I : (k : x < y) → t ＝ inl k → min' x y t ＝ min x y
  I k e = min' x y t                     ＝⟨ ap (min' x y) e                    ⟩
          min' x y (inl k)               ＝⟨ ap (min' x y) (ℚ-trich-a x y k ⁻¹) ⟩
          min' x y (ℚ-trichotomous x y)  ＝⟨ by-definition                      ⟩
          min x y                        ∎

  II : (k : (x ＝ y) ∔ y < x) → t ＝ inr k → min' x y t ＝ min x y
  II k e = min' x y t                    ＝⟨ ap (min' x y) e                    ⟩
           min' x y (inr k)              ＝⟨ ap (min' x y) (ℚ-trich-b x y k ⁻¹) ⟩
           min' x y (ℚ-trichotomous x y) ＝⟨ by-definition                      ⟩
           min x y                       ∎

min'-refl : (q : ℚ) → (t : (q < q) ∔ (q ＝ q) ∔ (q < q)) → min' q q t ＝ q
min'-refl q (inl l) = 𝟘-elim (ℚ<-irrefl q l)
min'-refl q (inr (inl l)) = l
min'-refl q (inr (inr l)) = 𝟘-elim (ℚ<-irrefl q l)

min-refl : (q : ℚ) → min q q ＝ q
min-refl q = I (ℚ-trichotomous q q)
 where
  I : (q < q) ∔ (q ＝ q) ∔ (q < q) → min q q ＝ q
  I t = min q q    ＝⟨ min'-to-min q q t ⁻¹ ⟩
        min' q q t ＝⟨ min'-refl q t        ⟩
        q          ∎

min'-comm : (x y : ℚ)
            → (s : (x < y) ∔ (x ＝ y) ∔ (y < x))
            → (t : (y < x) ∔ (y ＝ x) ∔ (x < y))
            → min' x y s ＝ min' y x t
min'-comm x y (inl s) (inl t) = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x s t))
min'-comm x y (inl s) (inr (inl t)) = 𝟘-elim (ℚ<-irrefl y (transport (_< y) (t ⁻¹) s))
min'-comm x y (inl s) (inr (inr t)) = refl
min'-comm x y (inr (inl s)) (inl t) = refl
min'-comm x y (inr (inr s)) (inl t) = refl
min'-comm x y (inr (inl s)) (inr (inl t)) = t
min'-comm x y (inr (inl s)) (inr (inr t)) = s ⁻¹
min'-comm x y (inr (inr s)) (inr (inl t)) = t
min'-comm x y (inr (inr s)) (inr (inr t)) = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x t s))

min-comm : (p q : ℚ) → min p q ＝ min q p
min-comm x y =
 min x y                       ＝⟨ min'-to-min x y (ℚ-trichotomous x y)                    ⟩
 min' x y (ℚ-trichotomous x y) ＝⟨ min'-comm x y (ℚ-trichotomous x y) (ℚ-trichotomous y x) ⟩
 min' y x (ℚ-trichotomous y x) ＝⟨ min'-to-min y x (ℚ-trichotomous y x)                    ⟩
 min y x ∎


min'-to-≤ : (p q : ℚ) → (t : (p < q) ∔ (p ＝ q) ∔ (q < p))
                      → (p ≤ q) × (min' p q t ＝ p)
                      ∔ (q ≤ p) × (min' p q t ＝ q)
min'-to-≤ p q (inl t) = Cases (ℚ-trichotomous p q) I II
 where
  I : p < q
    → (p ≤ q) × (min' p q (inl t) ＝ p) ∔ (q ≤ p) × (min' p q (inl t) ＝ q)
  I l = inl ((ℚ<-coarser-than-≤ p q l) , refl)

  II : (p ＝ q) ∔ q < p
     → (p ≤ q) × (min' p q (inl t) ＝ p) ∔ (q ≤ p) × (min' p q (inl t) ＝ q)
  II (inl e) = 𝟘-elim (ℚ<-irrefl p (transport (p <_) (e ⁻¹) t))
  II (inr l) = 𝟘-elim (ℚ<-irrefl p (ℚ<-trans p q p t l))
min'-to-≤ p q (inr t) = inr (I t , refl)
 where
  I : (p ＝ q) ∔ q < p → q ≤ p
  I (inl l) = transport (q ≤_) (l ⁻¹) (ℚ≤-refl q)
  I (inr l) = ℚ<-coarser-than-≤ q p l

min-to-≤ : (p q : ℚ) → (p ≤ q) × (min p q ＝ p) ∔ (q ≤ p) × (min p q ＝ q)
min-to-≤ p q = I (min'-to-≤ p q (ℚ-trichotomous p q))
 where
  I : (p ≤ q) × (min' p q (ℚ-trichotomous p q) ＝ p)
    ∔ (q ≤ p) × (min' p q (ℚ-trichotomous p q) ＝ q)
    → (p ≤ q) × (min p q ＝ p) ∔ q ≤ p × (min p q ＝ q)
  I (inl t) = inl t
  I (inr t) = inr t

decide-min : (p q : ℚ) → (min p q ＝ p) ∔ (min p q ＝ q)
decide-min p q = +functor pr₂ pr₂ (min-to-≤ p q)

min≤ : (p q : ℚ) → min p q ≤ p
min≤ p q = I (min-to-≤ p q)
 where
  I : (p ≤ q) × (min p q ＝ p) ∔ (q ≤ p) × (min p q ＝ q)
    → min p q ≤ p
  I (inl (p≤q , e)) = transport (_≤ p) (e ⁻¹) (ℚ≤-refl p)
  I (inr (q≤p , e)) = transport (_≤ p) (e ⁻¹) q≤p

min≤' : (p q : ℚ) → min p q ≤ q
min≤' p q = transport (_≤ q) (min-comm q p) (min≤ q p)

≤-to-min' : (x y : ℚ) → x ≤ y
          → (t : (x < y) ∔ (x ＝ y) ∔ (y < x)) → x ＝ min' x y t
≤-to-min' x y l (inl t) = refl
≤-to-min' x y l (inr (inl t)) = t
≤-to-min' x y l (inr (inr t)) = I (ℚ≤-split x y l)
 where
  I : (x < y) ∔ (x ＝ y) → x ＝ min' x y (inr (inr t))
  I (inl s) = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x s t))
  I (inr s) = s

≤-to-min : (x y : ℚ) → x ≤ y → x ＝ min x y
≤-to-min x y l = ≤-to-min' x y l (ℚ-trichotomous x y)

<-to-min : (x y : ℚ) → x < y → x ＝ min x y
<-to-min x y l = ≤-to-min x y (ℚ<-coarser-than-≤ x y l)

≤-to-max' : (x y : ℚ) → x ≤ y → (t : (x < y) ∔ (x ＝ y) ∔ (y < x)) → y ＝ max' x y t
≤-to-max' x y l (inl t) = refl
≤-to-max' x y l (inr (inl t)) = t ⁻¹
≤-to-max' x y l (inr (inr t)) = I (ℚ≤-split x y l)
 where
  I : x < y ∔ (x ＝ y) → y ＝ max' x y (inr (inr t))
  I (inl s) = 𝟘-elim (ℚ<-irrefl x (ℚ<-trans x y x s t))
  I (inr s) = s ⁻¹

≤-to-max : (x y : ℚ) → x ≤ y → y ＝ max x y
≤-to-max x y l = ≤-to-max' x y l (ℚ-trichotomous x y)

<-to-max : (x y : ℚ) → x < y → y ＝ max x y
<-to-max x y l = ≤-to-max x y (ℚ<-coarser-than-≤ x y l)

min-assoc : (x y z : ℚ) → min (min x y) z ＝ min x (min y z)
min-assoc x y z = I (min-to-≤ x y) (min-to-≤ (min x y) z) (min-to-≤ y z) (min-to-≤ x (min y z))
 where
  I : (x ≤ y) × (min x y ＝ x) ∔ (y ≤ x) × (min x y ＝ y)
     → (min x y ≤ z) × (min (min x y) z ＝ min x y)
     ∔ (z ≤ min x y) × (min (min x y) z ＝ z)
     → y ≤ z × (min y z ＝ y)
     ∔ (z ≤ y) × (min y z ＝ z)
     → (x ≤ min y z) × (min x (min y z) ＝ x)
     ∔ (min y z ≤ x) × (min x (min y z) ＝ min y z)
     → min (min x y) z ＝ min x (min y z)
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ap (λ - → min x -) (e₃ ⁻¹)
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti x z (transport (_≤ z) e₁ l₂) (transport (_≤ x) e₃ l₄) ∙ e₃ ⁻¹ ∙ (e₄ ⁻¹)
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (transport (z ≤_) e₁ l₂) (ℚ≤-trans x y z l₁ l₃) ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z y (ℚ≤-trans z x y (transport (z ≤_) e₁ l₂) l₁) l₃ ∙ (e₃ ⁻¹) ∙ (e₄ ⁻¹)
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = ap (λ - → min - z) e₁ ∙ ap (λ - → min x -) (e₃ ⁻¹)
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ (e₃ ⁻¹) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti y x l₁ (transport (x ≤_) e₃ l₄) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ e₁ ∙ (e₃ ⁻¹) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti y x l₁ (ℚ≤-trans x z y (transport (x ≤_) e₃ l₄) l₃) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti y z (transport (_≤ z) e₁ l₂) l₃ ∙ (e₃ ⁻¹) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z y (transport (z ≤_) e₁ l₂) l₃ ∙ e₁ ⁻¹ ∙ ap (λ - → min x -) (e₃ ⁻¹)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = ap (λ - → min - z) e₁ ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (ℚ≤-trans z y x l₃ l₁) (transport (x ≤_) e₃ l₄) ∙ (e₄ ⁻¹)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ (e₃ ⁻¹) ∙ (e₄ ⁻¹)

min-to-max : (x y : ℚ) → min x y ＝ x → max x y ＝ y
min-to-max x y e = I (min-to-≤ x y)
 where
  I : (x ≤ y) × (min x y ＝ x) ∔ y ≤ x × (min x y ＝ y)
    → max x y ＝ y
  I (inl (l₁ , e₁)) = ≤-to-max x y l₁ ⁻¹
  I (inr (l₂ , e₂)) = ≤-to-max x y (transport (_≤ y) (II ⁻¹) (ℚ≤-refl y)) ⁻¹
   where
    II : x ＝ y
    II = (e ⁻¹) ∙ e₂

max-assoc : (x y z : ℚ) → max (max x y) z ＝ max x (max y z)
max-assoc x y z = I (max-to-≤ x y) (max-to-≤ (max x y) z) (max-to-≤ y z) (max-to-≤ x (max y z))
 where
  I : (x ≤ y) × (max x y ＝ y) ∔ y ≤ x × (max x y ＝ x)
    → (max x y ≤ z) × (max (max x y) z ＝ z)
    ∔ (z ≤ max x y) × (max (max x y) z ＝ max x y)
    → (y ≤ z) × (max y z ＝ z)
    ∔ (z ≤ y) × (max y z ＝ y)
    → (x ≤ max y z) × (max x (max y z) ＝ max y z)
    ∔ (max y z ≤ x) × (max x (max y z) ＝ x)
    → max (max x y) z ＝ max x (max y z)
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (transport (_≤ x) e₃ l₄) (ℚ≤-trans x y z l₁ l₃) ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z y l₃ (transport (_≤ z) e₁ l₂) ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (ℚ≤-trans z y x l₃ (transport (_≤ x) e₃ l₄)) (ℚ≤-trans x y z l₁ (transport (_≤ z) e₁ l₂)) ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti y z l₃ (transport (z ≤_) e₁ l₂) ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti y x (ℚ≤-trans y z x l₃ (transport (_≤ x) e₃ l₄)) l₁ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ap (λ - → max x -) (e₃ ⁻¹)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (transport (_≤ x) e₃ l₄) (transport (_≤ z) e₁ l₂) ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z y l₃ (ℚ≤-trans y x z l₁ (transport (_≤ z) e₁ l₂)) ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ℚ≤-anti z x (ℚ≤-trans z y x l₃ (transport (_≤ x) e₃ l₄)) (transport (_≤ z) e₁ l₂) ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ e₁ ∙ ℚ≤-anti x z (transport (x ≤_) e₃ l₄) (transport (z ≤_) e₁ l₂) ∙ e₃ ⁻¹ ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inl (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ e₁ ∙ e₄ ⁻¹
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inl (l₄ , e₄)) = e₂ ∙ ap (λ - → max x -) (e₃ ⁻¹)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) (inr (l₃ , e₃)) (inr (l₄ , e₄)) = e₂ ∙ ap (λ - → max x -) (e₃ ⁻¹)

min₃ : (a b c : ℚ) → ℚ
min₃ a b c = min (min a b) c

min₄ : (a b c d : ℚ) → ℚ
min₄ a b c d = min (min (min a b) c) d

max₃ : (a b c : ℚ) → ℚ
max₃ a b c = max (max a b) c

max₄ : (a b c d : ℚ) → ℚ
max₄ a b c d = max (max (max a b) c) d

min≤max : (a b : ℚ) → min a b ≤ max a b
min≤max a b = I (min-to-≤ a b)
 where
  I : (a ≤ b) × (min a b ＝ a)
    ∔ (b ≤ a) × (min a b ＝ b)
    → min a b ≤ max a b
  I (inl (a≤b , e)) = transport₂ _≤_ (e ⁻¹) (min-to-max a b e ⁻¹) a≤b
  I (inr (b≤a , e)) = transport₂ _≤_ (e ⁻¹) (min-to-max b a (min-comm b a ∙ e) ⁻¹ ∙ max-comm b a) b≤a

min₃≤max₃ : (a b c : ℚ) → min₃ a b c ≤ max₃ a b c
min₃≤max₃ a b c = I (min-to-≤ (min a b) c) (max-to-≤ (max a b) c)
 where
  I : (min a b ≤ c) × (min (min a b) c ＝ min a b)
    ∔ (c ≤ (min a b)) × (min (min a b) c ＝ c)
    → (max a b ≤ c) × (max (max a b) c ＝ c)
    ∔ (c ≤ max a b) × (max (max a b) c ＝ max a b)
    → min₃ a b c ≤ max₃ a b c
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) l₁
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) (min≤max a b)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) (ℚ≤-refl c)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) l₂

min₄≤max₄ : (a b c d : ℚ) → min₄ a b c d ≤ max₄ a b c d
min₄≤max₄ a b c d = I (min-to-≤ (min₃ a b c) d) (max-to-≤ (max₃ a b c) d)
 where
  I : (min₃ a b c ≤ d) × (min (min₃ a b c) d ＝ min₃ a b c)
    ∔ (d ≤ min₃ a b c) × (min (min₃ a b c) d ＝ d)
    → (max₃ a b c ≤ d) × (max (max₃ a b c) d ＝ d)
    ∔ (d ≤ max₃ a b c) × (max (max₃ a b c) d ＝ max₃ a b c)
    → min₄ a b c d ≤ max₄ a b c d
  I (inl (l₁ , e₁)) (inl (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) l₁
  I (inl (l₁ , e₁)) (inr (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) (min₃≤max₃ a b c)
  I (inr (l₁ , e₁)) (inl (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) (ℚ≤-refl d)
  I (inr (l₁ , e₁)) (inr (l₂ , e₂)) = transport₂ _≤_ (e₁ ⁻¹) (e₂ ⁻¹) l₂

\end{code}
