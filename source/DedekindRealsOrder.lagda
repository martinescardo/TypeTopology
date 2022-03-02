Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation
open import RationalsOrder

open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology

open import Rationals

module DedekindRealsOrder
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals pe pt fe
open PropositionalTruncation pt -- TypeTopology

_<ℝ_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) <ℝ ((Ly , Ry) , isCuty) = ∃ q ꞉ ℚ , q ∈ Rx × q ∈ Ly

instance
 Strict-Order-ℝ-ℝ : Strict-Order ℝ ℝ
 _<_ {{Strict-Order-ℝ-ℝ}} = _<ℝ_

<-is-prop : (x y : ℝ) → is-prop (x < y)
<-is-prop x y = ∃-is-prop

ℝ<-trans : (x y z : ℝ) → x < y → y < z → x < z
ℝ<-trans ((Lx , Rx) , _) ((Ly , Ry) , _ , _ , _ , _ , disjoint-y , _) ((Lz , Rz) , _ , _ , rounded-left-z , _ , _ , _) l r = ∥∥-functor I (binary-choice l r)
 where
  I : (Σ q ꞉ ℚ , q ∈ Rx × q ∈ Ly) × (Σ p ꞉ ℚ , p ∈ Ry × p ∈ Lz ) → Σ s ꞉ ℚ , s ∈ Rx × s ∈ Lz
  I ((q , (qRx , qLy)) , (p , (pRy , pLz)))
   = q , (qRx , rounded-left-a Lz rounded-left-z q p (ℚ<-coarser-than-≤ q p (disjoint-y q p (qLy , pRy))) pLz)

_≤ℝ_ : ℝ → ℝ → 𝓤₀ ̇
((Lx , Rx) , isCutx) ≤ℝ ((Ly , Ry) , isCuty) = (q : ℚ) → q ∈ Lx → q ∈ Ly

instance
 Order-ℝ-ℝ : Order ℝ ℝ
 _≤_ {{Order-ℝ-ℝ}} = _≤ℝ_

≤-is-prop : (x y : ℝ) → is-prop (x ≤ y)
≤-is-prop ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) = Π₂-is-prop fe (λ q _ → ∈-is-prop Ly q)

ℝ≤-trans : (x y z : ℝ) → x ≤ y → y ≤ z → x ≤ z
ℝ≤-trans ((Lx , Rx) , _) ((Ly , Ry) , _) ((Lz , Rz) , _) f g = λ q qLx → g q (f q qLx)

ℝ-archimedean : (x y : ℝ)
              → x < y
              → ∃ q ꞉ ℚ , q ∈ upper-cut-of x
                        × q ∈ lower-cut-of y
ℝ-archimedean x y l = l

weak-linearity : (x y z : ℝ) → x < y → x < z ∨ z < y
weak-linearity x y z l = ∥∥-rec ∨-is-prop I l
 where
  I : Σ q ꞉ ℚ , q ∈ upper-cut-of x × q ∈ lower-cut-of y → x < z ∨ z < y
  I (q , qRx , qLy) = ∥∥-rec ∨-is-prop II (binary-choice exists-r exists-s)
   where
    exists-r : ∃ r ꞉ ℚ , r < q × r ∈ upper-cut-of x
    exists-r = rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q qRx
    exists-s : ∃ s ꞉ ℚ , q < s × s ∈ lower-cut-of y
    exists-s = rounded-left-b (lower-cut-of y) (rounded-from-real-L y) q qLy
    II : (Σ r ꞉ ℚ , r < q × r ∈ upper-cut-of x) × (Σ s ꞉ ℚ , q < s × s ∈ lower-cut-of y) → x < z ∨ z < y
    II ((r , r<q , rRx) , s , q<s , sLy) = ∥∥-rec ∨-is-prop IV III
     where
      III : r ∈ lower-cut-of z ∨ s ∈ upper-cut-of z
      III = located-from-real z r s (ℚ<-trans r q s r<q q<s)
      IV : r ∈ lower-cut-of z ∔ s ∈ upper-cut-of z → x < z ∨ z < y
      IV (inl rLz) = ∣ inl ∣ r , rRx , rLz ∣ ∣
      IV (inr sRz) = ∣ inr ∣ s , sRz , sLy ∣ ∣

_♯_ : (x y : ℝ) → 𝓤₀ ̇
x ♯ y = x < y ∨ y < x

apartness-gives-inequality : (x y : ℝ) → x ♯ y → ¬ (x ≡ y)
apartness-gives-inequality x y apart e = ∥∥-rec 𝟘-is-prop I apart
 where
  I : x < y ∔ y < x → 𝟘
  I (inl l) = ∥∥-rec 𝟘-is-prop III II
   where
    II : x < x
    II = transport (x <_) (e ⁻¹) l
    III : Σ q ꞉ ℚ , q ∈ upper-cut-of x × q ∈ lower-cut-of x → 𝟘
    III (q , qRx , qLx) = ℚ<-not-itself q (disjoint-from-real x q q (qLx , qRx))
  I (inr r) = ∥∥-rec 𝟘-is-prop III II
   where
    II : y < y
    II = transport (y <_) e r
    III : Σ p ꞉ ℚ , p ∈ upper-cut-of y × p ∈ lower-cut-of y → 𝟘
    III (p , pRy , pLy) = ℚ<-not-itself p (disjoint-from-real y p p (pLy , pRy))

ℝ<-≤-trans : (x y z : ℝ) → x < y → y ≤ z → x < z
ℝ<-≤-trans x y z x<y y≤z = ∥∥-functor I x<y
 where
  I : Σ q ꞉ ℚ , q ∈ upper-cut-of x × q ∈ lower-cut-of y → Σ q' ꞉ ℚ , q' ∈ upper-cut-of x × q' ∈ lower-cut-of z
  I (q , qRx , qLy) = q , qRx , y≤z q qLy

ℝ-less-than-or-equal-not-greater : (x y : ℝ) → x ≤ y → ¬ (y < x)
ℝ-less-than-or-equal-not-greater x y x≤y y<x = ∥∥-rec 𝟘-is-prop I y<x
 where
  I : Σ q ꞉ ℚ , q ∈ upper-cut-of y × q ∈ lower-cut-of x → 𝟘
  I (q , qRy , qLx) = ℚ<-not-itself q (disjoint-from-real y q q ((x≤y q qLx) , qRy))

ℝ-less-than-not-greater-or-equal : (x y : ℝ) → x < y → ¬ (y ≤ x)
ℝ-less-than-not-greater-or-equal x y l₁ l₂ = ℝ-less-than-or-equal-not-greater y x l₂ l₁


{-
ℝ-not-less-is-greater-or-equal : (x y : ℝ) → ¬ (x < y) → y ≤ x
ℝ-not-less-is-greater-or-equal x y nl q qLy = ∥∥-rec (∈-is-prop (lower-cut-of x) q) I xR-inhabited 
 where
  xR-inhabited : inhabited-right (upper-cut-of x)
  xR-inhabited = inhabited-from-real-R x
  I : Σ p ꞉ ℚ , p ∈ upper-cut-of x → q ∈ lower-cut-of x
  I (p , pRx) = II (ℚ-trichotomous fe p q)
   where
    II : p < q ∔ (p ≡ q) ∔ q < p → q ∈ lower-cut-of x
    II (inl p<q) = ∥∥-rec (∈-is-prop (lower-cut-of x) q) III (located-from-real x p q p<q)
     where
      III : p ∈ lower-cut-of x ∔ q ∈ upper-cut-of x → q ∈ lower-cut-of x
      III (inl pLx) = 𝟘-elim (ℚ<-not-itself p (disjoint-from-real x p p (pLx , pRx)))
      III (inr qRx) = 𝟘-elim (nl ∣ q , (qRx , qLy) ∣)
    II (inr (inl p-is-q)) = 𝟘-elim (nl ∣ p , pRx , (transport (_∈ lower-cut-of y) (p-is-q ⁻¹) qLy) ∣)
    II (inr (inr q<p)) = ∥∥-rec (∈-is-prop (lower-cut-of x) q) III (located-from-real x q k (pr₁ (pr₂ from-ℚ-dense)))
     where
      from-ℚ-dense : Σ k ꞉ ℚ , q < k × k < p
      from-ℚ-dense = ℚ-dense fe q p q<p
      k = pr₁ from-ℚ-dense
      III : q ∈ lower-cut-of x ∔ k ∈ upper-cut-of x → q ∈ lower-cut-of x
      III (inl qLx) = qLx
      III (inr kRx) = {!IV!}
       where
        IV : {!!}
        IV = {!!}
-}   

ℝ≤-<-trans : (x y z : ℝ) → x ≤ y → y < z → x < z
ℝ≤-<-trans x y z x≤y y<z = ∥∥-functor I y<z
 where
  I : Σ q ꞉ ℚ , q ∈ upper-cut-of y × q ∈ lower-cut-of z
    → Σ q' ꞉ ℚ , q' ∈ upper-cut-of x × q' ∈ lower-cut-of z
  I (q , qRy , qLz) = q , ∥∥-rec (∈-is-prop (upper-cut-of x) q) III II , qLz
   where
    II : ∃ k ꞉ ℚ , k < q × k ∈ upper-cut-of y
    II = rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q qRy 

    III : Σ k ꞉ ℚ , k < q × k ∈ upper-cut-of y → q ∈ upper-cut-of x
    III (k , k<q , kRy) = ∥∥-rec (∈-is-prop (upper-cut-of x) q) IV (located-from-real x k q k<q)
     where
      IV : k ∈ lower-cut-of x ∔ q ∈ upper-cut-of x → q ∈ upper-cut-of x
      IV (inl kLx) = 𝟘-elim (ℚ<-not-itself k (disjoint-from-real y k k (x≤y k kLx , kRy)))
      IV (inr qRx) = qRx

ℝ-zero-less-than-one : 0ℝ < 1ℝ
ℝ-zero-less-than-one = ∣ 1/2 , 0<1/2 , 1/2<1 ∣

ℝ-zero-apart-from-one : 0ℝ ♯ 1ℝ
ℝ-zero-apart-from-one = ∣ inl ℝ-zero-less-than-one ∣



