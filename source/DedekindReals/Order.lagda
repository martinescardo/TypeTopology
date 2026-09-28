Andrew Sneap, March 2021
Updated March 2022

In this file I define order of Dedekind Reals, and prove
some key properties.

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Order

open import UF.Embeddings
open import UF.FunExt
open import UF.PropTrunc
open import UF.Powerset
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Rationals.Type

module DedekindReals.Order
         (fe : Fun-Ext)
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
       where

open import DedekindReals.Type fe pe pt
open PropositionalTruncation pt

_<ℝ_ : ℝ → ℝ → 𝓤₀ ̇
x <ℝ y = ∃ q ꞉ ℚ , (x < q) × (q < y)

instance
 Strict-Order-ℝ-ℝ : Strict-Order ℝ ℝ
 _<_ {{Strict-Order-ℝ-ℝ}} = _<ℝ_

 Strict-Order-Chain-ℝ-ℝ-ℝ : Strict-Order-Chain ℝ ℝ ℝ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℝ-ℝ-ℝ}} p q r = (p < q) × (q < r)

<-is-prop : (x y : ℝ) → is-prop (x < y)
<-is-prop x y = ∃-is-prop

ℝ<-trans : (x y z : ℝ) → x < y → y < z → x < z
ℝ<-trans x y z x<y y<z = ∥∥-functor I (binary-choice x<y y<z)
 where
  I : (Σ k ꞉ ℚ , x < k < y)
    × (Σ l ꞉ ℚ , y < l < z)
    →  Σ m ꞉ ℚ , x < m < z
  I ((k , (x<k , k<y)) , l , (y<l , l<z)) = k , (x<k , k<z)
   where
    k<l : k < l
    k<l = disjoint-from-real y k l (k<y , y<l)
    k<z : k < z
    k<z = rounded-left-c (lower-cut-of z) (rounded-from-real-L z) k l k<l l<z

_≤ℝ_ : ℝ → ℝ → 𝓤₀ ̇
x ≤ℝ y = (q : ℚ) → q < x → q < y

instance
 Order-ℝ-ℝ : Order ℝ ℝ
 _≤_ {{Order-ℝ-ℝ}} = _≤ℝ_

≤-is-prop : (x y : ℝ) → is-prop (x ≤ y)
≤-is-prop ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) = Π₂-is-prop fe (λ q _ → ∈-is-prop Ly q)

ℝ≤-trans : (x y z : ℝ) → x ≤ y → y ≤ z → x ≤ z
ℝ≤-trans ((Lx , Rx) , _) ((Ly , Ry) , _) ((Lz , Rz) , _) f g = λ q qLx → g q (f q qLx)

ℝ-archimedean : (x y : ℝ)
              → x < y
              → ∃ q ꞉ ℚ , (x < q) × (q < y)
ℝ-archimedean x y l = l

weak-linearity : (x y z : ℝ) → x < y → (x < z) ∨ (z < y)
weak-linearity x y z l = ∥∥-rec ∨-is-prop I l
 where
  I : Σ q ꞉ ℚ , q > x × q < y → (x < z) ∨ (z < y)
  I (q , qRx , qLy) = ∥∥-rec ∨-is-prop II (binary-choice exists-r exists-s)
   where
    exists-r : ∃ r ꞉ ℚ , r < q × r > x
    exists-r = rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q qRx
    exists-s : ∃ s ꞉ ℚ , q < s < y
    exists-s = rounded-left-b (lower-cut-of y) (rounded-from-real-L y) q qLy
    II : (Σ r ꞉ ℚ , r < q × r > x) × (Σ s ꞉ ℚ , q < s < y) → (x < z) ∨ (z < y)
    II ((r , r<q , rRx) , s , q<s , sLy) = ∥∥-rec ∨-is-prop IV III
     where
      III : (r < z) ∨ (z < s)
      III = ℝ-locatedness z r s (ℚ<-trans r q s r<q q<s)
      IV : (r < z) ∔ (z < s) → (x < z) ∨ (z < y)
      IV (inl rLz) = ∣ inl ∣ r , rRx , rLz ∣ ∣
      IV (inr sRz) = ∣ inr ∣ s , sRz , sLy ∣ ∣

weak-linearity' : (x y z : ℝ) → x < y → (x < z) ∨ (z < y)
weak-linearity' x y z l = do
 (q , x<q , q<y) ← l
 (r , r<q , x<r) ← rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q x<q
 (s , q<s , s<y) ← rounded-left-b (lower-cut-of y) (rounded-from-real-L y) q q<y
 t               ← ℝ-locatedness z r s (ℚ<-trans r q s r<q q<s)
 Cases t (λ r<z → ∣ inl ∣ r , x<r , r<z ∣ ∣)
         (λ z<s → ∣ inr ∣ s , z<s , s<y ∣ ∣)

_♯_ : (x y : ℝ) → 𝓤₀ ̇
x ♯ y = (x < y) ∨ (y < x)

apartness-gives-inequality : (x y : ℝ) → x ♯ y → ¬ (x ＝ y)
apartness-gives-inequality x y apart e = ∥∥-rec 𝟘-is-prop I apart
 where
  I : ¬ ((x < y) ∔ (y < x))
  I (inl l) = ∥∥-rec 𝟘-is-prop III II
   where
    II : x < x
    II = transport (x <_) (e ⁻¹) l
    III : ¬ (Σ q ꞉ ℚ , (x < q) × (q < x))
    III (q , x<q , q<x) = ℚ<-not-itself-from-ℝ q x (q<x , x<q)
  I (inr r) = ∥∥-rec 𝟘-is-prop III II
   where
    II : y < y
    II = transport (y <_) e r
    III : ¬ (Σ p ꞉ ℚ , (p > y) × (p < y))
    III (p , y<p , p<y) = ℚ<-not-itself-from-ℝ p y (p<y , y<p)

ℝ<-≤-trans : (x y z : ℝ) → x < y → y ≤ z → x < z
ℝ<-≤-trans x y z x<y y≤z = ∥∥-functor I x<y
 where
  I : Σ q ꞉ ℚ , q > x × q < y → Σ q' ꞉ ℚ , q' > x × q' < z
  I (q , qRx , qLy) = q , qRx , y≤z q qLy

ℝ-less-than-or-equal-not-greater : (x y : ℝ) → x ≤ y → ¬ (y < x)
ℝ-less-than-or-equal-not-greater x y x≤y y<x = ∥∥-rec 𝟘-is-prop I y<x
 where
  I : ¬ (Σ q ꞉ ℚ , y < q < x)
  I (q , y<q , q<x) = ℚ<-not-itself-from-ℝ q y (x≤y q q<x , y<q)

ℝ-less-than-not-greater-or-equal : (x y : ℝ) → x < y → ¬ (y ≤ x)
ℝ-less-than-not-greater-or-equal x y l₁ l₂ = ℝ-less-than-or-equal-not-greater y x l₂ l₁

ℝ-not-less-is-greater-or-equal : (x y : ℝ) → ¬ (x < y) → y ≤ x
ℝ-not-less-is-greater-or-equal x y nl p pLy = ∥∥-rec (∈-is-prop (lower-cut-of x) p) I (rounded-left-b (lower-cut-of y) (rounded-from-real-L y) p pLy)
 where
  I : Σ q ꞉ ℚ , p < q < y → p < x
  I (q , l , q<y) = ∥∥-rec (∈-is-prop (lower-cut-of x) p) II (ℝ-locatedness x p q l)
   where
    II : p < x ∔ q > x → p < x
    II (inl p<x) = p<x
    II (inr x<q) = 𝟘-elim (nl ∣ q , (x<q , q<y) ∣)

ℝ≤-<-trans : (x y z : ℝ) → x ≤ y → y < z → x < z
ℝ≤-<-trans x y z x≤y y<z = ∥∥-functor I y<z
 where
  I : Σ q ꞉ ℚ , q > y × q < z
    → Σ q' ꞉ ℚ , q' > x × q' < z
  I (q , qRy , qLz) = q , ∥∥-rec (∈-is-prop (upper-cut-of x) q) III II , qLz
   where
    II : ∃ k ꞉ ℚ , k < q × k > y
    II = rounded-right-b (upper-cut-of y) (rounded-from-real-R y) q qRy

    III : Σ k ꞉ ℚ , k < q × k > y → q > x
    III (k , k<q , kRy) = ∥∥-rec (∈-is-prop (upper-cut-of x) q) IV (ℝ-locatedness x k q k<q)
     where
      IV : k < x ∔ q > x → q > x
      IV (inl kLx) = 𝟘-elim (ℚ<-irrefl k (disjoint-from-real y k k (x≤y k kLx , kRy)))
      IV (inr qRx) = qRx

<ℝ-irreflexive : (x : ℝ) → x ≮ x
<ℝ-irreflexive x l = ∥∥-rec 𝟘-is-prop I l
 where
  I : ¬ (Σ k ꞉ ℚ , x < k < x)
  I (k , x<k , k<x) = ℚ<-not-itself-from-ℝ k x (k<x , x<k)

ℝ-zero-less-than-one : 0ℝ < 1ℝ
ℝ-zero-less-than-one = ∣ 1/2 , 0<1/2 , 1/2<1 ∣

ℝ-zero-apart-from-one : 0ℝ ♯ 1ℝ
ℝ-zero-apart-from-one = ∣ inl ℝ-zero-less-than-one ∣

embedding-preserves-order : (p q : ℚ) → p < q → ι p < ι q
embedding-preserves-order p q l = I (use-rationals-density)
 where
  use-rationals-density : Σ k ꞉ ℚ , p < k < q
  use-rationals-density = ℚ-dense p q l

  I : (Σ k ꞉ ℚ , p < k < q) → ∃ k ꞉ ℚ , p < k < q
  I (k , p<k , k<q) = ∣ k , p<k , k<q ∣

\end{code}

Added by Martin Escardo 24th August 2023, adapted from Various.Dedekind.

\begin{code}

≤-ℝ-ℝ-antisym : (x y : ℝ) → x ≤ y → y ≤ x → x ＝ y
≤-ℝ-ℝ-antisym = ℝ-equality-from-left-cut'

♯-is-tight : (x y : ℝ) → ¬ (x ♯ y) → x ＝ y
♯-is-tight x y ν = ≤-ℝ-ℝ-antisym x y III IV
 where
  I : x ≮ y
  I ℓ = ν ∣ inl ℓ ∣

  II : y ≮ x
  II ℓ = ν ∣ inr ℓ ∣

  III : x ≤ y
  III = ℝ-not-less-is-greater-or-equal y x II

  IV : y ≤ x
  IV = ℝ-not-less-is-greater-or-equal x y I

ℝ-is-¬¬-separated : (x y : ℝ) → ¬¬ (x ＝ y) → x ＝ y
ℝ-is-¬¬-separated x y ϕ = ♯-is-tight x y (c ϕ)
 where
  c : ¬¬ (x ＝ y) → ¬ (x ♯ y)
  c = contrapositive (apartness-gives-inequality x y)

\end{code}

Added by Martin Escardo 31st August 2026.

\begin{code}

ℚ-to-ℝ-is-left-cancellable : left-cancellable (ι {{canonical-map-ℚ-to-ℝ}})
ℚ-to-ℝ-is-left-cancellable {p} {q} e = γ (ℚ-trichotomous p q)
 where
  γ : (p < q) ∔ (p ＝ q) ∔ (q < p) → p ＝ q
  γ (inl l)        = 𝟘-elim (<ℝ-irreflexive (ι q)
                              (transport (_< ι q) e
                                (embedding-preserves-order p q l)))
  γ (inr (inl e')) = e'
  γ (inr (inr l))  = 𝟘-elim (<ℝ-irreflexive (ι p)
                              (transport (_< ι p) (e ⁻¹)
                                (embedding-preserves-order q p l)))

ℚ-to-ℝ-is-embedding : is-embedding (ι {{canonical-map-ℚ-to-ℝ}})
ℚ-to-ℝ-is-embedding = lc-maps-into-sets-are-embeddings ι
                       ℚ-to-ℝ-is-left-cancellable
                       ℝ-is-set

\end{code}
