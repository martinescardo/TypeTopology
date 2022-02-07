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
