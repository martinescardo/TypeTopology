Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology
open import UF-Base -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Subsingletons -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import OrderNotation


open import UF-Powerset
open import DedekindRealsProperties
open import Rationals
open import RationalsAddition renaming (_+_ to _ℚ+_)
open import RationalsNegation
open import RationalsOrder 

module DedekindRealsAddition
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 

open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe
open PropositionalTruncation pt

_+_ : ℝ → ℝ → ℝ
((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) + ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) =
 (L-z , R-z) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
 where
  L-z R-z : ℚ-subset-of-propositions
  L-z p = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ≡ r ℚ+ s)) , ∃-is-prop
  R-z q = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ≡ r ℚ+ s)) , ∃-is-prop
  
  inhabited-left-z : ∃ q ꞉ ℚ , q ∈ L-z
  inhabited-left-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-left-x inhabited-left-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ L-x) × (Σ q ꞉ ℚ , q ∈ L-y) → ∃ z ꞉ ℚ , z ∈ L-z
    δ ((p , l-x) , q , l-y) = ∣ (p ℚ+ q) , (∣ (p , q) , l-x , l-y , refl ∣) ∣

  inhabited-right-z : ∃ q ꞉ ℚ , q ∈ R-z
  inhabited-right-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-right-x inhabited-right-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ R-x) × (Σ q ꞉ ℚ , q ∈ R-y) → ∃ z ꞉ ℚ , z ∈ R-z
    δ ((p , r-x) , q , r-y) = ∣ (p ℚ+ q) , (∣ (p , q) , (r-x , r-y , refl) ∣) ∣
    
  rounded-left-z : (z : ℚ) → (z ∈ L-z ⇔ (∃ t ꞉ ℚ , (z < t) × t ∈ L-z))
  rounded-left-z z = I , II
   where
    I : z ∈ L-z → ∃ t ꞉ ℚ , (z < t) × t ∈ L-z
    I zLz = ∣ {!!} , {!!} ∣
    II : ∃ t ꞉ ℚ , (z < t) × t ∈ L-z → z ∈ L-z
    II = {!!}
               
  rounded-right-z : (z : ℚ) → (z ∈ R-z) ⇔ (∃ q ꞉ ℚ , ((q < z) × (q ∈ R-z)))
  rounded-right-z z = {!!}
          
  disjoint-z : disjoint L-z R-z
  disjoint-z = {!!}
  located-z : located L-z R-z
  located-z = {!!}

ℝ+-comm : (x y : ℝ) → x + y ≡ y + x
ℝ+-comm ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) = ℝ-equality-from-left-cut' (x + y) (y + x) I II
 where
  x = ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
  y = ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)

  I : lower-cut-of (x + y) ⊆ lower-cut-of (y + x)
  I z f = ∥∥-functor α f
   where
    α : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (z ≡ r ℚ+ s) → Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-y × s ∈ L-x × (z ≡ r ℚ+ s)
    α ((r , s) , rLx , sLy , e) = (s , r) , (sLy , rLx , (e ∙ ℚ+-comm r s))
  II : lower-cut-of (y + x) ⊆ lower-cut-of (x + y)
  II z f = ∥∥-functor α f
   where
    α : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-y × s ∈ L-x × (z ≡ r ℚ+ s) → Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (z ≡ r ℚ+ s)
    α ((r , s) , rLy , sLx , e) = (s , r) , (sLx , rLy , (e ∙ ℚ+-comm r s))
