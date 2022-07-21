Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation
open import UF-PropTrunc -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology

open import Rationals
open import RationalsOrder
open import RationalsMinMax

module DedekindRealsMultiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals pe pt fe
open PropositionalTruncation pt

_*_ : ℝ → ℝ → ℝ
_*_ ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)  = (L , {!!}) , {!!}
 where
  L : ℚ-subset-of-propositions
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < {!!}) , ∃-is-prop
  
