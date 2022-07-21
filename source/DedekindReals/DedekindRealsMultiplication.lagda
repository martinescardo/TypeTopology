Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) -- TypeTopology

open import Notation.Order
open import UF.PropTrunc -- TypeTopology
open import UF.Subsingletons --TypeTopology
open import UF.FunExt -- TypeTopology
open import UF.Powerset -- TypeTopology

open import DedekindReals.Rationals
open import DedekindReals.RationalsOrder
open import DedekindReals.RationalsMinMax

module DedekindReals.DedekindRealsMultiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals.DedekindReals pe pt fe
open PropositionalTruncation pt

_*_ : ℝ → ℝ → ℝ
_*_ ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)  = (L , {!!}) , {!!}
 where
  L : {!!}
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < {!!}) , ∃-is-prop
  
