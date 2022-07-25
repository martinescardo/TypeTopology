Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import Notation.Order
open import UF.PropTrunc 
open import UF.Subsingletons 
open import UF.FunExt 
open import UF.Powerset 

open import DedekindReals.Rationals.Rationals
open import DedekindReals.Rationals.Order
open import DedekindReals.Rationals.MinMax

module DedekindReals.Reals.Multiplication
         (pe : Prop-Ext) 
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open import DedekindReals.Reals.Reals pe pt fe
open PropositionalTruncation pt

_*_ : ℝ → ℝ → ℝ
_*_ ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)  = (L , {!!}) , {!!}
 where
  L : {!!}
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < {!!}) , ∃-is-prop
  
