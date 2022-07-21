Andrew Sneap

In this file I prove that the rationals are an ordered field.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) --TypeTopology

open import Notation.Order --TypeTopology
open import UF.FunExt -- TypeTopology

open import DedekindReals.FieldAxioms
open import DedekindReals.Rationals
open import DedekindReals.RationalsAddition
open import DedekindReals.RationalsMultiplication
open import DedekindReals.RationalsNegation
open import DedekindReals.RationalsOrder

module DedekindReals.FieldRationals (fe : Fun-Ext) where

_#_ : (x y : ℚ) → 𝓤₀ ̇
x # y  = ¬ (x ＝ y)

0ℚ#1ℚ : 0ℚ # 1ℚ
0ℚ#1ℚ = ℚ-zero-not-one fe

RationalsField : Field-structure ℚ { 𝓤₀ }
RationalsField = (_+_ , _*_ , _#_) , (ℚ-is-set fe)
                                   , (ℚ+-assoc fe)
                                   , (ℚ*-assoc fe)
                                   , ℚ+-comm
                                   , ℚ*-comm
                                   , ℚ-distributivity fe
                                   , (0ℚ , 1ℚ) , 0ℚ#1ℚ
                                               , (ℚ-zero-left-neutral fe)
                                               , ℚ+-inverse fe
                                               , ℚ-mult-left-id fe
                                               , ℚ*-inverse fe

RationalsOrderedField : Ordered-field-structure { 𝓤₀ } { 𝓤₀ } { 𝓤₀ } ℚ RationalsField
RationalsOrderedField = _<_ , ℚ<-addition-preserves-order , ℚ<-pos-multiplication-preserves-order

RationalsOrderedField' : Ordered-Field 𝓤₀ { 𝓤₀ } { 𝓤₀ }
RationalsOrderedField' = (ℚ , RationalsField) , RationalsOrderedField

-- open import Matrices RationalsOrderedField'



