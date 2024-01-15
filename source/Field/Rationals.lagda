Andrew Sneap, 7 February 2021

In this file I prove that the rationals are an ordered field.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import Field.Axioms
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order

module Field.Rationals where

_#_ : (x y : ℚ) → 𝓤₀ ̇
x # y  = ¬ (x ＝ y)

0ℚ#1ℚ : 0ℚ # 1ℚ
0ℚ#1ℚ = ℚ-zero-not-one

RationalsField : Field-structure ℚ { 𝓤₀ }
RationalsField = (_+_ , _*_ , _#_) , ℚ-is-set
                                   , ℚ+-assoc
                                   , ℚ*-assoc
                                   , ℚ+-comm
                                   , ℚ*-comm
                                   , ℚ-distributivity
                                   , (0ℚ , 1ℚ) , 0ℚ#1ℚ
                                               , ℚ-zero-left-neutral
                                               , ℚ+-inverse
                                               , ℚ-mult-left-id
                                               , ℚ*-inverse

RationalsOrderedField : Ordered-field-structure { 𝓤₀ } { 𝓤₀ } { 𝓤₀ } ℚ RationalsField
RationalsOrderedField = _<_ , ℚ<-addition-preserves-order , ℚ<-pos-multiplication-preserves-order

RationalsOrderedField' : Ordered-Field 𝓤₀ { 𝓤₀ } { 𝓤₀ }
RationalsOrderedField' = (ℚ , RationalsField) , RationalsOrderedField
