Andrew Sneap

In this file I prove the the rationals are a Field.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt

open import DedekindReals.Rationals
open import DedekindReals.RationalsAddition
open import DedekindReals.RationalsNegation
open import DedekindReals.RationalsMultiplication
open import DedekindReals.RationalsOrder
open import DedekindReals.FieldAxioms

module DedekindReals.RationalsField where

ℚ-field-structure : field-structure ℚ { 𝓤₀ }
ℚ-field-structure = _+_ , _*_ , λ p q → ¬ (p ＝ q)

ℚ-field : Fun-Ext → Field-structure ℚ { 𝓤₀ }
ℚ-field fe = ℚ-field-structure
           , ℚ-is-set fe
           , ℚ+-assoc fe
           , ℚ*-assoc fe
           , ℚ+-comm
           , ℚ*-comm
           , ℚ-distributivity fe
           , (0ℚ , 1ℚ) , ℚ-zero-not-one fe
                       , ℚ-zero-left-neutral fe
                       , ℚ+-inverse fe
                       , ℚ-mult-left-id fe
                       , ℚ*-inverse fe

