Andrew Sneap

In this file I prove the the rationals are a Field.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import UF-FunExt

open import Rationals
open import RationalsAddition
open import RationalsNegation
open import RationalsMultiplication
open import RationalsOrder
open import FieldAxioms


ℚ-field-structure : field-structure ℚ { 𝓤₀ }
ℚ-field-structure = _+_ , _*_ , λ p q → ¬ (p ≡ q)

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

