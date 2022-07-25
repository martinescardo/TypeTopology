

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import UF.PropTrunc 
open import UF.FunExt 
open import UF.Subsingletons 
open import Notation.Order 

open import DedekindReals.Field.Axioms

module DedekindReals.Field.DedekindReals
         (fe : Fun-Ext)
         (pt : propositional-truncations-exist)
         (pe : Prop-Ext)
 where

open import DedekindReals.Reals.Reals pe pt fe
open import DedekindReals.Reals.Order pe pt fe
{-
DedekindRealsField : Field-structure ℝ { 𝓤₀ }
DedekindRealsField = ({!!} , {!!} , _♯_) , ℝ-is-set , {!!} , {!!} , {!!} , {!!} , {!!} , (0ℝ , 1ℝ) , ℝ-zero-apart-from-one , {!!} , {!!} , {!!} , {!!}

DedekindRealsOrderedField : Ordered-field-structure { 𝓤₁ } { 𝓤₀ } { 𝓤₀ } ℝ DedekindRealsField
DedekindRealsOrderedField = _<ℝ_ , {!!} , {!!}

DedekindRealsOrderedField' : Ordered-Field 𝓤₁ { 𝓤₀ } { 𝓤₀ }
DedekindRealsOrderedField' = (ℝ , DedekindRealsField) , DedekindRealsOrderedField


open import DedekindReals.Rationals.

DedekindRealsArchimedeanOrderedField : ArchimedeanOrderedField 𝓤₁
DedekindRealsArchimedeanOrderedField = DedekindRealsOrderedField' , I
 where
  I : (f : ℚ → ℝ) → (x y : ℝ) → Σ z ꞉ ℚ , x < f z × f z < y
  I f x y = {!!}
-}


\end{code}
