

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import UF-PropTrunc --TypeTopology
open import UF-FunExt --TypeTopology
open import UF-Subsingletons --TypeTopology
open import OrderNotation --TypeTopology

open import FieldAxioms

module FieldDedekindReals
         (fe : Fun-Ext)
         (pt : propositional-truncations-exist)
         (pe : Prop-Ext)
 where

open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe

DedekindRealsField : Field-structure ℝ { 𝓤₀ }
DedekindRealsField = ({!!} , {!!} , _♯_) , ℝ-is-set , {!!} , {!!} , {!!} , {!!} , {!!} , (0ℝ , 1ℝ) , ℝ-zero-apart-from-one , {!!} , {!!} , {!!} , {!!}

DedekindRealsOrderedField : Ordered-field-structure { 𝓤₁ } { 𝓤₀ } { 𝓤₀ } ℝ DedekindRealsField
DedekindRealsOrderedField = _<ℝ_ , {!!} , {!!}

DedekindRealsOrderedField' : Ordered-Field 𝓤₁ { 𝓤₀ } { 𝓤₀ }
DedekindRealsOrderedField' = (ℝ , DedekindRealsField) , DedekindRealsOrderedField

{-
open import Rationals

DedekindRealsArchimedeanOrderedField : ArchimedeanOrderedField 𝓤₁
DedekindRealsArchimedeanOrderedField = DedekindRealsOrderedField' , I
 where
  I : (f : ℚ → ℝ) → (x y : ℝ) → Σ z ꞉ ℚ , x < f z × f z < y
  I f x y = {!!}
-}


\end{code}
