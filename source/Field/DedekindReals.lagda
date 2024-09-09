Andrew Sneap, 7 February 2021

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}


open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons


module Field.DedekindReals
         (fe : Fun-Ext)
         (pt : propositional-truncations-exist)
         (pe : Prop-Ext)
 where


{-
DedekindRealsField : Field-structure ℝ { 𝓤₀ }
DedekindRealsField = ({!!} , {!!} , _♯_) , ℝ-is-set , {!!} , {!!} , {!!} , {!!} , {!!} , (0ℝ , 1ℝ) , ℝ-zero-apart-from-one , {!!} , {!!} , {!!} , {!!}

DedekindRealsOrderedField : Ordered-field-structure { 𝓤₁ } { 𝓤₀ } { 𝓤₀ } ℝ DedekindRealsField
DedekindRealsOrderedField = _<ℝ_ , {!!} , {!!}

DedekindRealsOrderedField' : Ordered-Field 𝓤₁ { 𝓤₀ } { 𝓤₀ }
DedekindRealsOrderedField' = (ℝ , DedekindRealsField) , DedekindRealsOrderedField

DedekindRealsArchimedeanOrderedField : ArchimedeanOrderedField 𝓤₁
DedekindRealsArchimedeanOrderedField = DedekindRealsOrderedField' , I
 where
  I : (f : ℚ → ℝ) → (x y : ℝ) → Σ z ꞉ ℚ , x < f z × f z < y
  I f x y = {!!}
-}


\end{code}
