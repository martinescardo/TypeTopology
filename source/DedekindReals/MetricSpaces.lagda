Andrew Sneap

\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT renaming (_+_ to _∔_ ; * to ⋆)  -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology

module MetricSpaces
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where 

open import DedekindReals pt fe
open import DedekindRealsOrder pt fe
open PropositionalTruncation pt

\end{code}

I cannot complete the following axioms without additions of Reals.

\begin{code}
 
m1 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
m1 X d = (x y : X) → (0ℝ ≤ d x y) × (d x y ≡ 0ℝ ⇔ x ≡ y)

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → 𝓤₁ ⊔ 𝓤 ̇
m2 X d = (x y : X) → d x y ≡ d y x

m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (d : X → X → ℝ) → {!!}
m3 X d = {!x!}
