Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import Categories.Category
open import Categories.Functor

module Categories.NaturalTransformation where

record NaturalTransformation
 {𝓤 𝓥 𝓦 𝓨 : Universe}
 {A : Precategory 𝓤 𝓥}
 {{B : Precategory 𝓦 𝓨}}
 (F G : Functor A B)
 : (𝓤 ⊔ 𝓥 ⊔ 𝓨) ̇  where
 field
  gamma : (a : obj A) → hom (Functor.Fobj F a) (Functor.Fobj G a)
  natural
   : (a b : obj A)
   → (f : hom {{A}} a b)
   → (Functor.Fhom G f) ∘ (gamma a) ＝ (gamma b) ∘ (Functor.Fhom F f)

\end{code}
