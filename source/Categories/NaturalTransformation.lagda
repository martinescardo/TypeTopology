Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import Categories.Type
open import Categories.Functor

module Categories.NaturalTransformation where

record NaturalTransformation {A : Precategory 𝓤 𝓥}
                             {B : Precategory 𝓦 𝓣}
                             (F G : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 field
  gamma : (a : obj A) → hom {{B}} (Functor.Fobj F a) (Functor.Fobj G a)
  natural : (a b : obj A)
            (f : hom {{A}} a b)
          → _∘_ {{B}} (Functor.Fhom G f) (gamma a)
          ＝ _∘_ {{B}} (gamma b) (Functor.Fhom F f)

\end{code}
