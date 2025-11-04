Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import Categories.Type
open import Categories.Functor

module Categories.NaturalTransformation where

\end{code}

Definition of a natural transformation in the usual way.
For two functors, F and G. We have:
- gamma : for every object in A, a homomorphism, hom (F a) (G a)
such that it is natural:
- for objects, f : hom a b, (G f) ∘ (gamma a) ＝ (gamma b) ∘ (F f)

\begin{code}

record NaturalTransformation {A : Precategory 𝓤 𝓥}
                             {B : Precategory 𝓦 𝓣}
                             (F G : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 field
  gamma : (a : obj A) → hom {{B}} (Functor.Fobj F a) (Functor.Fobj G a)
  natural : {a b : obj A}
            (f : hom {{A}} a b)
          → (Functor.Fhom G f) ∘[ B ] (gamma a)
          ＝ (gamma b) ∘[ B ] (Functor.Fhom F f)

\end{code}
