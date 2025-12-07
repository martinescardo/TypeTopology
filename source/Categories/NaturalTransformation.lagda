Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

module Categories.NaturalTransformation where

open import Categories.Type
open import Categories.Functor

\end{code}

Definition of a natural transformation in the usual way.
For two functors, F and G. We have:
- gamma : for every object in A, a homomorphism, hom (F a) (G a)
such that it is natural:
- for objects, f : hom a b, (G f) ∘ (gamma a) ＝ (gamma b) ∘ (F f)

\begin{code}

record NaturalTransformation {A : WildCategory 𝓤 𝓥}
                             {B : WildCategory 𝓦 𝓣}
                             (F' G' : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 open CategoryNotation A
 open CategoryNotation B
 open FunctorNotation F' renaming (functor-map to F)
 open FunctorNotation G' renaming (functor-map to G)
 field
  gamma : (a : obj A) → hom (F a) (G a)
  natural : {a b : obj A}
            (f : hom a b)
          → G f ∘ gamma a ＝ gamma b ∘ F f

\end{code}
