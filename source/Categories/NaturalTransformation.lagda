Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

module Categories.NaturalTransformation where

open import Categories.Type
open import Categories.Functor

\end{code}

The definition of a natural transformation is in the usual way.

For two functors, F and G. We have:
* gamma : for every object in A, a homomorphism, hom (F a) (G a), and
* a proof that this is natural: for objects, f : hom a b,
  G f ∘ gamma a ＝ gamma b ∘ F f

\begin{code}

record NaturalTransformation {A : WildCategory 𝓤 𝓥}
                             {B : WildCategory 𝓦 𝓣}
                             (F' G' : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 open CategoryNotation A
 open CategoryNotation B
 open FunctorNotation F' renaming (functor-map to F ; defn-fobj to fobj)
 open FunctorNotation G' renaming (functor-map to G)
 field
  gamma : (a : obj A) → hom (F {{fobj}} a) (G {{defn-fobj}} a)

 private
  γ = gamma

 field
  natural : {a b : obj A}
            (f : hom a b)
          → G f ∘ γ a ＝ γ b ∘ F f

\end{code}
