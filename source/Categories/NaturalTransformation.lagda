Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Wild
open import Categories.Notation.Wild
open import Categories.Notation.Functor
open import Categories.Functor

module Categories.NaturalTransformation where

\end{code}

The definition of a natural transformation is in the usual way.

For two functors, F : A → B and G : A → B. We have:

 * gamma : for every object, a : obj, there exists γ : hom (F a) (G a), and

 * a proof of naturality: for objects, a b : obj A, and homomorphism, f : hom a b,
   we have that G f ∘ gamma a ＝ gamma b ∘ F f.

\begin{code}

record NaturalTransformation {A : WildCategory 𝓤 𝓥}
                             {B : WildCategory 𝓦 𝓣}
                             (F' G' : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 open WildCategoryNotation A
 open WildCategoryNotation B

 open FunctorNotation F' renaming (functor-map to F ; fobj to Fobj)
 open FunctorNotation G' renaming (functor-map to G ; fobj to Gobj)

 field
  gamma : (a : obj A) → hom (F {{Fobj}} a) (G {{Gobj}} a)

 private
  γ = gamma

 field
  natural : {a b : obj A}
            (f : hom a b)
          → G f ○ γ a ＝ γ b ○ F f

\end{code}
