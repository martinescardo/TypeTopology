Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Wild
open import Categories.Notation
open import Categories.Functor

module Categories.NaturalTransformation where


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

We now define some notation similar to that of Category Notation
and Functor Notation for natural transformations.

\begin{code}

record NatNotation {A : WildCategory 𝓤 𝓥}
                        {B : WildCategory 𝓦 𝓣}
                        {F' G' : Functor A B}
                        (μ : NaturalTransformation F' G')
                   : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 open CategoryNotation A
 open CategoryNotation B
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

open NatNotation {{...}} public

module NaturalTNotation {A : WildCategory 𝓤 𝓥}
                        {B : WildCategory 𝓦 𝓣}
                        {F' G' : Functor A B}
                        (μ : NaturalTransformation F' G') where
 open CategoryNotation A
 open CategoryNotation B
 open FunctorNotation F' renaming (functor-map to F ; fobj to Fobj)
 open FunctorNotation G' renaming (functor-map to G ; fobj to Gobj)

 instance
  nat-notation : NatNotation μ
  gamma {{nat-notation}} = NaturalTransformation.gamma μ
  natural {{nat-notation}} = NaturalTransformation.natural μ

\end{code}
