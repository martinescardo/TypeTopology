Anna Williams 3 February 2026

Notation for working with natural transformations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import Categories.Wild
open import Categories.NaturalTransformation
open import Categories.Functor
open import Categories.Notation.Wild
open import Categories.Notation.Functor

module Categories.Notation.NaturalTransformation where

\end{code}

We now define some notation similar to that of Category Notation
and Functor Notation for natural transformations.

\begin{code}

record NatNotation {A : WildCategory 𝓤 𝓥}
                   {B : WildCategory 𝓦 𝓣}
                   {F' G' : Functor A B}
                   (μ : NaturalTransformation F' G')
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

open NatNotation {{...}} public

module NaturalTNotation {A : WildCategory 𝓤 𝓥}
                        {B : WildCategory 𝓦 𝓣}
                        {F' G' : Functor A B}
                        (μ : NaturalTransformation F' G') where
 open WildCategoryNotation A
 open WildCategoryNotation B
 open FunctorNotation F' renaming (functor-map to F ; fobj to Fobj)
 open FunctorNotation G' renaming (functor-map to G ; fobj to Gobj)

 instance
  nat-notation : NatNotation μ
  gamma {{nat-notation}} = NaturalTransformation.gamma μ
  natural {{nat-notation}} = NaturalTransformation.natural μ

\end{code}
