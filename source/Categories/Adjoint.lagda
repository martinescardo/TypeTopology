Anna Williams, 6 March 2026

Definition of adjoint.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import Categories.Wild
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.NaturalTransformation

open import Categories.Notation.Functor
open import Categories.Notation.NaturalTransformation

module Categories.Adjoint where

\end{code}

Blah

\begin{code}

record LeftAdjoint {A : WildCategory 𝓤 𝓥} {B : WildCategory 𝓦 𝓣} (F : Functor A B) : {!!} where
 field
  G : Functor B A
  unit : NaturalTransformation (id-functor A) (G F∘ F)
  counit : NaturalTransformation (F F∘ G) (id-functor B)

 private
  η = unit
  ε = counit
  
 field
  first-axiom : ({!ε · F!} N∘ {!F ·' η!}) ＝ id-natural-transformation F
  second-axiom : {!(G ·' ε)!} N∘ {!(η · G)!} ＝ id-natural-transformation G

\end{code}
