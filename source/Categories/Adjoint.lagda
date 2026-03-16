Anna Williams, 6 March 2026

Definition of adjoint.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import Notation.UnderlyingType

open import Categories.Pre
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.NaturalTransformation

open import Categories.Notation.Functor
open import Categories.Notation.NaturalTransformation

module Categories.Adjoint where

\end{code}

Blah

\begin{code}

record LeftAdjoint {A : Precategory 𝓤 𝓥} {B : Precategory 𝓦 𝓣} (F : Functor A B) (fe : Fun-Ext) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where
 field
  G : Functor B A
  unit : NaturalTransformation (id-functor A) (G F∘ F)
  counit : NaturalTransformation (F F∘ G) (id-functor B)

 private
  η = unit
  ε = counit

 private
  εF =  transport (NaturalTransformation ((F F∘ G) F∘ F)) (id-left-neutral-F∘ F fe) (ε · F)
  Fη = transport (NaturalTransformation F) (assoc-F∘ F G F fe) (transport (λ - → NaturalTransformation - (F F∘ (G F∘ F))) (id-right-neutral-F∘  F fe) (F ·' η))
  
 field
  first-axiom : εF N∘ Fη ＝ id-natural-transformation F

 private
  Gε = transport (NaturalTransformation (G F∘ (F F∘ G))) (id-right-neutral-F∘ G fe) (G ·' ε)
  ηG = transport (NaturalTransformation G) ((assoc-F∘ G F G fe)⁻¹) (transport (λ - → NaturalTransformation - ((G F∘ F) F∘ G)) (id-left-neutral-F∘ G fe) (η · G))

 field
  second-axiom : Gε N∘ ηG ＝ id-natural-transformation G

\end{code}
