Anna Williams, 6 March 2026

Definition of adjoint.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt

open import Categories.Pre
open import Categories.Functor
open import Categories.Functor-Composition
open import Categories.NaturalTransformation


module Categories.Adjoint where

\end{code}

A functor F : A → B is left adjoint [1], if there exists
 - a functor G : B → A,
 - a natural transformation η : id A → GF, the unit, and
 - a natual transformation ε : FG → id B, the counit.

Such that

 - (εF)(Fη) = id F, and
 - (Gε)(ηG) = id G.

[1] The Univalent Foundations Program (2013), Homotopy Type Theory: Univalent
Foundations of Mathematics. Institute for Advanced Study:
https://homotopytypetheory.org/book.

\begin{code}

record LeftAdjoint {A : Precategory 𝓤 𝓥}
                   {B : Precategory 𝓦 𝓣}
                   (F : Functor A B)
                   (fe : Fun-Ext) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ where
 field
  G : Functor B A
  unit : NaturalTransformation (id-functor A) (G F∘ F)
  counit : NaturalTransformation (F F∘ G) (id-functor B)

 private
  η = unit
  ε = counit

 private
  εF =  transport (NaturalTransformation ((F F∘ G) F∘ F))
                  (id-left-neutral-F∘ fe F)
                  (ε · F)

  Fη = transport (NaturalTransformation F)
                 (assoc-F∘ fe F G F)
                 (transport (λ - → NaturalTransformation - (F F∘ (G F∘ F)))
                            (id-right-neutral-F∘ fe F)
                            (F ·' η))

  Gε = transport (NaturalTransformation (G F∘ (F F∘ G)))
                 (id-right-neutral-F∘ fe G)
                 (G ·' ε)

  ηG = transport (NaturalTransformation G)
                 ((assoc-F∘ fe G F G)⁻¹)
                 (transport (λ - → NaturalTransformation - ((G F∘ F) F∘ G))
                            (id-left-neutral-F∘ fe G)
                            (η · G))

 field
  first-axiom : εF N∘ Fη ＝ id-natural-transformation F
  second-axiom : Gε N∘ ηG ＝ id-natural-transformation G

\end{code}
