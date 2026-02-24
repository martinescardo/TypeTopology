Anna Williams 14 February 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Sets-Properties
open import UF.DependentEquality
open import Categories.Wild
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Total where

\end{code}

We can now define a total precategory. This is the category that pairs up the
objects of a 'base' precategory with the corresponding objects index by that
object in the displayed precategory. That is, the objects are of the form
Σ x : obj P , obj[ x ]. We similarly define the homomorphisms and other fields.

\begin{code}

TotalPrecategory : {𝓦 𝓨 : Universe}
                   {P : Precategory 𝓤 𝓥}
                   (D : DisplayedPrecategory 𝓦 𝓨 P)
                 → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalPrecategory {𝓤} {𝓥} {𝓦} {𝓨} {P} D = (total-wild-category
                                          , total-is-precategory)
 where
  open PrecategoryNotation P
  open DispPrecatNotation D

  total-wild-category : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  total-wild-category = wildcategory
                       (Σ p ꞉ obj P , obj[ p ])
                       (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                       (𝒊𝒅 , D-𝒊𝒅)
                       (λ (g , 𝕘) (f , 𝕗) → g ◦ f , 𝕘 ○ 𝕗)
                       (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-left-neutral f
                                            , Idtofun (dep-id _ _)
                                               (D-𝒊𝒅-is-left-neutral 𝕗)))
                       (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-right-neutral f
                                            , Idtofun (dep-id _ _)
                                               (D-𝒊𝒅-is-right-neutral 𝕗)))
                       (λ f g h → to-Σ-＝ (assoc _ _ _
                                          , Idtofun (dep-id _ _) D-assoc))
   where
    dep-id = dependent-Id-via-transport

  total-is-precategory : is-precategory total-wild-category
  total-is-precategory _ _ = Σ-is-set (hom-is-set P) (λ _ → hom[-]-is-set)

\end{code}

