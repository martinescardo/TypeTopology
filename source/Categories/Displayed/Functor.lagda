Anna Williams, 30 October 2025

Definition of a displayed functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality
open import Categories.Pre
open import Categories.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Functor
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Functor where

\end{code}

We define displayed functors analagously to functors, but analogously to 
displayed categories we work with some "base" functor. Using this functor, we
map between the base precategories which lie below the displayed precategories.

\begin{code}

record DisplayedFunctor {P : Precategory 𝓦 𝓣}
                        {P' : Precategory 𝓦' 𝓣'}
                        (F' : Functor ⟨ P ⟩ ⟨ P' ⟩)
                        (D : DisplayedPrecategory 𝓤 𝓥 P)
                        (D' : DisplayedPrecategory 𝓤' 𝓥' P')
                      : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') ̇  where
 open PrecategoryNotation P
 open FunctorNotation F' renaming (functor-map to F)
 open DispPrecatNotation D
 open DispPrecatNotation D'
 field
  F₀ : {p : obj P}
     → obj[ p ]
     → obj[ F p ]
  F₁ : {a b : obj P}
       {f : hom a b}
       {x : obj[ a ]}
       {y : obj[ b ]}
     → hom[ f ] x y
     → hom[ F f ] (F₀ x) (F₀ y)

  disp-id-preserved : {c : obj P}
                      {a : obj[ c ]}
                    → F₁ D-𝒊𝒅
                    ＝⟦ (λ - → hom[ - ] (F₀ a) (F₀ a)) , id-preserved c ⟧
                      D-𝒊𝒅
  disp-distrib : {a b c : obj P}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 {z : obj[ c ]}
                 {f : hom a b}
                 {g : hom b c}
                 {𝕗 : hom[ f ] x y}
                 {𝕘 : hom[ g ] y z}
               → F₁ (𝕘 ○ 𝕗)
               ＝⟦ (λ - → hom[ - ] _ _) , distributivity g f ⟧
                 F₁ 𝕘 ○ F₁ 𝕗

\end{code}
