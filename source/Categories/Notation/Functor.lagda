Anna Williams 3 February 2026

Notation for working with functors.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Wild
open import Categories.Functor
open import Categories.Notation.Wild

module Categories.Notation.Functor where

\end{code}

We define some functor notation in the style of category notation. To
use this for some functor F, we write

`open FunctorNotation F renaming (functor-map to F')`

where F' is the name we want to use for the functor.

\begin{code}

record FUNCTORMAP {𝓤 𝓥 : Universe} (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 field
  gen-functor-map : A → B

open FUNCTORMAP {{...}} public

record FUNNOTATION {A : WildCategory 𝓤 𝓥}
                   {B : WildCategory 𝓦 𝓣}
                   (F : Functor A B)
                 : 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇ where
 
 open WildCategoryNotation A
 open WildCategoryNotation B
 field 
  id-preserved : (a : obj A) → Functor.F₁ F {a} 𝒊𝒅 ＝ 𝒊𝒅
  distributivity : {a b c : obj A}
                (g : hom b c)
                (f : hom a b)
              → Functor.F₁ F (g ○ f)
              ＝ Functor.F₁ F g ○ Functor.F₁ F f

open FUNNOTATION {{...}} public

module FunctorNotation {A : WildCategory 𝓤 𝓥}
                       {B : WildCategory 𝓦 𝓣}
                       (F : Functor A B) where

 open WildCategoryNotation A
 open WildCategoryNotation B

 functor-map = gen-functor-map

 instance
  fobj : FUNCTORMAP (obj A) (obj B)
  gen-functor-map {{fobj}} = Functor.F₀ F

 instance
  fhom : {a b : obj A}
       → FUNCTORMAP (hom a b) (hom (functor-map a) (functor-map b))
  gen-functor-map {{fhom}} = Functor.F₁ F

 instance
  functor-notation : FUNNOTATION F
  id-preserved {{functor-notation}} = Functor.id-preserved F
  distributivity {{functor-notation}} = Functor.distributivity F


\end{code}
