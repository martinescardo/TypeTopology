Anna Williams, 17 October 2025

Definition of functor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Notation.Wild
open import Categories.Wild

module Categories.Functor where

\end{code}

We define a functor from wild category A to wild category B in the usual way.
This includes,

 * F₀, a map from obj A to obj B, and

 * F₁, a map from hom A to hom B.

With the following structure

 * id-preserved: F₀ id = id, and

 * distributivity: F₁ (g ∘ f) = F₁ g ∘ F₁ f.

\begin{code}

record Functor (A : WildCategory 𝓤 𝓥)
               (B : WildCategory 𝓦 𝓣)
             : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇  where
 constructor functor

 open WildCategoryNotation A
 open WildCategoryNotation B

 field
  F₀ : obj A → obj B

  F₁ : {a b : obj A} → hom a b → hom (F₀ a) (F₀ b)

  id-preserved : (a : obj A) → F₁ {a} 𝒊𝒅 ＝ 𝒊𝒅

  distributivity : {a b c : obj A}
                   (g : hom b c)
                   (f : hom a b)
                 → F₁ (g ○ f) ＝ F₁ g ○ F₁ f

\end{code}
