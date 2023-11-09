Jon Sterling and Mike Shulman, September 2023.

\begin{code}
{-# OPTIONS --safe --without-K #-}

module WildCategories.Base where

open import MLTT.Spartan
open import UF.Subsingletons

record WildCategory 𝓤 𝓥 : (𝓤 ⊔ 𝓥)⁺ ̇ where
 field
  ob : 𝓤 ̇
  hom : ob → ob → 𝓥 ̇
  idn : (x : ob) → hom x x
  _<<_ : {x y z : ob} (g : hom y z) (f : hom x y) → hom x z
  assoc
   : {u v w x : ob} (f : hom u v) (g : hom v w) (h : hom w x)
   → h << (g << f) ＝ (h << g) << f
  lunit
   : {x y : ob} (f : hom x y)
   → f << idn x ＝ f
  runit
   : {x y : ob} (f : hom x y)
   → idn y << f ＝ f

module _ {𝓤 𝓥} (C : WildCategory 𝓤 𝓥) where
 open WildCategory C

 is-initial-object : ob → 𝓤 ⊔ 𝓥 ̇
 is-initial-object I = (x : ob) → is-singleton (hom I x)

 has-initial-object : 𝓤 ⊔ 𝓥 ̇
 has-initial-object = Σ is-initial-object

\end{code}
