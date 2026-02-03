Anna Williams 3 February 2026

Definition of functor composition

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Wild
open import Categories.Functor
open import Categories.Notation.Wild
open import Categories.Notation.Functor

module Categories.Functor-Composition where

\end{code}

We now define functor composition in the expected way.

\begin{code}

_F∘_ : {A : WildCategory 𝓤 𝓥}
       {B : WildCategory 𝓦 𝓣}
       {C : WildCategory 𝓤' 𝓥'}
       (G' : Functor B C)
       (F' : Functor A B)
     → Functor A C
_F∘_ {_} {_} {_} {_} {_} {_} {A} {B} {C} G' F' = functor
 where
  open WildCategoryNotation A
  open WildCategoryNotation B
  open WildCategoryNotation C
  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  
  F₀ : obj A → obj C
  F₀ x = G (F x)

  F₁ : {a b : obj A} → hom a b → hom (F₀ a) (F₀ b)
  F₁ h = G (F h)

  id-eq : (a : obj A)
        → G (F 𝒊𝒅) ＝ 𝒊𝒅
  id-eq a = G (F 𝒊𝒅) ＝⟨ i  ⟩
            G 𝒊𝒅     ＝⟨ ii ⟩
            𝒊𝒅       ∎
   where
    i  = ap G (id-preserved a)
    ii = id-preserved (F a)

  f-distrib : {a b c : obj A}
              (g : hom b c)
              (f : hom a b)
            → G (F (g ○ f)) ＝ G (F g) ○ G (F f)
  f-distrib g f = G (F (g ○ f))     ＝⟨ i  ⟩
                  G (F g ○ F f)     ＝⟨ ii ⟩
                  G (F g) ○ G (F f) ∎
   where
    i  = ap G (distributivity g f)
    ii = distributivity (F g) (F f)

  functor : Functor A C
  functor = make-functor F₀ F₁ id-eq f-distrib

\end{code}
