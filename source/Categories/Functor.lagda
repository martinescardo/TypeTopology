Anna Williams, 17 October 2025

Definition of functor

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import Categories.Type

module Categories.Functor where

\end{code}

We define a functor from precategory A to precategory B as is usual.
This includes:
- Fobj, which is a map from objects of A to objects of B
- Fhom, which is a map from homomorphisms of A to homomorphisms of B

with the following structure
- Fhom (id A) = id (Fobj B)
- Fhom (g ∘ f) = (Fhom g) ∘ (Fhom f)

\begin{code}

record Functor (A : Precategory 𝓤 𝓥) (B : Precategory 𝓦 𝓣)
 : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ̇  where
 field
  Fobj : obj A → obj B
  Fhom : {a b : obj A} → hom {{A}} a b → hom {{B}} (Fobj a) (Fobj b)
  id-pres : (a : obj A) → Fhom (id {{A}} {a}) ＝ id {{B}} {Fobj a}
  distrib : {a b c : obj A}
            (g : hom {{A}} b c)
            (f : hom {{A}} a b)
          → Fhom (g ∘[ A ] f) ＝ (Fhom g) ∘[ B ] (Fhom f)

open Functor {{...}} public

\end{code}

We now define functor composition in the expected way.

\begin{code}

_F∘_ : {A : Precategory 𝓤 𝓥}
       {B : Precategory 𝓦 𝓣}
       {C : Precategory 𝓤' 𝓥'}
       (G : Functor B C)
       (F : Functor A B)
     → Functor A C
_F∘_ {_} {_} {_} {_} {_} {_} {A} {B} {C} G F = record {
                                                Fobj = fobj ;
                                                Fhom = fhom ;
                                                id-pres = id-pres' ;
                                                distrib = distrib'
                                               }
 where
  fobj : obj A → obj C
  fobj x = Fobj {{G}} (Fobj {{F}} x)

  fhom : {a b : obj A} → hom {{A}} a b → hom {{C}} (fobj a) (fobj b)
  fhom h = Fhom {{G}} (Fhom {{F}} h)

  id-pres' : (a : obj A) → Fhom {{G}} (Fhom {{F}} (id {{A}})) ＝ id {{C}}
  id-pres' a = Fhom {{G}} (Fhom {{F}} (id {{A}})) ＝⟨ i ⟩
               Fhom {{G}} (id {{B}})              ＝⟨ ii ⟩
               id {{C}}                           ∎
   where
    i = ap (Fhom {{G}}) (id-pres {{F}} a)
    ii = id-pres {{G}} (Fobj {{F}} a)

  distrib' : {a b c : obj A}
             (g : hom {{A}} b c)
             (f : hom {{A}} a b)
           → fhom (g ∘[ A ] f) ＝ (fhom g) ∘[ C ] (fhom f)
  distrib' g f = fhom (g ∘[ A ] f)                             ＝⟨ i  ⟩
                 Fhom {{G}} (Fhom {{F}} g ∘[ B ] Fhom {{F}} f) ＝⟨ ii ⟩
                 (fhom g) ∘[ C ] (fhom f)                      ∎
   where
    i = ap (Fhom {{G}}) (distrib {{F}} g f)
    ii = distrib {{G}} (Fhom {{F}} g) (Fhom {{F}} f)

\end{code}
