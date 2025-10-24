Anna Williams, 17 October 2025

Definition of functor

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import Categories.Category

module Categories.Functor where

record Functor {𝓤 𝓥 𝓦 𝓨 : Universe} (A : Precategory 𝓤 𝓥) (B : Precategory 𝓦 𝓨)
 : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓨) ̇  where
 field
  Fobj : obj A → obj B
  Fhom : {a b : obj A} → hom {{A}} a b → hom {{B}} (Fobj a) (Fobj b)
  id-pres : (a : obj A) → Fhom (id {{A}} {a}) ＝ id {{B}} {Fobj a}
  distrib
   : {a b c : obj A}
     {f : hom {{A}} a b}
     {g : Precategory.hom A b c}
   → Fhom (_∘_ {{A}} g f) ＝ _∘_ {{B}} (Fhom g) (Fhom f)

open Functor {{...}}

\end{code}

We now define functor composition.

\begin{code}

_F∘_ : {𝓐 𝓑 𝓤 𝓥 𝓦 𝓨 : Universe} {{A : Precategory 𝓤 𝓥}} {{B : Precategory 𝓦 𝓨}} {{C : Precategory 𝓐 𝓑}} (G : Functor B C) (F : Functor A B) → Functor A C
_F∘_ {{A}} {{B}} {{C}} G F = record { Fobj = fobj ; Fhom = fhom ; id-pres = id-pres' ; distrib = distrib' }
 where
  fobj : obj A → obj C
  fobj x = Fobj {{G}} (Fobj {{F}} x)

  fhom : {a b : obj A} → hom {{A}} a b → hom {{C}} (fobj a) (fobj b)
  fhom h = Fhom {{G}} (Fhom {{F}} h)

  id-pres' : (a : obj A) → Fhom {{G}} (Fhom {{F}} (id {{A}})) ＝ id {{C}}
  id-pres' a = Fhom {{G}} (Fhom {{F}} (id {{A}})) ＝⟨ ap (Fhom {{G}}) (id-pres {{F}} a) ⟩
               Fhom {{G}} (id {{B}})              ＝⟨ id-pres {{G}} (Fobj {{F}} a) ⟩
              id {{C}}                            ∎

  distrib' : {a b c : obj A} {f : hom {{A}} a b} {g : hom {{A}} b c} →
      fhom (_∘_ {{A}} g f) ＝ _∘_ {{C}} (fhom g) (fhom f)
  distrib' {_} {_} {_} {f} {g} = fhom ((_∘_ {{A}} g) f)                              ＝⟨ ap (Fhom {{G}}) (distrib {{F}}) ⟩
                                 Fhom {{G}} (_∘_{{B}} (Fhom {{F}} g) (Fhom {{F}} f)) ＝⟨ distrib {{G}} ⟩
                                 _∘_{{C}} (fhom g) (fhom f)                          ∎
\end{code}
