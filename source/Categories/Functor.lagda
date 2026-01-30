Anna Williams, 17 October 2025

Definition of functor

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Notation
open import Categories.Wild

module Categories.Functor where

\end{code}

We define a functor from precategory A to precategory B as is usual. This
includes,
* Fobj, a map from objects of A to objects of B, and
* Fhom, a map from homomorphisms of A to homomorphisms of B.

With the following structure
* Fhom id = id, and
* Fhom (g ∘ f) = Fhom g ∘ Fhom f.

\begin{code}

record Functor (A : WildCategory 𝓤 𝓥) (B : WildCategory 𝓦 𝓣)
 : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ̇  where
 constructor make-functor
 open CategoryNotation A
 open CategoryNotation B
 field
  Fobj : obj A → obj B
  Fhom : {a b : obj A} → hom a b → hom (Fobj a) (Fobj b)
  id-preserved : (a : obj A) → Fhom {a} id ＝ id
  distributes : {a b c : obj A}
                (g : hom b c)
                (f : hom a b)
              → Fhom (g ○ f) ＝ (Fhom g) ○ (Fhom f)

\end{code}

We define some functor notation in the style of category notation. To
use this for some functor F, we write
"open FunctorNotation F renaming (functor-map to F')" where F' is the name
we want to use for the functor.

\begin{code}

record FUNCTORMAP {𝓤 𝓥 : Universe} (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 field
  gen-functor-map : A → B

open FUNCTORMAP {{...}} public

record FUNNOTATION {A : WildCategory 𝓤 𝓥} {B : WildCategory 𝓦 𝓣}
                       (F : Functor A B) : 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇ where
 
 open CategoryNotation A
 open CategoryNotation B
 field 
  id-preserved : (a : obj A) → Functor.Fhom F {a} id ＝ id
  distributes : {a b c : obj A}
                (g : hom b c)
                (f : hom a b)
              → Functor.Fhom F (g ○ f)
              ＝ Functor.Fhom F g ○ Functor.Fhom F f

open FUNNOTATION {{...}} public

module FunctorNotation {A : WildCategory 𝓤 𝓥} {B : WildCategory 𝓦 𝓣}
                       (F : Functor A B) where

 open CategoryNotation A
 open CategoryNotation B

 functor-map = gen-functor-map

 instance
  fobj : FUNCTORMAP (obj A) (obj B)
  gen-functor-map {{fobj}} = Functor.Fobj F

 instance
  fhom : {a b : obj A}
       → FUNCTORMAP (hom a b) (hom (functor-map a) (functor-map b))
  gen-functor-map {{fhom}} = Functor.Fhom F

 instance
  functor-notation : FUNNOTATION F
  id-preserved {{functor-notation}} = Functor.id-preserved F
  distributes {{functor-notation}} = Functor.distributes F


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
  open CategoryNotation A
  open CategoryNotation B
  open CategoryNotation C
  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  
  Fobj : obj A → obj C
  Fobj x = G (F x)

  Fhom : {a b : obj A} → hom a b → hom (Fobj a) (Fobj b)
  Fhom h = G (F h)

  id-eq : (a : obj A)
        → G (F id) ＝ id
  id-eq a = G (F id) ＝⟨ i  ⟩
            G id     ＝⟨ ii ⟩
            id       ∎
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
    i  = ap G (distributes g f)
    ii = distributes (F g) (F f)

  functor : Functor A C
  functor = make-functor Fobj Fhom id-eq f-distrib

\end{code}
