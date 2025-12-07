Anna Williams, 17 October 2025

Definition of functor

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

module Categories.Functor where

open import Categories.Type

\end{code}

We define a functor from precategory A to precategory B as is usual.
This includes:
- Fobj, which is a map from objects of A to objects of B
- Fhom, which is a map from homomorphisms of A to homomorphisms of B

with the following structure
- Fhom (id A) = id (Fobj B)
- Fhom (g ∘ f) = (Fhom g) ∘ (Fhom f)

\begin{code}

record Functor (A : WildCategory 𝓤 𝓥) (B : WildCategory 𝓦 𝓣)
 : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ̇  where
 constructor make-functor
 open CategoryNotation A
 open CategoryNotation B
 field
  Fobj : obj A → obj B
  Fhom : {a b : obj A} → hom a b → hom (Fobj a) (Fobj b)
  id-pres : (a : obj A) → Fhom {a} id ＝ id
  distrib : {a b c : obj A}
          (g : hom b c)
          (f : hom a b)
        → Fhom (g ∘ f) ＝ (Fhom g) ∘ (Fhom f)

\end{code}

Functor Notation

\begin{code}

record MAP {𝓤 𝓥 : Universe} (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 field
  func : A → B

open MAP {{...}} public

record FunctorGen {A : WildCategory 𝓤 𝓥} {B : WildCategory 𝓦 𝓣}
                       (F : Functor A B) : 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇ where
 
 open CategoryNotation A
 open CategoryNotation B
 field 
  id-pres : (a : obj A) → Functor.Fhom F {a} id ＝ id
  distrib : {a b c : obj A}
            (g : hom b c)
            (f : hom a b)
          → Functor.Fhom F (g ∘ f)
          ＝ Functor.Fhom F g ∘ Functor.Fhom F f

open FunctorGen {{...}} public

module FunctorNotation {A : WildCategory 𝓤 𝓥} {B : WildCategory 𝓦 𝓣}
                       (F : Functor A B) where

 open CategoryNotation A
 open CategoryNotation B

 instance
  test : MAP (obj A) (obj B)
  func {{test}} = Functor.Fobj F

 instance
  test' : {a b : obj A} → MAP (hom a b) (hom (func a) (func b))
  func {{test'}} = Functor.Fhom F

 instance
  test'' : FunctorGen F
  id-pres {{test''}} = Functor.id-pres F
  distrib {{test''}} = Functor.distrib F

 functor-map = func

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
  
  fobj : obj A → obj C
  fobj x = G (F x)

  fhom : {a b : obj A} → hom a b → hom (fobj a) (fobj b)
  fhom h = G (F h)

  id-eq : (a : obj A)
        → G (F id) ＝ id
  id-eq a = G (F id) ＝⟨ i  ⟩
            G id     ＝⟨ ii ⟩
            id       ∎
   where
    i  = ap G (id-pres a)
    ii = id-pres (F a)

  f-distrib : {a b c : obj A}
              (g : hom b c)
              (f : hom a b)
            → G (F (g ∘ f)) ＝ G (F g) ∘ G (F f)
  f-distrib g f = G (F (g ∘ f))     ＝⟨ i  ⟩
                  G (F g ∘ F f)     ＝⟨ ii ⟩
                  G (F g) ∘ G (F f) ∎
   where
    i  = ap G (distrib g f)
    ii = distrib (F g) (F f)

  functor : Functor A C
  functor = make-functor fobj fhom id-eq f-distrib

\end{code}
