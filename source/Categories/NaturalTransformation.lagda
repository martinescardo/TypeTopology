Anna Williams, 17 October 2025

Definition of natural transformation

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Notation.Functor
open import Categories.Functor
open import Categories.Functor-Composition

module Categories.NaturalTransformation where

\end{code}

The definition of a natural transformation is in the usual way.

For two functors, F : A → B and G : A → B. We have:

 * gamma : for every object, a : obj, there exists γ : hom (F a) (G a), and

 * a proof of naturality: for objects, a b : obj A, and homomorphism, f : hom a b,
   we have that G f ∘ gamma a ＝ gamma b ∘ F f.

\begin{code}

record NaturalTransformation {A : Precategory 𝓤 𝓥}
                             {B : Precategory 𝓦 𝓣}
                             (F' G' : Functor A B)
                           : (𝓤 ⊔ 𝓥 ⊔ 𝓣) ̇  where
 open PrecategoryNotation A
 open PrecategoryNotation B

 open FunctorNotation F' renaming (functor-map to F ; fobj to Fobj)
 open FunctorNotation G' renaming (functor-map to G ; fobj to Gobj)

 field
  transf : (a : obj A) → hom (F {{Fobj}} a) (G {{Gobj}} a)

 private
  γ = transf

 field
  natural : {a b : obj A}
            (f : hom a b)
          → G f ◦ γ a ＝ γ b ◦ F f

\end{code}

Identity natural transformation

\begin{code}

id-natural-transformation : {A : Precategory 𝓤 𝓥} {B : Precategory 𝓦 𝓣} (F : Functor A B) → NaturalTransformation F F
id-natural-transformation {_} {_} {_} {_} {A} {B} F' = record { transf = λ _ → 𝒊𝒅 ; natural = inter }
 where
  open PrecategoryNotation A
  open PrecategoryNotation B
  open FunctorNotation F' renaming (functor-map to F)

  inter : {a b : obj A} (f : hom a b) → (F f) ◦ 𝒊𝒅 ＝ 𝒊𝒅 ◦ F f
  inter f = (F f) ◦ 𝒊𝒅 ＝⟨ 𝒊𝒅-is-right-neutral (F f) ⟩
            F f       ＝⟨ (𝒊𝒅-is-left-neutral (F f))⁻¹ ⟩
            𝒊𝒅 ◦ F f   ∎

\end{code}

Natural transformation thingy

\begin{code}

_·_ : {A : Precategory 𝓤 𝓥}
      {B : Precategory 𝓦 𝓣}
      {C : Precategory 𝓤' 𝓥'}
      {G H : Functor B C}
    → NaturalTransformation G H
    → (F : Functor A B)
    → NaturalTransformation (G F∘ F) (H F∘ F)
_·_ {_} {_} {_} {_} {_} {_} {A} {B} {C} {G'} {H'}
    N F' = record { transf = μ ∘ F
                  ; natural = nat-condition }
 where
  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  open FunctorNotation H' renaming (functor-map to H)
  open PrecategoryNotation A
  open PrecategoryNotation C

  μ = NaturalTransformation.transf N
  naturality = NaturalTransformation.natural N 

  nat-condition : {a b : obj A}
                  (f : hom a b)
                → H (F f) ◦ μ (F a) ＝ μ (F b) ◦ G (F f)
  nat-condition f = naturality (F f)


_·'_ : {A : Precategory 𝓤 𝓥}
      {B : Precategory 𝓦 𝓣}
      {C : Precategory 𝓤' 𝓥'}
      {G H : Functor A B}
    → (F : Functor B C)
    → NaturalTransformation G H
    → NaturalTransformation (F F∘ G) (F F∘ H)
_·'_ {_} {_} {_} {_} {_} {_} {A} {B} {C} {G'} {H'}
    F' N = record { transf = λ a → F (μ a) 
                  ; natural = nat-condition }
 where
  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  open FunctorNotation H' renaming (functor-map to H)
  open PrecategoryNotation A
  open PrecategoryNotation B
  open PrecategoryNotation C

  μ = NaturalTransformation.transf N
  naturality = NaturalTransformation.natural N 

  nat-condition : {a b : obj A}
                  (f : hom a b)
                → F (H f) ◦ F (μ a) ＝ F (μ b) ◦ F (G f)
  nat-condition {a} {b} f = F (H f) ◦ F (μ a) ＝⟨ (distributivity (H f) (μ a))⁻¹ ⟩
                            F (H f ◦ μ a)     ＝⟨ ap F (naturality f) ⟩
                            F (μ b ◦ G f)     ＝⟨ distributivity (μ b) (G f) ⟩
                            F (μ b) ◦ F (G f) ∎

\end{code}

Composition

\begin{code}

_N∘_ : {A : Precategory 𝓤 𝓥}
       {B : Precategory 𝓦 𝓣}
     → {F G H : Functor A B}
     → NaturalTransformation G H
     → NaturalTransformation F G
     → NaturalTransformation F H
_N∘_ {_} {_} {_} {_} {A} {B} {F'} {G'} {H'}
     N M = record { transf = λ a → (μ a) ◦ (ε a)
                  ; natural = naturality }
 where
  open PrecategoryNotation A
  open PrecategoryNotation B

  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  open FunctorNotation H' renaming (functor-map to H)

  μ = NaturalTransformation.transf N
  ε = NaturalTransformation.transf M

  natμ = NaturalTransformation.natural N
  natε = NaturalTransformation.natural M

  naturality : {a b : obj A}
               (f : hom a b)
             → H f ◦ (μ a ◦ ε a) ＝ (μ b ◦ ε b) ◦ F f
  naturality {a} {b} f = H f ◦ (μ a ◦ ε a) ＝⟨ assoc _ _ _ ⟩
                         (H f ◦ μ a) ◦ ε a ＝⟨ ap (_◦ ε a) (natμ f) ⟩
                         (μ b ◦ G f) ◦ ε a ＝⟨ (assoc _ _ _)⁻¹ ⟩
                         μ b ◦ (G f ◦ ε a) ＝⟨ ap (μ b ◦_) (natε f) ⟩
                         μ b ◦ (ε b ◦ F f) ＝⟨ assoc _ _ _ ⟩
                         (μ b ◦ ε b) ◦ F f ∎

\end{code}
