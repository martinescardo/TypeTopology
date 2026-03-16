Anna Williams 3 February 2026

Definition of functor composition

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Functor
open import Categories.Notation.Pre
open import Categories.Notation.Functor

module Categories.Functor-Composition where

\end{code}

We now define functor composition in the expected way.

\begin{code}

module _ {A : Precategory 𝓤 𝓥}
       {B : Precategory 𝓦 𝓣}
       {C : Precategory 𝓤' 𝓥'}
       (G' : Functor B C)
       (F' : Functor A B) where
 open PrecategoryNotation A
 open PrecategoryNotation B
 open PrecategoryNotation C
 open FunctorNotation F' renaming (functor-map to F)
 open FunctorNotation G' renaming (functor-map to G)
  
 f-distrib : {a b c : obj A}
             (g : hom b c)
             (f : hom a b)
           → G (F (g ◦ f)) ＝ G (F g) ◦ G (F f)
 f-distrib g f = G (F (g ◦ f))     ＝⟨ i  ⟩
                 G (F g ◦ F f)     ＝⟨ ii ⟩
                 G (F g) ◦ G (F f) ∎
  where
   i  = ap G (distributivity g f)
   ii = distributivity (F g) (F f)


 id-eq : (a : obj A)
       → G (F 𝒊𝒅) ＝ 𝒊𝒅
 id-eq a = G (F 𝒊𝒅) ＝⟨ i  ⟩
           G 𝒊𝒅     ＝⟨ ii ⟩
           𝒊𝒅       ∎
  where
   i  = ap G (id-preserved a)
   ii = id-preserved (F a)

_F∘_ : {A : Precategory 𝓤 𝓥}
       {B : Precategory 𝓦 𝓣}
       {C : Precategory 𝓤' 𝓥'}
       (G' : Functor B C)
       (F' : Functor A B)
     → Functor A C
_F∘_ {_} {_} {_} {_} {_} {_} {A} {B} {C} G' F' = combined-functor
 where
  open PrecategoryNotation A
  open PrecategoryNotation B
  open PrecategoryNotation C
  open FunctorNotation F' renaming (functor-map to F)
  open FunctorNotation G' renaming (functor-map to G)
  
  F₀ : obj A → obj C
  F₀ a = G (F a)

  F₁ : {a b : obj A} → hom a b → hom (F₀ a) (F₀ b)
  F₁ f = G (F f)

{-
  f-distrib : {a b c : obj A}
              (g : hom b c)
              (f : hom a b)
            → G (F (g ◦ f)) ＝ G (F g) ◦ G (F f)
  f-distrib g f = G (F (g ◦ f))     ＝⟨ i  ⟩
                  G (F g ◦ F f)     ＝⟨ ii ⟩
                  G (F g) ◦ G (F f) ∎
   where
    i  = ap G (distributivity g f)
    ii = distributivity (F g) (F f)
-}

  combined-functor : Functor A C
  combined-functor = functor F₀ F₁ (id-eq G' F') (f-distrib G' F')

\end{code}

Composition with the identity functor does nothing.

\begin{code}

id-left-neutral-F∘ : {A : Precategory 𝓤 𝓥}
                     {B : Precategory 𝓦 𝓣}
                     (F : Functor A B)
                     (fe : Fun-Ext)
                   → (id-functor B) F∘ F ＝ F
id-left-neutral-F∘ {_} {_} {_} {_} {A} {B} F' fe = test
 where
  open PrecategoryNotation A
  open PrecategoryNotation B
  open FunctorNotation F' renaming (functor-map to F)

  idFB = id-functor B

  test : (id-functor B F∘ F') ＝ F'
  test = functor F F _ (f-distrib idFB F')            ＝⟨ ap (λ - → functor F F - (f-distrib idFB F')) (dfunext fe (λ _ → hom-is-set B _ _)) ⟩
         functor F F id-preserved (f-distrib idFB F') ＝⟨ ap (functor F F id-preserved) I ⟩
         F'                             ∎

   where
    I = (implicit-dfunext fe (λ a → implicit-dfunext fe (λ b → implicit-dfunext fe (λ c → dfunext fe (λ g → dfunext fe (λ f → hom-is-set B _ _))))))

id-right-neutral-F∘ : {A : Precategory 𝓤 𝓥}
                      {B : Precategory 𝓦 𝓣}
                      (F : Functor A B)
                      (fe : Fun-Ext)
                    → F F∘ id-functor A ＝ F
id-right-neutral-F∘ {_} {_} {_} {_} {A} {B} F' fe = test
 where
  open PrecategoryNotation A
  open PrecategoryNotation B
  open FunctorNotation F' renaming (functor-map to F)

  idFA = id-functor A

  test : (F' F∘ idFA) ＝ F'
  test = functor F F _ (f-distrib F' idFA)            ＝⟨ ap (λ - → functor F F - (f-distrib F' idFA)) (dfunext fe (λ _ → hom-is-set B _ _)) ⟩
         functor F F id-preserved (f-distrib F' idFA) ＝⟨ ap (functor F F id-preserved) I ⟩
         F'                             ∎

   where
    I = (implicit-dfunext fe (λ a → implicit-dfunext fe (λ b → implicit-dfunext fe (λ c → dfunext fe (λ g → dfunext fe (λ f → hom-is-set B _ _))))))


assoc-F∘ : {A : Precategory 𝓤 𝓥}
           {B : Precategory 𝓦 𝓣}
           {C : Precategory 𝓤' 𝓥'}
           {D : Precategory 𝓦' 𝓣'}
           (F : Functor A B)
           (G : Functor B C)
           (H : Functor C D)
           (fe : Fun-Ext)
         → H F∘ (G F∘ F) ＝ (H F∘ G) F∘ F
assoc-F∘ {_} {_} {_} {_} {_} {_} {_} {_}
 {A} {B} {C} {D} F G H
 fe = functor _ _ (id-eq H (G F∘ F)) (f-distrib H (G F∘ F)) ＝⟨ ap (λ - → functor _ _ - (f-distrib H (G F∘ F))) I ⟩
      functor _ _ (id-eq (H F∘ G) F) _                      ＝⟨ ap (functor _ _ _) II ⟩
      functor _ _ _ _ ∎
 where
  I = dfunext fe (λ x → hom-is-set D _ _)
  II = implicit-dfunext fe (λ a → implicit-dfunext fe (λ b → implicit-dfunext fe (λ c → dfunext fe (λ g → dfunext fe (λ f → hom-is-set D _ _)))))

\end{code}
