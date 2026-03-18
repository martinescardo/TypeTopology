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


 id-eq : (a : obj A) → G (F 𝒊𝒅) ＝ 𝒊𝒅
 id-eq a = G (F 𝒊𝒅) ＝⟨ ap G (id-preserved a) ⟩
           G 𝒊𝒅     ＝⟨ id-preserved (F a) ⟩
           𝒊𝒅       ∎

 _F∘_ : Functor A C
 _F∘_ = combined-functor
  where
   F₀ : obj A → obj C
   F₀ a = G (F a)

   F₁ : {a b : obj A} → hom a b → hom (F₀ a) (F₀ b)
   F₁ f = G (F f)

   combined-functor : Functor A C
   combined-functor = functor F₀ F₁ id-eq f-distrib 

\end{code}

The identity functor is left and right neutral with repspect to the composition
operation.

\begin{code}

module _ {𝓤 𝓥 𝓦 𝓣 : Universe}
         {A : Precategory 𝓤 𝓥}
         {B : Precategory 𝓦 𝓣}
         (fe : Fun-Ext)
         (F' : Functor A B) where
 open PrecategoryNotation A
 open PrecategoryNotation B
 open FunctorNotation F' renaming (functor-map to F)

 id-left-neutral-F∘ : (id-functor B) F∘ F' ＝ F'
 id-left-neutral-F∘ = test
  where
   test : (id-functor B F∘ F') ＝ F'
   test = functor F F _ (f-distrib (id-functor B) F')            ＝⟨ I ⟩
          functor F F id-preserved (f-distrib (id-functor B) F') ＝⟨ II ⟩
          F'                                                     ∎

    where
     I = ap (λ - → functor F F - (f-distrib (id-functor B) F'))
            (dfunext fe (λ _ → hom-is-set B _ _))
     II = ap (functor F F id-preserved)
             (implicit-dfunext fe
              (λ _ → implicit-dfunext fe
               (λ _ → implicit-dfunext fe
                (λ _ → dfunext fe
                 (λ _ → dfunext fe
                  (λ _ → hom-is-set B _ _))))))

 id-right-neutral-F∘ : F' F∘ id-functor A ＝ F'
 id-right-neutral-F∘ = test
  where
  
   idFA = id-functor A

   test : (F' F∘ idFA) ＝ F'
   test = functor F F _ (f-distrib F' idFA)            ＝⟨ I ⟩
          functor F F id-preserved (f-distrib F' idFA) ＝⟨ II ⟩
          F'                                           ∎

    where
     I = ap (λ - → functor F F - (f-distrib F' idFA))
            (dfunext fe (λ _ → hom-is-set B _ _))
     II = ap (functor F F id-preserved)
             (implicit-dfunext fe
              (λ _ → implicit-dfunext fe
               (λ _ → implicit-dfunext fe
                (λ _ → dfunext fe
                 (λ _ → dfunext fe
                  (λ _ → hom-is-set B _ _))))))

\end{code}

The functor composition operation is associative.

\begin{code}

assoc-F∘ : {A : Precategory 𝓤 𝓥}
           {B : Precategory 𝓦 𝓣}
           {C : Precategory 𝓤' 𝓥'}
           {D : Precategory 𝓦' 𝓣'}
           (fe : Fun-Ext)
           (F : Functor A B)
           (G : Functor B C)
           (H : Functor C D)
         → H F∘ (G F∘ F) ＝ (H F∘ G) F∘ F
assoc-F∘ {_} {_} {_} {_} {_} {_} {_} {_} {A} {B} {C} {D} fe F G H
 = functor _ _ (id-eq H (G F∘ F)) (f-distrib H (G F∘ F)) ＝⟨ I ⟩
      functor _ _ (id-eq (H F∘ G) F) _                      ＝⟨ II ⟩
      functor _ _ _ _ ∎
 where
  I = ap (λ - → functor _ _ - (f-distrib H (G F∘ F)))
         (dfunext fe (λ x → hom-is-set D _ _))
  II = ap (functor _ _ _)
          (implicit-dfunext fe
           (λ _ → implicit-dfunext fe
            (λ _ → implicit-dfunext fe
             (λ _ → dfunext fe
              (λ _ → dfunext fe
               (λ _ → hom-is-set D _ _))))))

\end{code}
