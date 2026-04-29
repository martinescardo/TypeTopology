Anna Williams, March 2026

This file corresponds to the paper

https://anna-maths.xyz/assets/papers/disp-categories.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Examples.Set
open import Categories.Examples.Magma

open import Categories.Functor
open import Categories.Functor-Composition

open import Categories.NaturalTransformation

open import Categories.Adjoint

open import Categories.Notation.Pre

open import Categories.Displayed.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Examples.Magma

open import Categories.Displayed.Functor

open import Categories.Displayed.Total

open import Categories.Displayed.Notation.Pre

module Categories.AW-MSciProject where

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.DependentEquality
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Univalence

\end{code}

## Chapter 3: Category Theory

### Section 3.1: Categories

\begin{code}

Definition-3-1 : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Definition-3-1 = WildCategory

Example-3-2 : WildCategory (𝓤 ⁺) 𝓤
Example-3-2 = SetWildCategory

Example-3-3 : Fun-Ext → WildCategory (𝓤 ⁺) 𝓤
Example-3-3 = MagmaWildCategory

Definition-3-4 : (W : WildCategory 𝓤 𝓥)
               → (A B : obj W)
               → 𝓥 ̇
Definition-3-4 W A B = A ≅ B
 where
  open WildCategoryNotation W

module _ (W : WildCategory 𝓤 𝓥) where
 open WildCategoryNotation W

 Proposition-3-5 : (A B : obj W)
                 → (f : A ≅ B)
                 → (g h : inverse ⌜ f ⌝)
                 → pr₁ g ＝ pr₁ h
 Proposition-3-5 _ _ _ = at-most-one-inverse

Definition-3-6 : (W : WildCategory 𝓤 𝓥)
                 (p : is-precategory W)
               → Precategory 𝓤 𝓥
Definition-3-6 W p = W , p

Proposition-3-7 : (W : WildCategory 𝓤 𝓥)
                → Fun-Ext
                → is-prop (is-precategory W)
Proposition-3-7 = being-precat-is-prop

Example-3-8-Set : Fun-Ext → Precategory (𝓤 ⁺) 𝓤
Example-3-8-Set = SetPrecategory

Example-3-8-Magma : Fun-Ext → Precategory (𝓤 ⁺) 𝓤
Example-3-8-Magma = MagmaPrecategory

module _ (P : Precategory 𝓤 𝓥) where
 open PrecategoryNotation P
 
 Proposition-3-9-prop : {a b : obj P}
                        (f : hom a b)
                      → is-prop (inverse f)
 Proposition-3-9-prop = being-iso-is-prop P

 Proposition-3-9-set : {a b : obj P}
                     → is-set (a ≅ b)
 Proposition-3-9-set = isomorphism-type-is-set P

 Corollary-3-10 : {a b : obj P}
                  {f f' : a ≅ b}
                → ⌜ f ⌝ ＝ ⌜ f' ⌝
                → f ＝ f'
 Corollary-3-10 = to-≅-＝

 Proposition-3-11 : (a b : obj P)
                  → (a ＝ b → a ≅ b)
 Proposition-3-11 a b = id-to-iso a b

Definition-3-12 : (P : Precategory 𝓤 𝓥)
                  (p : is-category P)
                → Category 𝓤 𝓥
Definition-3-12 P p = P , p

Corollary-3-13 : (C : Category 𝓤 𝓥)
               → ((a b : obj C) → is-set (a ＝ b))
Corollary-3-13 = cat-objs-form-a-1-type

Example-3-15 : is-univalent 𝓤
             → Fun-Ext
             → Category (𝓤 ⁺) 𝓤
Example-3-15 = SetCategory

Example-3-16 : Fun-Ext
             → is-univalent 𝓤
             → Category (𝓤 ⁺) 𝓤
Example-3-16 = MagmaCategory

\end{code}

### Functors

\begin{code}

Definition-3-17 : (P : Precategory 𝓤 𝓥)
                  (Q : Precategory 𝓦 𝓣)
                → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
Definition-3-17 P Q = Functor P Q

Example-3-19 : (P : Precategory 𝓤 𝓥)
             → Functor P P
Example-3-19 P = id-functor P

module _ {A : Precategory 𝓤 𝓥}
         {B : Precategory 𝓤' 𝓥'}
         {C : Precategory 𝓦 𝓣}
         {D : Precategory 𝓦' 𝓣'} where

 Definition-3-20 : (G : Functor B C)
                   (F : Functor A B)
                 → Functor A C
 Definition-3-20 G F = G F∘ F

 Proposition-3-21-left : Fun-Ext
                       → (F : Functor A B)
                       → F F∘ (id-functor A) ＝ F
 Proposition-3-21-left = id-left-neutral-F∘

 Proposition-3-21-right : Fun-Ext
                        → (F : Functor A B)
                        → (id-functor B) F∘ F ＝ F
 Proposition-3-21-right = id-right-neutral-F∘

 Proposition-3-22 : Fun-Ext
                  → (F : Functor A B)
                    (G : Functor B C)
                    (H : Functor C D)
                  → H F∘ (G F∘ F) ＝ (H F∘ G) F∘ F
 Proposition-3-22 = assoc-F∘

\end{code}

### Section 3.3: Natural Transformations

\begin{code}

module _ {A : Precategory 𝓤 𝓥}
         {B : Precategory 𝓦 𝓣}
         {C : Precategory 𝓤' 𝓥'}
         where

 Definition-3-23 : (F G : Functor A B)
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 Definition-3-23 F G = NaturalTransformation F G

 Example-3-25 : (F : Functor A B)
              → NaturalTransformation F F
 Example-3-25 F = id-natural-transformation F

 Definition-3-26 : {G H : Functor B C}
                   (μ : NaturalTransformation G H)
                   (F : Functor A B)
                 → NaturalTransformation (G F∘ F) (H F∘ F)
 Definition-3-26 = _·_

 Definition-3-27 : {F G H : Functor A B}
                   (γ : NaturalTransformation G H)
                   (μ : NaturalTransformation F G)
                 → NaturalTransformation F H
 Definition-3-27 = _N∘_

\end{code}

### Section 3.4: Adjoints

\begin{code}

 Definition-3-28 : (F : Functor A B)
                 → Fun-Ext
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 Definition-3-28 F = LeftAdjoint F

\end{code}

## Chapter 4: Displayed Category Theory

### Section 4.1: Displayed Categories

\begin{code}

Definition-4-1 : (𝓦 𝓣 : Universe)
                 (P : Precategory 𝓤 𝓥)
               → (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥) ⁺ ̇
Definition-4-1 𝓦 𝓣 P = DisplayedPrecategory 𝓦 𝓣 P

Example-4-2 : {fe : Fun-Ext}
            → DisplayedPrecategory 𝓤 𝓤 (SetPrecategory fe)
Example-4-2 {𝓤} {fe} = DispPreMagma {𝓤} {fe}

module _ {P : Precategory 𝓦 𝓣}
         {a b : obj P} where
 open PrecategoryNotation P

 Definition-4-3 : (D : DisplayedPrecategory 𝓤 𝓥 P)
                  (x : obj[ a ] D)
                  (y : obj[ b ] D)
                  (f : a ≅ b)
                → 𝓥 ̇
 Definition-4-3 D x y f = x ≅[ f ] y
  where
   open DisplayedPrecategoryNotation D


 module _ {D : DisplayedPrecategory 𝓤 𝓥 P} where
  open DisplayedPrecategoryNotation D
  
  Proposition-4-4 : {x : obj[ a ] D}
                    {y : obj[ b ] D}
                    {f : a ≅ b}
                    (𝕗 : x ≅[ f ] y)
                    (g h : D-inverse f D-⌜ 𝕗 ⌝)
                  → D-⌞ g ⌟ ＝ D-⌞ h ⌟
  Proposition-4-4 𝕗 g h = at-most-one-D-inverse D g h
  Proposition-4-5 : {x : obj[ a ] D}
                    {y : obj[ b ] D}
                    {f : a ≅ b}
                    {𝕗 𝕘 : x ≅[ f ] y}
                  → D-⌜ 𝕗 ⌝ ＝ D-⌜ 𝕘 ⌝
                  → 𝕗 ＝ 𝕘
  Proposition-4-5 = to-≅[-]-＝

  Proposition-4-6 : (x : obj[ a ] D)
                    (y : obj[ b ] D)
                    (e : a ＝ b)
                  → x ＝⟦ (λ - → obj[ - ] D) , e ⟧ y
                  → x ≅[ id-to-iso a b e ] y
  Proposition-4-6 x y e = D-id-to-iso D e x y

 Definition-4-7 : (D : DisplayedPrecategory 𝓤 𝓥 P)
                → is-displayed-category D
                → DisplayedCategory 𝓤 𝓥 P
 Definition-4-7 D p = D , p

 Example-4-8 : {fe : Fun-Ext}
             → DisplayedCategory 𝓤 𝓤 (SetPrecategory fe)
 Example-4-8 {𝓤} {fe} = DispCatMagma {𝓤} {fe}

\end{code}

### Section 4.2: Displayed Functor

\begin{code}

Definition-4-9 : {P : Precategory 𝓦 𝓣}
                 {P' : Precategory 𝓦' 𝓣'}
                 (F : Functor P P')
                 (D : DisplayedPrecategory 𝓤 𝓥 P)
                 (D' : DisplayedPrecategory 𝓤' 𝓥' P')
               → 𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ̇
Definition-4-9 F D D' = DisplayedFunctor F D D'

\end{code}

### Section 4.3: Total Category

\begin{code}

Proposition-4-10 : (P : Precategory 𝓤 𝓥)
                   (D : DisplayedPrecategory 𝓦 𝓣 P)
                 → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
Proposition-4-10 P D = TotalPrecategory D

Proposition-4-11 : (C : Category 𝓤 𝓥)
                   (D : DisplayedCategory 𝓦 𝓣 ⟨ C ⟩)
                 → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
Proposition-4-11 C D = TotalCategory {_} {_} {_} {_} {C} D

Example-4-12-pre : {𝓤 : Universe}
                   {fe : Fun-Ext}
                 → Precategory (𝓤 ⁺) 𝓤
Example-4-12-pre {𝓤} {fe} = MagmaTotalPre {𝓤} {fe}

Example-4-12-univ : {𝓤 : Universe}
                    {fe : Fun-Ext}
                  → is-univalent 𝓤
                  → Category (𝓤 ⁺) 𝓤
Example-4-12-univ {𝓤} {fe} = TotCatMagma {𝓤} {fe}

\end{code}
