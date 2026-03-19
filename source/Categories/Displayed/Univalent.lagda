Anna Williams 14 February 2026

Definition of univalent displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.DependentEquality
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Univalent where

\end{code}

Following the definition of isomorphism, as with categories we can now define
the notion of id-to-iso for displayed precategories.

\begin{code}

module _ {P : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓣 P) where
 open PrecategoryNotation P
 open DisplayedPrecategoryNotation D

 D-id-to-iso : {a b : obj P}
               (e : a ＝ b)
               (x : obj[ a ] D)
               (y : obj[ b ] D)
             → x ＝⟦ (λ - → obj[ - ] D) , e ⟧ y
             → x ≅[ id-to-iso a b e ] y
 D-id-to-iso refl x _ refl = D-𝒊𝒅 , D-𝒊𝒅 , h , h
  where
   h : D-𝒊𝒅 ○ D-𝒊𝒅 ＝⟦ (λ - → hom[ - ] x x) , 𝒊𝒅-is-left-neutral 𝒊𝒅 ⟧ D-𝒊𝒅
   h = D-𝒊𝒅-is-left-neutral D-𝒊𝒅

\end{code}

We define the property of being a displayed category akin to that of being a
category.

\begin{code}

 is-displayed-category : (𝓤 ⊔ 𝓦 ⊔ 𝓣) ̇
 is-displayed-category = {a b : obj P}
                         (e : a ＝ b)
                         (x : obj[ a ] D)
                         (y : obj[ b ] D)
                       → is-equiv (D-id-to-iso e x y)

 is-displayed-category-is-prop : (fe : Fun-Ext)
                               → is-prop (is-displayed-category)
 is-displayed-category-is-prop fe = implicit-Π₂-is-prop fe
                                     (λ x y → Π₃-is-prop fe (I x y))
  where
   I : (a b : obj P)
       (e : a ＝ b)
       (x : obj[ a ] D)
       (y : obj[ b ] D)
     → is-prop (is-equiv (D-id-to-iso e x y))
   I a b e x y = being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥})
                                     (D-id-to-iso e x y)

\end{code}

We can now define displayed categories. These are exactly precategories such
that the map D-id-to-iso is an equivalence.

\begin{code}

DisplayedCategory : (𝓤 𝓥 : Universe)
                    {𝓦 𝓣 : Universe}
                    (P : Precategory 𝓦 𝓣)
                  → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇
DisplayedCategory 𝓤 𝓥 P = Σ D ꞉ DisplayedPrecategory 𝓤 𝓥 P
                          , is-displayed-category D
\end{code}

Projections from a displayed category.

\begin{code}

instance
  underlying-disp-precat-of-disp-cat
   : {P : Precategory 𝓦 𝓣}
   → Underlying-Type (DisplayedCategory 𝓤 𝓥 P) (DisplayedPrecategory 𝓤 𝓥 P)
  ⟨_⟩ {{underlying-disp-precat-of-disp-cat}} (D , _) = D

D-id-to-iso-is-equiv : {P : Precategory 𝓦 𝓣}
                       (D : DisplayedCategory 𝓤 𝓥 P)
                     → is-displayed-category ⟨ D ⟩
D-id-to-iso-is-equiv = pr₂

\end{code}
