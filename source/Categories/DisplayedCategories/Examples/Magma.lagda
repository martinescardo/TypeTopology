Anna Williams, 30 November 2025

Examples involving displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Type
open import Categories.DisplayedCategories.Type
open import Categories.Examples.Magma
open import Categories.Examples.Set

open import MLTT.Spartan
open import UF.Base
open import UF.DependentEquality
open import UF.FunExt
open import UF.Sets-Properties
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.DisplayedCategories.Examples.Magma where

\end{code}

We define the Displayed Precategory of Magmas

\begin{code}

module _ {𝓤 : Universe} where
 Magma-DPrecat : (fe : Fun-Ext) → DisplayedPrecategory 𝓤 𝓤 (SetPrecat fe)
 Magma-DPrecat fe = record
                     { obj[_] = λ (X , _) → X → X → X
                     ; hom[_] = λ {(a , _)} f _·_ _*_ → (x y : a) → f (x · y) ＝ (f x) * (f y)
                     ; hom[-]-is-set = λ {_} {(_ , sB)} → Π-is-set fe
                                                          λ x → Π-is-set fe
                                                            λ y → props-are-sets (sB _ _)
                     ; id-fam = λ _·_ x x' → refl
                     ; comp = λ {a} {b} {c} {f} {g} {_·_} {_*_} {_∙_} gyz fxy x y → {!!}
                     ; cmp-right-id = {!!}
                     ; cmp-left-id = {!!}
                     ; cmp-assoc = {!!}
                     }


 Magma-Precat : (fe : Fun-Ext) → Precategory (𝓤 ⁺) 𝓤
 Magma-Precat fe = TotalPrecategory (Magma-DPrecat fe)

 Magma-DCat : (ua : is-univalent 𝓤)
              (fe : Fun-Ext)
            → DisplayedCategory
 Magma-DCat ua fe = Magma-DPrecat fe , is-disp-cat
  where
   is-disp-cat : is-disp-category (Magma-DPrecat fe)
   is-disp-cat c c' refl _·_ _*_ = (fromiso , left) , (fromiso , right)
    where
     fromiso : _≅[_]_ {{Magma-DPrecat fe}} {c} {c'} _·_ (id-to-iso {{SetWildcat}} c c refl) _*_ → _·_ ＝ _*_
     fromiso (f , g , gl , gr) = dfunext fe (λ x → dfunext fe λ y → f x y)

     left : (λ x → id-to-iso-disp {{Magma-DPrecat fe}} (fromiso x)) ∼ (λ x → x)
     left (f , g , gl , gr) = {!!}
     
     right : (λ x → fromiso (id-to-iso-disp {{Magma-DPrecat fe}} x)) ∼ (λ x → x)
     right x = {!!}

\end{code}
