Anna Williams, 12 November 2025

The Category of Sets

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Wild hiding (⌜_⌝)
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_) renaming (inverse to e-inverse)
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

module Categories.Examples.Set where

\end{code}

First we define Sets under a given universe 𝓤. We first define the property of
being a set, note that we define this with explicit arguments here, and then
the type of sets.

\begin{code}

module _ {𝓤 : Universe} where
 is-set-explicit : 𝓤 ̇ → 𝓤 ̇
 is-set-explicit A = Π a ꞉ A , Π b ꞉ A , is-prop (a ＝ b)

 Sets : 𝓤 ⁺ ̇
 Sets = Σ X ꞉ 𝓤 ̇ , is-set-explicit X

\end{code}

We define the wild category of sets in the expected way. This is where
the homs are exactly functions between the underlying type of the sets.

\begin{code}

 SetWildCategory : WildCategory (𝓤 ⁺) 𝓤
 SetWildCategory = wildcategory Sets
                                (λ (X , _) (Y , _) → (X → Y))
                                id
                                _∘_
                                (λ _ → refl)
                                (λ _ → refl)
                                (λ _ _ _ → refl)

 open WildCategoryNotation SetWildCategory

\end{code}

We now define the precategory of sets. Notably, the homs are sets since the
underlying type of the codomain is a set.

\begin{code}

 SetPrecategory : (fe : Fun-Ext) → Precategory (𝓤 ⁺) 𝓤
 SetPrecategory fe = (SetWildCategory , set-is-precategory)
  where
   set-is-precategory : is-precategory SetWildCategory
   set-is-precategory (X , sX) (Y , sY)
    = Π-is-set fe (λ _ → sY _ _)

\end{code}

To now show this is a category, we show that identification between sets
corresponds with isomorphism of objects in the wild category. Notice that
we can also prove this using SIP.

\begin{code}

 id-equiv-iso : (ua : is-univalent 𝓤)
                (fe : Fun-Ext)
                (A B : Sets)
              → (A ＝ B) ≃ (A ≅ B)
 id-equiv-iso ua fe (X , sX) (Y , sY) = ((X , sX) ＝ (Y , sY)) ≃⟨ i ⟩
                                        (X ＝ Y)               ≃⟨ ii ⟩
                                        (X ≃ Y)                ≃⟨ iii ⟩
                                        (X , sX) ≅ (Y , sY)    ■
  where
   i : (X , sX ＝ Y , sY) ≃ (X ＝ Y)
   i = subtype-＝-≃-pr₁-＝ is-set-explicit
                            (λ _ → Π₂-is-prop fe
                                    (λ x y → being-prop-is-prop fe))
                            (X , sX) (Y , sY)

   ii : (X ＝ Y) ≃ (X ≃ Y)
   ii = idtoeq X Y , ua X Y

   iii : (X ≃ Y) ≃ (X , sX) ≅ (Y , sY)
   iii = Σ-cong equiv-≃-inverse
    where
     qinv-≃-inverse : (f : X → Y)
                    → qinv f ≃ inverse {_} {_} {_} {X , sX} {Y , sY} f
     qinv-≃-inverse f = qinveq g (g⁻¹ , g-is-section , g-has-section)
      where
       g : qinv f → inverse {_} {_} {_} {X , sX} {Y , sY} f
       g (h , lh , rh) = h , (dfunext fe lh , dfunext fe rh)

       g⁻¹ : inverse {_} {_} {_} {X , sX} {Y , sY} f → qinv f
       g⁻¹ (h , lh , rh) = h
                               , (λ x → ap (λ - → - x) lh)
                               , λ y → ap (λ - → - y) rh

       g-is-section : g⁻¹ ∘ g ∼ id
       g-is-section (h , lh , rh) = to-Σ-＝ (refl
                                   , (to-×-＝ (dfunext fe (λ x → sX _ _ _ _))
                                              (dfunext fe (λ y → sY _ _ _ _))))
                                             
       g-has-section : g ∘ g⁻¹ ∼ id
       g-has-section (h , lh , rh) = to-Σ-＝ (refl
                                  , (to-×-＝ (Π-is-set fe (λ x → sX _ _) _ _)
                                             (Π-is-set fe (λ y → sY _ _) _ _)))

     equiv-≃-inverse : (f : X → Y)
                     → is-equiv f ≃ inverse {_} {_} {_} {X , sX} {Y , sY} f
     equiv-≃-inverse f = ≃-comp
                          (is-equiv-≃-qinv fe f (sX _ _))
                          (qinv-≃-inverse f)

\end{code}

We can finally prove that Set forms a category.

\begin{code}

 SetCategory : (ua : is-univalent 𝓤)
               (fe : Fun-Ext)
             → Category (𝓤 ⁺) 𝓤
 SetCategory ua fe = SetPrecategory fe , set-is-category
  where
   pointwise-equal : (a b : obj SetWildCategory)
                   → id-to-iso a b ∼ ⌜ id-equiv-iso ua fe a b ⌝
   pointwise-equal (a , sA) b refl
    = to-Σ-＝ (refl
            , (to-Σ-＝ (refl
                     , to-×-＝ (Π-is-set fe (λ x → sA _ _) _ _)
                               (Π-is-set fe (λ x → sA _ _) _ _))))

   set-is-category : is-category (SetPrecategory fe)
   set-is-category a b
    = equiv-closed-under-∼ ⌜ id-equiv-iso ua fe a b ⌝
                           (id-to-iso a b)
                           (⌜ id-equiv-iso ua fe a b ⌝-is-equiv)
                           (pointwise-equal a b)

\end{code}

