Anna Williams 14 February 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_)
open import UF.EquivalenceExamples
open import UF.Sets-Properties
open import UF.DependentEquality
open import Notation.UnderlyingType
open import Categories.Wild
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Pre hiding (⌜_⌝)
open import Categories.Notation.Univalent hiding (⌜_⌝)
open import Categories.Displayed.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Notation.Pre
open import Categories.Displayed.Notation.Univalent

module Categories.Displayed.Total where

\end{code}

We can now define a total precategory. This is the category that pairs up the
objects of a 'base' precategory with the corresponding objects index by that
object in the displayed precategory. That is, the objects are of the form
Σ x : obj P , obj[ x ]. We similarly define the homomorphisms and other fields.

\begin{code}

module _ {𝓤 𝓥 𝓦 𝓣 : Universe} where

 TotalPrecategory : {P : Precategory 𝓤 𝓥}
                    (D : DisplayedPrecategory 𝓦 𝓣 P)
                  → Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
 TotalPrecategory {P} D = (total-wild-category
                                           , total-is-precategory)
  where
   open PrecategoryNotation P
   open DisplayedPrecategoryNotation D

   total-wild-category : WildCategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
   total-wild-category = wildcategory
                        (Σ p ꞉ obj P , obj[ p ] D)
                        (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                        (𝒊𝒅 , D-𝒊𝒅)
                        (λ (g , 𝕘) (f , 𝕗) → g ◦ f , 𝕘 ○ 𝕗)
                        (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-left-neutral f
                                             , transport-from-dependent-Id
                                                (D-𝒊𝒅-is-left-neutral 𝕗)))
                        (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-right-neutral f
                                             , transport-from-dependent-Id
                                                (D-𝒊𝒅-is-right-neutral 𝕗)))
                        (λ f g h → to-Σ-＝ (assoc _ _ _
                                        , transport-from-dependent-Id D-assoc))

   total-is-precategory : is-precategory total-wild-category
   total-is-precategory _ _ = Σ-is-set (hom-is-set P) (λ _ → hom[-]-is-set)

\end{code}

We now show that if we have a category and a displayed category, the total
category formed of these is a category.

\begin{code}

 module _ {P : Precategory 𝓤 𝓥} (D : DisplayedPrecategory 𝓦 𝓣 P) where
  open PrecategoryNotation P
  open PrecategoryNotation (TotalPrecategory D)
  open DisplayedPrecategoryNotation D
  
  total-iso-join :  {a b : obj P} {x : obj[ a ] D} {y : obj[ b ] D}
                 → (Σ f ꞉ a ≅ b , x ≅[ f ] y) ≃ ((a , x) ≅ (b , y))
  total-iso-join {a} {b} {x} {y} = qinveq F (F⁻¹ , has-section , is-section)
   where
    F : (Σ f ꞉ a ≅ b , x ≅[ f ] y) → ((a , x) ≅ (b , y))
    F ((f , f⁻¹ , p , q)
     , (𝕗 , 𝕗⁻¹ , 𝕡 , 𝕢)) = (f , 𝕗)
                         , (f⁻¹ , 𝕗⁻¹)
                         , to-Σ-＝ (p , transport-from-dependent-Id 𝕡)
                         , to-Σ-＝ (q , transport-from-dependent-Id 𝕢)

    F⁻¹ : ((a , x) ≅ (b , y)) → (Σ f ꞉ a ≅ b , x ≅[ f ] y)
    F⁻¹ ((f , 𝕗) , (f⁻¹ , 𝕗⁻¹) , p , q) = (f , f⁻¹ , ap pr₁ p , ap pr₁ q)
                                       , (𝕗 , 𝕗⁻¹ , snd-eq-left , snd-eq-right)
     where
      snd-eq-left : 𝕗⁻¹ ○ 𝕗 ＝⟦ (λ - → hom[ - ] _ _) , ap pr₁ p ⟧ D-𝒊𝒅
      snd-eq-left = dependent-Id-from-transport (pr₂ (from-Σ-＝ p))

      snd-eq-right : 𝕗 ○ 𝕗⁻¹ ＝⟦ (λ - → hom[ - ] _ _) , ap pr₁ q ⟧ D-𝒊𝒅
      snd-eq-right = dependent-Id-from-transport (pr₂ (from-Σ-＝ q))

    has-section : F⁻¹ ∘ F ∼ id
    has-section e@(iso@(f , f⁻¹ , p , q)
     , d-iso@(𝕗 , 𝕗⁻¹ , 𝕡 , 𝕢)) = to-Σ-＝ (f-eq , disp-eq)
     where
      f-eq = to-≅-＝ refl

      lem : {a b : obj P}
            {x : obj[ a ] D}
            {y : obj[ b ] D}
            {f f' : a ≅ b}
            (e : f ＝ f')
            (𝕗 : x ≅[ f ] y)
          → pr₁ (transport (λ - → x ≅[ - ] y) e 𝕗)
          ＝ transport _ (ap pr₁ e) (pr₁ 𝕗)
      lem refl _ = refl

      𝕗' = (pr₂ ((F⁻¹ ∘ F) e))

      eq : pr₁ (transport (λ - → x ≅[ - ] y) f-eq 𝕗') ＝ 𝕗
      eq = pr₁ (transport (λ - → x ≅[ - ] y) f-eq 𝕗')            ＝⟨ I ⟩
           transport (λ - → hom[ - ] x y) (ap pr₁ f-eq) (pr₁ 𝕗') ＝⟨ II ⟩
           𝕗 ∎
       where
        I = lem f-eq _
        II = ap₂ (transport (λ - → hom[ - ] x y))
                 (hom-is-set P (ap pr₁ f-eq) refl)
                 refl

      disp-eq : transport (λ - → x ≅[ - ] y) f-eq (pr₂ ((F⁻¹ ∘ F) e)) ＝ d-iso
      disp-eq = to-≅[-]-＝ eq

    is-section : F ∘ F⁻¹ ∼ id
    is-section ((f , 𝕗) , (f⁻¹ , 𝕗⁻¹) , p , q) = to-≅-＝ refl


 TotalCategory : {C : Category 𝓤 𝓥}
                 (D : DisplayedCategory 𝓦 𝓣 ⟨ C ⟩)
               → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
 TotalCategory {C} D = (TotalPrecategory ⟨ D ⟩) , is-cat
  where
   open CategoryNotation C
   open DisplayedCategoryNotation D
   open PrecategoryNotation (TotalPrecategory ⟨ D ⟩)

   is-cat : is-category (TotalPrecategory ⟨ D ⟩)
   is-cat (a , x) (b , y) = equiv-closed-under-∼ ⌜ univalence ⌝
                                                 (id-to-iso (a , x) (b , y))
                                                 ⌜ univalence ⌝-is-equiv
                                                 pointwise-equality
    where
     univalence : ((a , x) ＝ (b , y)) ≃ ((a , x) ≅ (b , y))
     univalence = ((a , x) ＝ (b , y))                      ≃⟨ i ⟩
                  ((Σ e ꞉ a ＝ b , transport _ e x ＝ y))   ≃⟨ ii ⟩
                  (Σ e ꞉ a ＝ b , x ≅[ id-to-iso a b e ] y) ≃⟨ iii ⟩
                  (Σ f ꞉ a ≅ b , x ≅[ f ] y)                ≃⟨ iv ⟩
                  total-isomorphism                         ■
      where
       total-isomorphism : 𝓥 ⊔ 𝓣 ̇
       total-isomorphism = ((a , x) ≅ (b , y))

       transport-equiv-iso : (e : a ＝ b)
                           → (transport (λ - → obj[ - ] D) e x ＝ y)
                           ≃ x ≅[ id-to-iso a b e ] y
       transport-equiv-iso refl = (D-id-to-iso ⟨ D ⟩ refl x y)
                                , D-id-to-iso-is-equiv D refl x y

       i = Σ-＝-≃
       ii = Σ-cong transport-equiv-iso
       iii = Σ-change-of-variable (λ - → (x ≅[ - ] y))
                                  (id-to-iso a b)
                                  (id-to-iso-is-equiv C a b)
       iv = total-iso-join ⟨ D ⟩

     pointwise-equality : id-to-iso (a , x) (b , y)
                         ∼ ⌜ univalence ⌝
     pointwise-equality refl = refl

\end{code}
