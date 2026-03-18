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

ap₂-ish : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ } → (f : A → B → C) → {x x' : A} → {y : B} → (e : x ＝ x') → f x y ＝ f x' y
ap₂-ish f refl = refl

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
                        (Σ p ꞉ obj P , obj[ p ])
                        (λ (a , x) (b , y) → Σ f ꞉ hom a b , hom[ f ] x y)
                        (𝒊𝒅 , D-𝒊𝒅)
                        (λ (g , 𝕘) (f , 𝕗) → g ◦ f , 𝕘 ○ 𝕗)
                        (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-left-neutral f
                                             , Idtofun (dep-id _ _)
                                                (D-𝒊𝒅-is-left-neutral 𝕗)))
                        (λ (f , 𝕗) → to-Σ-＝ (𝒊𝒅-is-right-neutral f
                                             , Idtofun (dep-id _ _)
                                                (D-𝒊𝒅-is-right-neutral 𝕗)))
                        (λ f g h → to-Σ-＝ (assoc _ _ _
                                           , Idtofun (dep-id _ _) D-assoc))
    where
     dep-id = dependent-Id-via-transport

   total-is-precategory : is-precategory total-wild-category
   total-is-precategory _ _ = Σ-is-set (hom-is-set P) (λ _ → hom[-]-is-set)

 TotalCategory : {C : Category 𝓤 𝓥}
                 (D : DisplayedCategory 𝓦 𝓣 ⟨ C ⟩)
               → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣)
 TotalCategory {C} D = (TotalPrecategory ⟨ D ⟩) , is-cat
  where
   open CategoryNotation C
   open DisplayedCategoryNotation D
   open PrecategoryNotation (TotalPrecategory ⟨ D ⟩)

   is-cat : is-category (TotalPrecategory ⟨ D ⟩)
   is-cat (a , x) (b , y) = equiv-closed-under-∼ ⌜ thing ⌝
                                                 (id-to-iso (a , x) (b , y))
                                                 ⌜ thing ⌝-is-equiv
                                                 pointwise-equal
    where
     thing : ((a , x) ＝ (b , y)) ≃ ((a , x) ≅ (b , y))
     thing = ((a , x) ＝ (b , y))                       ≃⟨ i ⟩
             ((Σ e ꞉ a ＝ b , transport _ e x ＝ y))    ≃⟨ ii ⟩
             (Σ e ꞉ a ＝ b , x ≅[ id-to-iso a b e ] y)  ≃⟨ iii ⟩
             (Σ f ꞉ a ≅ b , x ≅[ f ] y)                ≃⟨ iv ⟩
             end                       ■
      where
       end : 𝓥 ⊔ 𝓣 ̇ 
       end = ((a , x) ≅ (b , y))

       inter : (e : a ＝ b)
             → (transport obj[_] e x ＝ y) ≃ x ≅[ id-to-iso a b e ] y
       inter refl = (D-id-to-iso ⟨ D ⟩ refl x y) , D-id-to-iso-is-equiv D refl x y

       total-iso-join : (Σ f ꞉ a ≅ b , x ≅[ f ] y) ≃ ((a , x) ≅ (b , y))
       total-iso-join = qinveq F (F⁻¹ , P , Q)
        where
         F : (Σ f ꞉ a ≅ b , x ≅[ f ] y) → ((a , x) ≅ (b , y))
         F ((f , f⁻¹ , p , q)
          , (𝕗 , 𝕗⁻¹ , 𝕡 , 𝕢)) = (f , 𝕗)
                              , (f⁻¹ , 𝕗⁻¹)
                              , to-Σ-＝ (p , Idtofun (dependent-Id-via-transport (λ - → hom[ - ] x x) p) 𝕡)
                              , to-Σ-＝ (q , Idtofun (dependent-Id-via-transport (λ - → hom[ - ] y y) q) 𝕢)

         F⁻¹ : ((a , x) ≅ (b , y)) → (Σ f ꞉ a ≅ b , x ≅[ f ] y)
         F⁻¹ ((f , 𝕗) , (f⁻¹ , 𝕗⁻¹) , p , q) = (f , f⁻¹ , ap pr₁ p , ap pr₁ q)
                                            , (𝕗 , 𝕗⁻¹ , snd-eq-left , snd-eq-right)
          where
           snd-eq-left : 𝕗⁻¹ ○ 𝕗 ＝⟦ (λ - → hom[ - ] _ _) , ap pr₁ p ⟧ D-𝒊𝒅
           snd-eq-left = (Idtofun ((dependent-Id-via-transport (λ - → hom[ - ] _ _) (ap pr₁ p))⁻¹)) (pr₂ (from-Σ-＝ p))

           snd-eq-right : 𝕗 ○ 𝕗⁻¹ ＝⟦ (λ - → hom[ - ] _ _) , ap pr₁ q ⟧ D-𝒊𝒅
           snd-eq-right = (Idtofun ((dependent-Id-via-transport (λ - → hom[ - ] _ _) (ap pr₁ q))⁻¹)) (pr₂ (from-Σ-＝ q))

         P : F⁻¹ ∘ F ∼ id
         P e@(iso@(f , f⁻¹ , p , q)
          , d-iso@(𝕗 , 𝕗⁻¹ , 𝕡 , 𝕢)) = to-Σ-＝ (to-≅-＝ ⟨ C ⟩ refl , disp-eq)
          where
           f-eq = to-≅-＝ ⟨ C ⟩ {_} {_} {_} {iso} refl

           lem : {x y : obj C}
                 {xx : obj[ x ]}
                 {yy : obj[ y ]}
                 {f f' : x ≅ y}
                 (e : f ＝ f')
                 (ff : xx ≅[ f ] yy)
               → pr₁ (transport (λ - → xx ≅[ - ] yy) e ff) ＝ transport _ (ap pr₁ e) (pr₁ ff)
           lem refl _ = refl
           
           eq : pr₁ (transport (λ - → x ≅[ - ] y) f-eq (pr₂ ((F⁻¹ ∘ F) e))) ＝ 𝕗
           eq = pr₁ (transport (λ - → x ≅[ - ] y) f-eq (pr₂ ((F⁻¹ ∘ F) e)))            ＝⟨ lem f-eq _ ⟩
                transport (λ - → hom[ - ] x y) (ap pr₁ f-eq) (pr₁ (pr₂ ((F⁻¹ ∘ F) e))) ＝⟨ p' ⟩
                𝕗 ∎
            where
             p' : transport (λ - → hom[ - ] x y) (ap pr₁ f-eq) (pr₁ (pr₂ ((F⁻¹ ∘ F) e))) ＝ transport {_} {_} {hom a b} (λ - → hom[ - ] x y) refl (pr₁ (pr₂ ((F⁻¹ ∘ F) e)))
             p' = ap₂-ish (transport (λ - → hom[ - ] x y)) (hom-is-set ⟨ C ⟩ (ap pr₁ f-eq) refl)

           disp-eq : transport (λ - → x ≅[ - ] y) (to-≅-＝ (C .pr₁) refl) (pr₂ ((F⁻¹ ∘ F) e)) ＝ d-iso
           disp-eq = DisplayedPrecategory.to-≅[-]-＝ ⟨ D ⟩ (transport (λ - → x ≅[ - ] y) (to-≅-＝ (C .pr₁) refl) (pr₂ ((F⁻¹ ∘ F) e))) d-iso eq
           
         Q : F ∘ F⁻¹ ∼ id
         Q ((f , 𝕗) , (f⁻¹ , 𝕗⁻¹) , p , q) = to-Σ-＝ (refl , to-Σ-＝ (refl , to-×-＝ (hom-is-set (TotalPrecategory ⟨ D ⟩) _ _)
                                                                                   (hom-is-set (TotalPrecategory ⟨ D ⟩) _ _)))

       i = Σ-＝-≃
       ii = Σ-cong inter
       iii = Σ-change-of-variable (λ - → (x ≅[ - ] y)) (id-to-iso a b) (id-to-iso-is-equiv C a b)
       iv = total-iso-join

     pointwise-equal : id-to-iso (a , x) (b , y) ∼ ⌜ thing ⌝
     pointwise-equal refl = refl

\end{code}
