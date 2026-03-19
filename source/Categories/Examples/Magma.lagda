Anna Williams, 13 November 2025

The Category of Magmas

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Categories.Wild
open import Categories.Pre 
open import Categories.Univalent
open import Categories.Notation.Wild renaming (⌜_⌝ to ⌜_⌝')
open import Categories.Notation.Pre renaming (⌜_⌝ to ⌜_⌝')
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_) renaming (inverse to e-inverse)
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.SIP-Examples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.Examples.Magma where

\end{code}

We start by defining the Wild Category of Magmas, using the definition
of Magma from the SIP example for Magma.

\begin{code}

module _ {𝓤 : Universe} (fe : Fun-Ext) where
 open magma renaming (_≅_ to _M≅_)

 MagmaWildCategory : WildCategory (𝓤 ⁺) 𝓤
 MagmaWildCategory = wildcategory Magma
                                  magma-hom
                                  (λ {a} → magma-id {a})
                                  (λ {a} {b} {c} → magma-comp {a} {b} {c})
                                  (λ {a} {b} → left-id-neutral {a} {b})
                                  (λ {a} {b} → right-id-neutral {a} {b})
                                  λ {a} {b} {c} {d}
                                    → magma-assoc {a} {b} {c} {d}
  where
   magma-hom : (a b : Magma) → 𝓤 ̇
   magma-hom (X , _·_ , _)
             (Y , _*_ , _)
    = Σ f ꞉ (X → Y) , ((x y : X) → f (x · y) ＝ f x * f y)

   magma-id : {a : Magma} → magma-hom a a
   magma-id = id , λ x y → refl

   magma-comp : {a b c : Magma}
              → magma-hom b c
              → magma-hom a b
              → magma-hom a c
   magma-comp {X , _·_ , _}
              {Y , _*_ , _}
              {Z , _∙_ , _}
              (f , fp)
              (g , gp) = f ∘ g , ∘-preserves-property
    where
     ∘-preserves-property : (x y : X) → (f ∘ g) (x · y) ＝ (f ∘ g) x ∙ (f ∘ g) y
     ∘-preserves-property x y = (f ∘ g) (x · y)       ＝⟨ ap f (gp x y) ⟩
                                f (g x * g y)         ＝⟨ fp (g x) (g y) ⟩
                                (f ∘ g) x ∙ (f ∘ g) y ∎

   left-id-neutral : {a b : Magma}
                     (f : magma-hom a b)
                   → magma-comp {a} {b} {b} (magma-id {b}) f ＝ f
   left-id-neutral {_} {_ , _ , sB} (f , pf)
    = to-Σ-＝ (refl , dfunext fe (λ x → dfunext fe (λ y → sB _ _)))

   right-id-neutral : {a b : Magma}
                      (f : magma-hom a b)
                    → magma-comp {a} {a} {b} f (magma-id {a}) ＝ f
   right-id-neutral {_} {_ , _ , sB} (f , pf)
    = to-Σ-＝ (refl , dfunext fe (λ x → dfunext fe (λ y → sB _ _)))

   magma-assoc : {a b c d : Magma}
                 (f : magma-hom a b)
                 (g : magma-hom b c)
                 (h : magma-hom c d)
               → magma-comp {a} {c} {d} h (magma-comp {a} {b} {c} g f)
               ＝ magma-comp {a} {b} {d} (magma-comp {b} {c} {d} h g) f
   magma-assoc {_} {_} {_} {_ , _ , sD} (f , pf) (g , pg) (h , ph)
    = to-Σ-＝ (refl , dfunext fe (λ x → dfunext fe (λ y → sD _ _)))

 open WildCategoryNotation MagmaWildCategory

\end{code}

We now show that this is a precategory

\begin{code}

 MagmaPrecategory : Precategory (𝓤 ⁺) 𝓤
 MagmaPrecategory = MagmaWildCategory , is-pre
  where
   is-pre : is-precategory MagmaWildCategory
   is-pre (_ , _ , sX) (_ , _ , sY)
    = Σ-is-set (Π-is-set fe (λ _ → sY))
       λ f → Π₂-is-set fe
         λ x y → props-are-sets sY

\end{code}

We show that Magmas have univalence, using the SIP example for Magmas. To do
this, we show that the notion of isomorphism for the sip example is equivalent
to that of isomorphism in the magma wild category.

\begin{code}

module _ {𝓤 : Universe} (fe : Fun-Ext) where
 open magma renaming (_≅_ to _M≅_)
 open PrecategoryNotation (MagmaPrecategory {𝓤} fe)

 sns-equiv-iso : (A B : Magma)
               → (A M≅ B) ≃ (A ≅ B)
 sns-equiv-iso A@(a , _·_ , sA) B@(b , _*_ , sB)
  = qinveq toiso (fromiso , has-section , is-section)
  where
   toiso : A M≅ B → A ≅ B
   toiso (f , e@((g , gp) , (g' , gp')) , fp)
         = (f , λ x y → ap (λ - → - x y) fp)
         , (g , g-is-hom)
         , to-subtype-＝ left-is-prop (e-inverse _ (fe _ _) left-inv)
         , to-subtype-＝ right-is-prop (e-inverse _ (fe _ _) gp)
    where
     g-is-hom : (x y : b) → g (x * y) ＝ (g x · g y)
     g-is-hom x y = g (x * y)             ＝⟨ i ⟩
                    g (f (g x) * y)       ＝⟨ ii ⟩
                    g (f (g x) * f (g y)) ＝⟨ iii ⟩
                    g (f (g x · g y))     ＝⟨ iv ⟩
                    g x · g y             ∎
      where
       i   = ap (λ - → g (- * y)) (gp x)⁻¹
       ii  = ap (λ - → g (f (g x) * -)) (gp y)⁻¹
       iii = ap g ((λ x y → ap (λ - → - x y) fp) (g x) (g y))⁻¹
       iv  = inverses-are-retractions f e (g x · g y)

     left-is-prop = (λ _ → Π₂-is-prop fe (λ _ _ → sA))
     right-is-prop = (λ _ → Π₂-is-prop fe (λ _ _ → sB))
     
     left-inv : (λ x → g (f x)) ∼ (λ x → x)
     left-inv = inverses-are-retractions f e
     
   fromiso : A ≅ B → A M≅ B
   fromiso ((f , fp) , (g , gp) , lg , rg)
    = f
    , f-is-equiv
    , dfunext fe (λ x → dfunext fe (λ y → fp x y))

    where
     f-is-equiv = (g , λ x → ap (λ - → - x) (ap pr₁ rg))
                , (g , λ x → ap (λ - → - x) (ap pr₁ lg))

   is-section : toiso ∘ fromiso ∼ id
   is-section e@((f , fp) , (g , gp) , lg , rg)
    = to-≅-＝ {_} {_} {_} {A} {B} (to-subtype-＝ (λ _ → Π₂-is-prop fe (λ x y → sB)) refl)
   
   has-section : fromiso ∘ toiso ∼ id
   has-section (f , e@((g , gp) , (g' , gp')) , fp)
    = to-Σ-＝ (refl
            , (to-×-＝ is-equiv-f-＝ (Π₂-is-set fe (λ _ _ → sB) _ _)))
    where
     is-equiv-f-＝ = (to-×-＝
                 (to-subtype-＝ (λ p → Π-is-prop fe λ y → sB) refl)
                 (to-subtype-＝ (λ p → Π-is-prop fe λ y → sA) invs-eq))

      where
       invs-eq : g ＝ g'
       invs-eq = dfunext fe λ b → g b            ＝⟨ (gp' (g b))⁻¹ ⟩
                                  (g' ∘ f ∘ g) b ＝⟨ ap g' (gp b) ⟩
                                  g' b           ∎

 characterization-of-magma-＝ : is-univalent 𝓤
                             → (A B : Magma)
                             → (A ＝ B) ≃ (A ≅ B)
 characterization-of-magma-＝ ua A B = ≃-comp
                                       (characterization-of-Magma-＝ ua A B)
                                       (sns-equiv-iso A B)

\end{code}

And finally show that this is a category.

\begin{code}

 MagmaCategory : is-univalent 𝓤 → Category (𝓤 ⁺) 𝓤
 MagmaCategory ua = (MagmaPrecategory fe) , is-cat
  where
   pointwise-eq : (A B : Magma)
      → id-to-iso A B
      ∼ ⌜ characterization-of-magma-＝ ua A B ⌝
   pointwise-eq A@(a , _·_ , sA) B@(b , _*_ , sB) refl
    = to-Σ-＝ (refl , underlying-equality)
    where
     inv-eq' = to-subtype-＝ (λ f → Π₂-is-prop fe (λ _ _ → sB)) refl

     left-inv = hom-is-set (MagmaPrecategory fe) {A} {A} _ _
     right-inv = hom-is-set (MagmaPrecategory fe) {A} {A} _ _
    
     underlying-is-iso = underlying-morphism-is-isomorphism {_} {_} {_} {A} {B}

     underlying-equality : underlying-is-iso ((id-to-iso A B) refl)
                         ＝ underlying-is-iso 
                            (⌜ characterization-of-magma-＝ ua A B ⌝ refl) 
     underlying-equality = to-Σ-＝ (inv-eq' , to-×-＝ left-inv right-inv)

   is-cat : is-category (MagmaPrecategory fe)
   is-cat A B = equiv-closed-under-∼
                 ⌜ characterization-of-magma-＝ ua A B ⌝
                 (id-to-iso A B)
                 ⌜ characterization-of-magma-＝ ua A B ⌝-is-equiv
                 (pointwise-eq A B)

\end{code}
