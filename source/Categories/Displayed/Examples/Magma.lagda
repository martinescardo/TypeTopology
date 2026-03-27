Anna Williams 25 February 2026

Category of Magmas via displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.DependentEquality
open import UF.Equiv
open import UF.FunExt
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Univalent
open import Categories.Notation.Pre
open import Categories.Examples.Set
open import Categories.Examples.Magma
open import Categories.Displayed.Pre
open import Categories.Displayed.Notation.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Total

module Categories.Displayed.Examples.Magma where

\end{code}

We define the displayed precategory of magmas over set.
The displayed object, for each object of set is the collection
of magmas for that given set. This is given by the type of magma operations.

The displayed homomorphism is exactly the type expressing that a given
magma operation is a magma homomorphism.

The rest follows as expected.

\begin{code}


module _ {𝓤 : Universe} {fe : Fun-Ext} where
 open PrecategoryNotation (SetPrecategory {𝓤} fe)

 DispPreMagma : DisplayedPrecategory 𝓤 𝓤 (SetPrecategory fe)
 DispPreMagma = record
              { obj[_] = λ (A , _) → (A → A → A)
              ; hom[_] = λ {(A , _)} f _·_ _*_
                       → (x y : A) → f (x · y) ＝ f x * f y
              ; hom[-]-is-set = λ {_} {(_ , sB)}
                              → Π₂-is-set fe λ x y → props-are-sets (sB _ _)
              ; D-𝒊𝒅 = λ _ _ → refl
              ; _○_ = λ {_} {_} {_} {g} {f} {_·_} {_*_} {_∙_} gmagma fmagma x y
                    → g (f (x · y))     ＝⟨ ap g (fmagma x y) ⟩
                      g (f x * f y)     ＝⟨ gmagma (f x) (f y) ⟩
                      g (f x) ∙ g (f y) ∎
              ; D-𝒊𝒅-is-right-neutral = λ {_} {(_ , sB)} 𝕗
                 → (dfunext fe λ _ → dfunext fe λ _ → sB _ _ _ _)
              ; D-𝒊𝒅-is-left-neutral = λ {_} {(_ , sB)} 𝕗
                 → (dfunext fe λ _ → dfunext fe λ _ → sB _ _ _ _)
              ; D-assoc = λ {_} {_} {_} {(_ , sD)}
                 → (dfunext fe λ x → dfunext fe λ y → sD _ _ _ _)
              }

\end{code}

We can now define the precategory of magmas (again), using the total precategory
formed of the magma displayed precategory over set.

\begin{code}

 MagmaTotalPre : Precategory (𝓤 ⁺) 𝓤
 MagmaTotalPre = TotalPrecategory DispPreMagma

\end{code}

We now define the displayed category of magmas.

\begin{code}

 open DisplayedPrecategoryNotation DispPreMagma

 DispCatMagma : DisplayedCategory 𝓤 𝓤 (SetPrecategory fe)
 DispCatMagma = DispPreMagma , λ {a} {b} e x y → is-disp-cat a b e x y
  where

   is-disp-cat : (a : obj (SetPrecategory fe))
                 (b : obj (SetPrecategory fe))
                 (e : a ＝ b)
                 (x : obj[ a ] DispPreMagma)
                 (y : obj[ b ] DispPreMagma)
               → is-equiv (D-id-to-iso DispPreMagma {a} {b} e x y)
   is-disp-cat a@(A , sA) b refl _·_ _*_ = (iso-to-id , has-section) 
                                         , (iso-to-id , is-section)
    where
     iso-to-id : _≅[_]_ {_} {_} {_} {_} {_} {_} {a} {a}
                 _·_ (id , id , refl , refl) _*_
              → dependent-Id (λ - → obj[ - ] DispPreMagma) {a} refl _·_ _*_
     iso-to-id (f , _) = dfunext fe λ x → dfunext fe λ y → f x y

     has-section : (D-id-to-iso DispPreMagma refl _·_ _*_) ∘ iso-to-id
                 ∼ id
     has-section _
      = to-Σ-＝ (Π₂-is-prop fe (λ x y → sA _ _) _ _
      , to-Σ-＝ ((Π₂-is-prop fe (λ x y → sA _ _) _ _)
      , to-×-＝ (Π₂-is-set fe (λ x y → props-are-sets (sA _ _)) _ _)
                (Π₂-is-set fe (λ x y → props-are-sets (sA _ _)) _ _)))

     is-section : iso-to-id ∘ (D-id-to-iso DispPreMagma refl _·_ _*_)
                ∼ id
     is-section _ = Π₂-is-set fe (λ x y → sA _ _) _ _

\end{code}
