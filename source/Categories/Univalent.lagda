Anna Williams 29/01

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import MLTT.Spartan
open import Categories.Wild
open import Categories.Pre
open import Categories.Notation
open import Notation.UnderlyingType

module Categories.Univalent where

\end{code}


A category is exactly a univalent precategory.

\begin{code}

Category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Category 𝓤 𝓥 = Σ P ꞉ Precategory 𝓤 𝓥 , is-category ⟨ P ⟩

\end{code}

Projections from a category.

\begin{code}

instance
  underlying-precategory-of-category
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Category 𝓤 𝓥) (Precategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-precategory-of-category}} (P , _) = P

  underlying-wildcategory-of-category
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Category 𝓤 𝓥) (WildCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-wildcategory-of-category}} ((W , _) , _) = W


id-to-iso-is-equiv : (C : Category 𝓤 𝓥)
                   → is-category ⟨ C ⟩
id-to-iso-is-equiv = pr₂

instance
 catobj : {𝓤 𝓥 : Universe} → OBJ (Category 𝓤 𝓥) (𝓤 ̇ )
 obj {{catobj}} ((C , _) , _) = WildCategory.obj C

\end{code}

We can now show that the objects of any category are 1-types. This is because
equality between objects is given exactly by isomorphism, which we have shown
forms a set.

\begin{code}

cat-objs-form-a-1-type : (A : Category 𝓤 𝓥) → (a b : obj A) → is-set (a ＝ b)
cat-objs-form-a-1-type A a b = equiv-to-set id-equiv-iso
                                          (isomorphism-type-is-set ⟨ A ⟩)
 where
  open CategoryNotation ⟨ A ⟩
  id-equiv-iso : (a ＝ b) ≃ a ≅ b
  id-equiv-iso = id-to-iso a b , id-to-iso-is-equiv A a b

\end{code}
