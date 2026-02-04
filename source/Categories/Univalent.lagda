Anna Williams 29 January 2026

Definition of a (univalent) category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Sets
open import UF.Sets-Properties
open import UF.Equiv hiding (_≅_)
open import UF.Equiv-FunExt
open import MLTT.Spartan
open import Categories.Wild
open import Categories.Pre
open import Categories.Notation.Wild
open import Categories.Notation.Pre
open import Notation.UnderlyingType
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Categories.Univalent where

\end{code}

We wish to combine the similar notions of equivalence, namely the internal
equality, a ＝ b, and isomorphisms, a ≅ b.

To bring into alignment the two different forms of equality, we define the
property of being a category, where identification is equivalent to isomorphism.
That is the map `id-to-iso` is an equivalence.

\begin{code}

module _ {𝓤 𝓥 : Universe} (P : Precategory 𝓤 𝓥) where
 open PrecategoryNotation P

 is-category : (𝓤 ⊔ 𝓥) ̇
 is-category = (a b : obj P) → is-equiv (id-to-iso a b)

 being-cat-is-prop : (fe : Fun-Ext)
                   → is-prop (is-category)
 being-cat-is-prop fe x y = Π₂-is-prop fe I _ _
  where
   I : (a b : obj P) → is-prop (is-equiv (id-to-iso a b))
   I a b = being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) (id-to-iso a b)

\end{code}

We can now define a category.

\begin{code}

Category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Category 𝓤 𝓥 = Σ P ꞉ Precategory 𝓤 𝓥 , is-category P

\end{code}

We now define the object notation for a category and the projections from
the sigma type.

\begin{code}

instance
 catobj : {𝓤 𝓥 : Universe} → OBJ (Category 𝓤 𝓥) (𝓤 ̇ )
 obj {{catobj}} ((C , _) , _) = WildCategory.obj C

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

\end{code}

We can now show that the objects of any category are 1-types. This is because
equality between objects is given exactly by isomorphism, which we have shown
forms a set.

\begin{code}

cat-objs-form-a-1-type : (C : Category 𝓤 𝓥) → (a b : obj C) → is-set (a ＝ b)
cat-objs-form-a-1-type C a b = equiv-to-set
                                id-equiv-iso
                                (isomorphism-type-is-set ⟨ C ⟩)
 where
  open PrecategoryNotation ⟨ C ⟩
  id-equiv-iso : (a ＝ b) ≃ a ≅ b
  id-equiv-iso = id-to-iso a b , id-to-iso-is-equiv C a b

\end{code}
