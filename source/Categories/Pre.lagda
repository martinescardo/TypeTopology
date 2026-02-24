Anna Williams 29 January 2026

Definition of precategory.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Notation.Wild
open import UF.Sets
open import UF.Sets-Properties
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.FunExt

open import Notation.UnderlyingType
open import MLTT.Spartan
open import Categories.Wild

module Categories.Pre where

\end{code}

Precategories are exactly wild categories where the homs are sets. This
property is given by the below.

\begin{code}

module _ {𝓤 𝓥 : Universe} (W : WildCategory 𝓤 𝓥) where
 open WildCategoryNotation W

 is-precategory : (𝓤 ⊔ 𝓥) ̇
 is-precategory = (a b : obj W) → is-set (hom a b)

 being-precat-is-prop : (fe : Fun-Ext)
                      → is-prop (is-precategory)
 being-precat-is-prop fe = Π₂-is-prop fe (λ _ _ → being-set-is-prop fe)

\end{code}

We can now define the notion of a precategory.

\begin{code}

Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Precategory 𝓤 𝓥 = Σ W ꞉ WildCategory 𝓤 𝓥 , is-precategory W

\end{code}

This gives the object notation for precategories and projections from the
sigma type.

\begin{code}

instance
 precatobj : {𝓤 𝓥 : Universe} → OBJ (Precategory 𝓤 𝓥) (𝓤 ̇ )
 obj {{precatobj}} (P , _) = WildCategory.obj P

instance
  underlying-wildcategory-of-precategory
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Precategory 𝓤 𝓥) (WildCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-wildcategory-of-precategory}} (P , _) = P

hom-is-set : (P : Precategory 𝓤 𝓥)
             {a b : obj P}
           → is-set (WildCategory.hom ⟨ P ⟩ a b)
hom-is-set (_ , p) {a} {b} = p a b

\end{code}

We now show that in a precategory, for any given homomorphism, being an
isomorphism is a (mere) proposition. We argue that inverses are unique,
and then since the type of homomorphisms between two objects is a set,
equality between any two homomorphisms is a proposition, so our left and
right inverse equalities are a proposition.

\begin{code}

module _ (P : Precategory 𝓤 𝓥) where
 open WildCategoryNotation ⟨ P ⟩

 inverses-are-lc : {a b : obj P}
                   {f : hom a b}
                   (i j : inverse f)
                 → ⌞ i ⌟ ＝ ⌞ j ⌟
                 → i ＝ j
 inverses-are-lc i j refl = ap₂ (λ l r → ⌞ i ⌟ , l , r) l-eq r-eq
  where
   l-eq : ⌞ i ⌟-is-left-inverse ＝ ⌞ j ⌟-is-left-inverse
   l-eq = hom-is-set P ⌞ i ⌟-is-left-inverse ⌞ j ⌟-is-left-inverse

   r-eq : ⌞ i ⌟-is-right-inverse ＝ ⌞ j ⌟-is-right-inverse
   r-eq = hom-is-set P ⌞ i ⌟-is-right-inverse ⌞ j ⌟-is-right-inverse

 being-iso-is-prop : {a b : obj P}
                     (f : hom a b)
                   → is-prop (inverse f)
 being-iso-is-prop f i j = inverses-are-lc i j (at-most-one-inverse i j)

\end{code}

Following this, we can see that the type of isomorphisms is a set.

\begin{code}

 isomorphism-type-is-set : {a b : obj P}
                         → is-set (a ≅ b)
 isomorphism-type-is-set = Σ-is-set (hom-is-set P)
                                    (λ f → props-are-sets (being-iso-is-prop f))

\end{code}
