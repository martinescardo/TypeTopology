Jon Sterling, started 28th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.Precategory where

open import MLTT.Spartan
open import UF.Subsingletons

-- We prefer composition in diagrammatic order.

category-structure : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
category-structure 𝓤 𝓥 =
 Σ ob ꞉ (𝓤 ̇),
 Σ hom ꞉ (ob → ob → 𝓥 ̇) ,
 Σ idn ꞉ ((A : ob) → hom A A) ,
 ({A B C : ob} (f : hom A B) (g : hom B C) → hom A C)

module category-structure (𝓒 : category-structure 𝓤 𝓥) where
 ob : 𝓤 ̇
 ob = pr₁ 𝓒

 hom : ob → ob → 𝓥 ̇
 hom A B = pr₁ (pr₂ 𝓒) A B

 idn : (A : ob) → hom A A
 idn A = pr₁ (pr₂ (pr₂ 𝓒)) A

 seq : {A B C : ob} (f : hom A B) (g : hom B C) → hom A C
 seq f g = pr₂ (pr₂ (pr₂ 𝓒)) f g

 cmp : {A B C : ob} (g : hom B C) (f : hom A B) → hom A C
 cmp f g = seq g f

module category-axiom-statements (𝓒 : category-structure 𝓤 𝓥) where
 open category-structure 𝓒

 statement-hom-is-set : 𝓤 ⊔ 𝓥 ̇
 statement-hom-is-set = (A B : ob) → is-set (hom A B)

 statement-idn-L : 𝓤 ⊔ 𝓥 ̇
 statement-idn-L = (A B : ob) (f : hom A B) → seq (idn A) f ＝ f

 statement-idn-R : 𝓤 ⊔ 𝓥 ̇
 statement-idn-R = (A B : ob) (f : hom A B) → seq f (idn B) ＝ f

 statement-assoc : 𝓤 ⊔ 𝓥 ̇
 statement-assoc =
  (A B C D : ob) (f : hom A B) (g : hom B C) (h : hom C D)
  → seq f (seq g h) ＝ seq (seq f g) h

 -- TODO: univalence statement

-- Precategories are an intermediate notion in univalent 1-category theory.
module _ (𝓒 : category-structure 𝓤 𝓥) where
 open category-axiom-statements 𝓒

 precategory-axioms : 𝓤 ⊔ 𝓥 ̇
 precategory-axioms =
  statement-hom-is-set
  × statement-idn-L
  × statement-idn-R
  × statement-assoc

 module precategory-axioms (ax : precategory-axioms) where
  hom-is-set : statement-hom-is-set
  hom-is-set = pr₁ ax

  idn-L : statement-idn-L
  idn-L = pr₁ (pr₂ ax)

  idn-R : statement-idn-R
  idn-R = pr₁ (pr₂ (pr₂ ax))

  assoc : statement-assoc
  assoc = pr₂ (pr₂ (pr₂ ax))

precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
precategory 𝓤 𝓥 =
 Σ 𝓒 ꞉ category-structure 𝓤 𝓥 ,
 precategory-axioms 𝓒

module precategory (𝓒 : precategory 𝓤 𝓥) where
 open category-structure (pr₁ 𝓒) public
 open precategory-axioms (pr₁ 𝓒) (pr₂ 𝓒) public

\end{code}
