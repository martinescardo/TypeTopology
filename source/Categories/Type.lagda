Anna Williams, 17 October 2025

Definitions of:
 * precategory
 * category

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import Notation.UnderlyingType
open import UF.Base
open import UF.Equiv hiding (_≅_)
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties

module Categories.Type where

\end{code}

We start by defining the notion of a precategory.
This consists of the usual components of a (set theoretic) category,
which is as follows:

- A collection of objects, obj
- For each pair of objects, A B : obj, a set of homorphisms between A and B
- For each object A : obj, an identity homorphism (id A) : hom A A
- A composition operation, ∘, which for objects A B C : obj
  and homorphisms f : hom A B, g : hom B C gives a new homomorphism
  g ∘ f : hom A C

with the following axioms

- left-id: For objects A B : obj and morphism f : hom A B, f ∘ (id A) ＝ f
- right-id: For objects A B : obj and morphism f : hom A B, (id B) ∘ f ＝ f
- associativity: For objects A B C D : obj and morphisms f : hom A B,
                 g : hom B C, h : hom C D, we have h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f

\begin{code}

record Precategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇  where
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
  hom-is-set : {a b : obj} → is-set (hom a b)
  
  id : {a : obj} → hom a a
  
  _∘_ : {a b c : obj} → hom b c → hom a b → hom a c
  
  left-id : {a b : obj} → (f : hom a b) → id ∘ f ＝ f
  
  right-id : {a b : obj} → (f : hom a b) → f ∘ id ＝ f
  
  assoc : {a b c d : obj}
          {f : hom a b}
          {g : hom b c}
          {h : hom c d}
        → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f

\end{code}

We add instance argument versions of each field, apart from
obj, which we make explicit. We also add a syntax definition
for composition where the precategory cannot be inferred.

\begin{code}

open Precategory {{...}} public hiding (obj)

obj : (P : Precategory 𝓤 𝓥) → 𝓤 ̇
obj = Precategory.obj

pcat-comp : (P : Precategory 𝓤 𝓥)
          {a b c : obj P}
          → hom {{P}} b c
          → hom {{P}} a b
          → hom {{P}} a c
pcat-comp P f g = _∘_{{P}} f g

syntax pcat-comp P f g = f ∘[ P ] g

\end{code}

An isomorphism in a category consists of a homomorphism f : hom a b
and some "inverse" homomorphism g : hom b a, such that g ∘ f = (id a)
and f ∘ g ＝ (id b).

We first define the type of a given homomorphism being an isomorphism,
then we define the type of isomorphism between objects of a precategory.

\begin{code}

is-iso : {{ P : Precategory 𝓤 𝓥 }} {a b : obj P} (f : hom a b) → 𝓥 ̇ 
is-iso {{P}} {a} {b} f = Σ inv ꞉ hom b a , (inv ∘ f ＝ id) × (f ∘ inv ＝ id)

inv : {{ P : Precategory 𝓤 𝓥 }}
      {a b : obj P}
      {f : hom a b}
    → is-iso f
    → hom b a
inv iso = pr₁ iso

l-inverse : {{ P : Precategory 𝓤 𝓥 }}
            {a b : obj P}
            {f : hom {{P}} a b}
            (iso : is-iso f)
          → (inv iso) ∘ f ＝ id 
l-inverse iso = pr₁ (pr₂ iso)

r-inverse : {{ P : Precategory 𝓤 𝓥 }}
            {a b : obj P}
            {f : hom a b}
            (iso : is-iso f)
          → f ∘ (inv iso) ＝ id
r-inverse iso = pr₂ (pr₂ iso)

mk-iso : {{ P : Precategory 𝓤 𝓥 }}
         {a b : obj P}
         {f : hom a b}
         (inv : hom b a)
       → (inv ∘ f ＝ id)
       → (f ∘ inv ＝ id)
       → is-iso f
mk-iso inv l-id r-id = (inv , l-id , r-id)

_≅_ : {{ P : Precategory 𝓤 𝓥 }} (a b : obj P) → 𝓥 ̇
a ≅ b = Σ f ꞉ hom a b , is-iso f

\end{code}

We now show that for a given homomorphism, being an isomorphism is a
(mere) proposition. We argue that inverses are unique, and then since
the type of homomorphisms between two objects is a set, equality between
any two homomorphisms is a proposition, so our left and right inverse
equalities are a proposition.

\begin{code}

is-iso-eq : {{P : Precategory 𝓤 𝓥}}
            {a b : obj P}
            {f : hom {{P}} a b}
            (x y : is-iso f)
          → inv x ＝ inv y
          → x ＝ y
is-iso-eq x y refl = ap₂ (mk-iso (inv x)) l-eq r-eq
 where
  l-eq : l-inverse x ＝ l-inverse y
  l-eq = hom-is-set (l-inverse x) (l-inverse y)

  r-eq : r-inverse x ＝ r-inverse y
  r-eq = hom-is-set (r-inverse x) (r-inverse y)

being-iso-is-prop : {{P : Precategory 𝓤 𝓥}}
                    {a b : obj P}
                    (f : hom a b)
                  → is-prop (is-iso f)
being-iso-is-prop f x y = is-iso-eq x y inverse-eq
 where
  inverse-eq : inv x ＝ inv y
  inverse-eq = inv x                   ＝⟨ (right-id (inv x))⁻¹ ⟩
               (inv x) ∘ id            ＝⟨ ap ((inv x) ∘_) ((r-inverse y)⁻¹) ⟩
               (inv x) ∘ (f ∘ (inv y)) ＝⟨ assoc ⟩
               ((inv x) ∘ f) ∘ (inv y) ＝⟨ ap (_∘ (inv y)) (l-inverse x) ⟩
               id ∘ (inv y)            ＝⟨ left-id (inv y) ⟩
               inv y ∎

\end{code}

We now argue that this means that the type of isomorphisms is a set.
This follows from the fact that being an isomorphism is a proposition.

\begin{code}

isomorphisms-are-sets : {{P : Precategory 𝓤 𝓥}}
                        {a b : obj P}
                      → is-set (a ≅ b)
isomorphisms-are-sets = Σ-is-set hom-is-set
                         (λ f → props-are-sets (being-iso-is-prop f))

\end{code}

We wish to combine the similar notions of equivalence,
namely the internal equality: a ＝ b and isomorphisms a ≅ b.

We can in fact show that if a ＝ b, then a ≅ b. This is because if
a ＝ b, then by path induction we need to show that a ≅ a. This is
simple as we can form an isomophism with the identity homomorphism.

\begin{code}

id-to-iso : {{ A : Precategory 𝓤 𝓥 }} (a b : obj A) → a ＝ b → a ≅ b
id-to-iso {{A}} a b refl = id , (mk-iso id id-comp-id-is-id id-comp-id-is-id)
 where
  id-comp-id-is-id : id ∘ id ＝ id
  id-comp-id-is-id = left-id id
\end{code}

To bring into alignment the two different forms of equality, we define a
category to be a precategory where identification is equivalent to isomorphism.

\begin{code}

Category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Category 𝓤 𝓥 = Σ P ꞉ Precategory 𝓤 𝓥 ,
                     ((a b : obj P) → (a ＝ b) ≃ (_≅_ {{P}} a b))

instance
  underlying-type-of-category : {𝓤 𝓥 : Universe}
                              → Underlying-Type (Category 𝓤 𝓥) (Precategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-type-of-category}} (P , _) = P


id-equiv-iso : (C : Category 𝓤 𝓥)
             → ((a b : obj ⟨ C ⟩)
             → (a ＝ b) ≃ (_≅_ {{⟨ C ⟩}} a b))
id-equiv-iso C = pr₂ C

\end{code}

We can now show that the objects of any category is a 1-type. This is because
equality between objects is exactly isomorphism, which we know is a set.

\begin{code}

cat-objs-are-1-types : (A : Category 𝓤 𝓥) → (a b : obj ⟨ A ⟩) → is-set (a ＝ b)
cat-objs-are-1-types A a b = equiv-to-set (id-equiv-iso A a b)
                                       (isomorphisms-are-sets {{⟨ A ⟩}})
\end{code}

