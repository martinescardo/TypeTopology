Anna Williams, 17 October 2025

Definitions of:
 * precategory
 * category

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)

open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties

module Categories.Category where

\end{code}

We start by defining the notion of a precategory.
This consists of the usual components of a category, which is as follows

- A collection of objects, obj
- For each pair of objects, A B : obj, a set of homorphisms between A and B
- For each object A : obj, an identity homorphism (id A) : hom A A
- A composition operation, ∘, which for objects A B C : obj
  and homorphisms f : hom A B, g : hom B C gives a new homomorphism in hom A C

with the following axioms

- left-id: For objects A B : obj and morphism f : hom A B, f = f ∘ (id A)
- right-id: For objects A B : obj and morphism f : hom A B, f = (id B) ∘ f
- associativity: For objects A B C D : obj and morphisms f : hom A B,
                 g : hom B C, h : hom C D, we have f ∘ (g ∘ h) = (f ∘ g) ∘ h

\begin{code}

record Precategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
  hom-is-set : {a b : obj} → is-set (hom a b)
  
  id : (a : obj) → hom a a
  
  _∘_ : {a b c : obj} → hom b c → hom a b → hom a c
  
  left-id : {a b : obj} → (f : hom a b) → f ＝ (id b) ∘ f
  
  right-id : {a b : obj} → (f : hom a b) → f ＝ f ∘ (id a)
  
  assoc
   : {a b c d : obj}
     {f : hom a b}
     {g : hom b c}
     {h : hom c d}
   → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
\end{code}

We define instance argument versions of each field of the record so, for
example, we can write f ∘ g, to mean _∘_ P f g, for a precategory P.

\begin{code}

obj : (P : Precategory 𝓤 𝓥) → 𝓤 ̇
obj = Precategory.obj

hom : {{ P : Precategory 𝓤 𝓥 }} (a b : obj P) → 𝓥 ̇ 
hom {{P}} = Precategory.hom P

_∘_ : {{ P : Precategory 𝓤 𝓥 }} {a b c : obj P} → hom b c → hom a b → hom a c
_∘_ {{P}} = Precategory._∘_ P

id : {{ P : Precategory 𝓤 𝓥 }} {a : obj P} → hom a a
id {{P}} {a} = Precategory.id P a

hom-is-set : {{ P : Precategory 𝓤 𝓥 }} {a b : obj P} → is-set (hom a b)
hom-is-set {{P}} = Precategory.hom-is-set P

left-id
 : {{ P : Precategory 𝓤 𝓥 }} {a b : obj P} → (f : hom a b) → f ＝ id ∘ f
left-id {{P}} = Precategory.left-id P

right-id
 : {{ P : Precategory 𝓤 𝓥 }} {a b : obj P} → (f : hom a b) → f ＝ f ∘ id
right-id {{P}} = Precategory.right-id P

assoc
 : {{ P : Precategory 𝓤 𝓥 }}
   {a b c d : obj P}
   {f : hom a b}
   {g : hom b c}
   {h : hom c d}
 → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
assoc {{P}} = Precategory.assoc P

\end{code}

An isomorphism in a category consists of a homomorphism f : hom a b
and some "inverse" homomorphism g : hom b a, such that g ∘ f = (id a)
and f ∘ g = (id b).

We first define the type of a given homomorphism being an isomorphism,
then we define the type of isomorphism between objects of a precategory.

\begin{code}

record Is-Iso {{ P : Precategory 𝓤 𝓥 }} {a b : obj P} (f : hom a b) : 𝓥 ̇ where
 field
  inv : hom b a
  l-inverse : inv ∘ f ＝ id
  r-inverse : f ∘ inv ＝ id

Cat-Iso : {{ P : Precategory 𝓤 𝓥 }} (a b : obj P) → 𝓥 ̇
Cat-Iso a b = Σ f ꞉ hom a b , Is-Iso f

\end{code}

We now show that for a given homomorphism, being an isomorphism is a
(mere) proposition. We argue that inverses are unique, and then since
the type of homomorphisms between two objects is a set, equality between
any two homomorphisms is a proposition, so our left and right inverse
equalities are a proposition.

\begin{code}

-- This might want cleaning up
-- I feel there is probably a better way of doing this
is-iso-eq
 : {{P : Precategory 𝓤 𝓥}} {a b : obj P} {f : hom {{P}} a b} → (x y : Is-Iso f)
 → (Is-Iso.inv x) ＝ (Is-Iso.inv y)
 → x ＝ y
is-iso-eq x y refl = ap₂ p-record l-eq r-eq
 where
  l-eq : Is-Iso.l-inverse x ＝ Is-Iso.l-inverse y
  l-eq = hom-is-set (Is-Iso.l-inverse x) (Is-Iso.l-inverse y)

  r-eq : Is-Iso.r-inverse x ＝ Is-Iso.r-inverse y
  r-eq = hom-is-set (Is-Iso.r-inverse x) (Is-Iso.r-inverse y)

  p-record = λ l-in r-in → record { inv = Is-Iso.inv x ;
                                    l-inverse = l-in ;
                                    r-inverse = r-in }


specific-iso-is-prop
 : {{P : Precategory 𝓤 𝓥}}
   {a b : obj P}
 → (f : hom a b)
 → is-prop (Is-Iso f)
specific-iso-is-prop {_} {_} {a} {b} f x y = is-iso-eq x y inverse-eq
 where
  g : hom b a
  g = Is-Iso.inv x

  g' : hom b a
  g' = Is-Iso.inv y

  inverse-eq : Is-Iso.inv x ＝ Is-Iso.inv y
  inverse-eq = g            ＝⟨ right-id g ⟩
               g ∘ id       ＝⟨ ap (g ∘_) ((Is-Iso.r-inverse y)⁻¹) ⟩
               g ∘ (f ∘ g') ＝⟨ assoc ⟩
               (g ∘ f) ∘ g' ＝⟨ ap (_∘ g') (Is-Iso.l-inverse x) ⟩
               id ∘ g'      ＝⟨ (left-id g')⁻¹ ⟩
               g' ∎

\end{code}

We now argue that this means that the type of isomorphisms is a set.
This follows from the fact that being an isomorphism is a proposition.

\begin{code}

isomorphism-is-set
 : {{P : Precategory 𝓤 𝓥}}
   {a b : obj P}
 → is-set (Cat-Iso a b)
isomorphism-is-set = Σ-is-set hom-is-set
                              (λ f → props-are-sets (specific-iso-is-prop f))

\end{code}

We wish to combine the similar notions of equivalence,
namely the internal equality: a = b and isomorphisms a ≅ b.

We can in fact show that if a = b, then a ≅ b. This is because if
a = b, then by path induction we need to show that a ≅ a. This is
simple as we can form an isomophism with the identity homomorphism.

\begin{code}

id-to-iso : {{ A : Precategory 𝓤 𝓥 }} (a b : obj A) → a ＝ b → Cat-Iso a b
id-to-iso a b refl = id , record { inv = id ;
                                   l-inverse = id-squared-is-id ;
                                   r-inverse = id-squared-is-id }
 where
  id-squared-is-id : id ∘ id ＝ id
  id-squared-is-id = (left-id id)⁻¹

\end{code}

To bring into alignment the two different forms of equality, we define a
category to be a precategory where equality is exactly isomorphism.

\begin{code}

record Category (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇  where
 field
  precategory : Precategory 𝓤 𝓥
  id-equiv-iso : (a b : obj precategory) → (a ＝ b) ≃ Cat-Iso ⦃ precategory ⦄ a b

_ₚ : Category 𝓤 𝓥 → Precategory 𝓤 𝓥
_ₚ = Category.precategory

\end{code}

We can now show that any category's objects are sets. This is because
equality between objects is exactly isomorphism, which we know is a set.

\begin{code}

cat-obj-is-1-type : (A : Category 𝓤 𝓥) → (a b : obj (A ₚ)) → is-set (a ＝ b)
cat-obj-is-1-type A a b = equiv-to-set (Category.id-equiv-iso A a b)
                                       (isomorphism-is-set {{A ₚ}})
\end{code}

