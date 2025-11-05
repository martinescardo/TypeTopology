Anna Williams, 17 October 2025

Definitions of:
 * precategory
 * category

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import Notation.UnderlyingType
open import UF.Base
open import UF.Embeddings
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module Categories.Type (fe : Fun-Ext) where

\end{code}

We start by defining the notion of a wild category.
This consists of the usual components of a (set theoretic) category,
which is as follows:

- A collection of objects, obj
- For each pair of objects, A B : obj, a type of homorphism between A and B
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

record WildCategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇  where
 constructor make
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
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

open WildCategory {{...}} public hiding (obj)

obj : (W : WildCategory 𝓤 𝓥) → 𝓤 ̇
obj = WildCategory.obj

wildcat-comp : (W : WildCategory 𝓤 𝓥)
          {a b c : obj W}
          → hom {{W}} b c
          → hom {{W}} a b
          → hom {{W}} a c
wildcat-comp W g f = _∘_{{W}} g f

syntax wildcat-comp P g f = g ∘⟨ P ⟩ f

infixl 5 wildcat-comp

\end{code}

An isomorphism in a category consists of a homomorphism f : hom a b
and some "inverse" homomorphism g : hom b a, such that g ∘ f = (id a)
and f ∘ g ＝ (id b).

We first define the type of a given homomorphism being an isomorphism,
then we define the type of isomorphism between objects of a wild category.

\begin{code}

is-iso : {{ W : WildCategory 𝓤 𝓥 }} {a b : obj W} (f : hom a b) → 𝓥 ̇ 
is-iso {_} {_} {a} {b} f = Σ inv ꞉ hom b a , (inv ∘ f ＝ id) × (f ∘ inv ＝ id)

inv : {{ W : WildCategory 𝓤 𝓥 }}
      {a b : obj W}
      {f : hom a b}
    → is-iso f
    → hom b a
inv iso = pr₁ iso

l-inverse : {{ W : WildCategory 𝓤 𝓥 }}
            {a b : obj W}
            {f : hom {{W}} a b}
            (iso : is-iso f)
          → (inv iso) ∘ f ＝ id 
l-inverse iso = pr₁ (pr₂ iso)

r-inverse : {{ W : WildCategory 𝓤 𝓥 }}
            {a b : obj W}
            {f : hom a b}
            (iso : is-iso f)
          → f ∘ (inv iso) ＝ id
r-inverse iso = pr₂ (pr₂ iso)

is-inverse : {{ W : WildCategory 𝓤 𝓥 }}
            {a b : obj W}
            {f : hom a b}
            (iso : is-iso f)
          → ((inv iso) ∘ f ＝ id) × (f ∘ (inv iso) ＝ id)
is-inverse = pr₂

mk-iso : {{ W : WildCategory 𝓤 𝓥 }}
         {a b : obj W}
         {f : hom a b}
         (inv : hom b a)
       → (inv ∘ f ＝ id)
       → (f ∘ inv ＝ id)
       → is-iso f
mk-iso inv l-id r-id = (inv , l-id , r-id)

_≅_ : {{ W : WildCategory 𝓤 𝓥 }} (a b : obj W) → 𝓥 ̇
a ≅ b = Σ f ꞉ hom a b , is-iso f

wildcat-iso : (W : WildCategory 𝓤 𝓥)
              (a b : obj W)
            → 𝓥 ̇
wildcat-iso W a b = _≅_ {{W}} a b

syntax wildcat-iso W a b = a ≅⟨ W ⟩ b

\end{code}

We now define the notion of a precategory

\begin{code}

is-precategory : (W : WildCategory 𝓤 𝓥) → (𝓤 ⊔ 𝓥) ̇
is-precategory W = (a b : obj W) → is-set (hom {{W}} a b)

being-precategory-is-prop : (W : WildCategory 𝓤 𝓥) → is-prop (is-precategory W)
being-precategory-is-prop W p q = Π-is-prop fe
                                   (λ a → Π-is-prop fe
                                    (λ b → being-set-is-prop fe)) _ _

Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Precategory 𝓤 𝓥 = Σ W ꞉ WildCategory 𝓤 𝓥 , is-precategory W

\end{code}

We also define the corresponding projections from a precategory.

\begin{code}

instance
  underlying-wildcategory-of-precategory
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Precategory 𝓤 𝓥) (WildCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-wildcategory-of-precategory}} (P , _) = P

hom-is-set : {{P : Precategory 𝓤 𝓥}}
             {a b : obj ⟨ P ⟩}
           → is-set (hom {{⟨ P ⟩}} a b)
hom-is-set {{_ , p}} {a} {b} = p a b

\end{code}

We now show that for a given homomorphism, being an isomorphism is a
(mere) proposition. We argue that inverses are unique, and then since
the type of homomorphisms between two objects is a set, equality between
any two homomorphisms is a proposition, so our left and right inverse
equalities are a proposition.

\begin{code}

inv-is-lc : {{P : Precategory 𝓤 𝓥}}
            {a b : obj ⟨ P ⟩}
            {f : hom {{⟨ P ⟩}} a b}
            (x y : is-iso {{⟨ P ⟩}} f)
          → inv {{⟨ P ⟩}} x ＝ inv {{⟨ P ⟩}} y
          → x ＝ y
inv-is-lc {{P}} x y refl = ap₂ (mk-iso {{⟨ P ⟩}} (inv {{⟨ P ⟩}} x)) l-eq r-eq
 where
  l-eq : l-inverse {{⟨ P ⟩}} x ＝ l-inverse {{⟨ P ⟩}} y
  l-eq = hom-is-set (l-inverse {{⟨ P ⟩}} x) (l-inverse {{⟨ P ⟩}} y)

  r-eq : r-inverse {{⟨ P ⟩}} x ＝ r-inverse {{⟨ P ⟩}} y
  r-eq = hom-is-set (r-inverse {{⟨ P ⟩}} x) (r-inverse {{⟨ P ⟩}} y)

being-iso-is-prop : {{P : Precategory 𝓤 𝓥}}
                    {a b : obj ⟨ P ⟩}
                    (f : hom {{⟨ P ⟩}} a b)
                  → is-prop (is-iso {{⟨ P ⟩}} f)
being-iso-is-prop {{P}} {a} {b} f x y = inv-is-lc x y inverse-eq
 where  
  inverse-eq : inv {{⟨ P ⟩}} x ＝ inv {{⟨ P ⟩}} y
  inverse-eq = x⁻¹                               ＝⟨ i ⟩
               x⁻¹ ∘⟨ ⟨ P ⟩ ⟩ (id {{⟨ P ⟩}})     ＝⟨ ii ⟩
               x⁻¹ ∘⟨ ⟨ P ⟩ ⟩ (f ∘⟨ ⟨ P ⟩ ⟩ y⁻¹) ＝⟨ iii ⟩
               (x⁻¹ ∘⟨ ⟨ P ⟩ ⟩ f) ∘⟨ ⟨ P ⟩ ⟩ y⁻¹ ＝⟨ iv ⟩
               (id {{⟨ P ⟩}}) ∘⟨ ⟨ P ⟩ ⟩ y⁻¹     ＝⟨ v ⟩
               y⁻¹ ∎
   where
    x⁻¹ = inv {{⟨ P ⟩}} x
    y⁻¹ = inv {{⟨ P ⟩}} y

    i = (right-id {{⟨ P ⟩}} x⁻¹)⁻¹
    ii = ap (λ y → x⁻¹ ∘⟨ ⟨ P ⟩ ⟩ y) ((r-inverse {{⟨ P ⟩}} y)⁻¹)
    iii = assoc {{⟨ P ⟩}}
    iv = ap (λ x → x ∘⟨ ⟨ P ⟩ ⟩ y⁻¹) (l-inverse {{⟨ P ⟩}} x)
    v = left-id {{⟨ P ⟩}} y⁻¹

\end{code}

We now argue that this means that the type of isomorphisms is a set.
This follows from the fact that being an isomorphism is a proposition.

\begin{code}

isomorphism-type-is-set : {{P : Precategory 𝓤 𝓥}}
                          {a b : obj ⟨ P ⟩}
                        → is-set (a ≅⟨ ⟨ P ⟩ ⟩ b)
isomorphism-type-is-set {{P}} = Σ-is-set hom-is-set
                                 (λ f → props-are-sets (being-iso-is-prop f))

\end{code}

We wish to combine the similar notions of equivalence,
namely the internal equality: a ＝ b and isomorphisms a ≅ b.

We can in fact show that if a ＝ b, then a ≅ b. This is because if
a ＝ b, then by path induction we need to show that a ≅ a. This is
simple as we can form an isomophism with the identity homomorphism.

\begin{code}

id-to-iso : {{ P : Precategory 𝓤 𝓥 }}
            (a b : obj ⟨ P ⟩ )
          → a ＝ b
          → a ≅⟨ ⟨ P ⟩ ⟩ b
id-to-iso {{P}} a b refl = id {{⟨ P ⟩}} , iso
 where
  iso : is-iso {{⟨ P ⟩}} (id {{⟨ P ⟩}})
  iso = (mk-iso {{⟨ P ⟩}} (id {{⟨ P ⟩}}) id-comp-id-is-id id-comp-id-is-id)
   where
    id-comp-id-is-id : id {{⟨ P ⟩}} ∘⟨ ⟨ P ⟩ ⟩ id {{⟨ P ⟩}} ＝ id {{⟨ P ⟩}}
    id-comp-id-is-id = left-id {{⟨ P ⟩}} (id {{⟨ P ⟩}})
\end{code}

To bring into alignment the two different forms of equality, we define a
category to be a precategory where identification is equivalent to isomorphism.

\begin{code}

is-category : (P : Precategory 𝓤 𝓥) → (𝓤 ⊔ 𝓥) ̇ 
is-category P = (a b : obj ⟨ P ⟩) → is-equiv (id-to-iso {{P}} a b)

being-category-is-prop : (P : Precategory 𝓤 𝓥) → is-prop (is-category P)
being-category-is-prop P x y = Π-is-prop fe (λ x → Π-is-prop fe (I x)) _ _
 where
  I : (a b : obj ⟨ P ⟩) → is-prop (is-equiv (id-to-iso {{P}} a b))
  I a b e e' = being-equiv-is-prop (λ x y → fe {x} {y})
                                    (id-to-iso {{P}} a b) e e'

Category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Category 𝓤 𝓥 = Σ P ꞉ Precategory 𝓤 𝓥 , is-category P

\end{code}

Projections from category.

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
id-to-iso-is-equiv C = pr₂ C

\end{code}

We can now show that the objects of any category is a 1-type. This is because
equality between objects is exactly isomorphism, which we know is a set.

\begin{code}

cat-objs-are-1-types : (A : Category 𝓤 𝓥) → (a b : obj ⟨ A ⟩) → is-set (a ＝ b)
cat-objs-are-1-types A a b = equiv-to-set id-equiv-iso
                                          (isomorphism-type-is-set {{⟨ A ⟩}})
 where
  id-equiv-iso : (a ＝ b) ≃ (a ≅⟨ ⟨ A ⟩ ⟩ b)
  id-equiv-iso = id-to-iso {{⟨ A ⟩}} a b , id-to-iso-is-equiv A a b

\end{code}
