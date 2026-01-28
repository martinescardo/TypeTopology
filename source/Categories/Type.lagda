Anna Williams, 17 October 2025

Definitions of
 * wild category,
 * precategory, and
 * category.

We follow the naming conventions of the HoTT Book. The properties of the
different types of category are given in the table below.

[[Add full reference to the HoTT Book, like HoTT Book [1], and the add the full reference
from here https://homotopytypetheory.org/book/]]


                ┌──────┬──────┬────────────┐
                │ obj  │ hom  │ univalence │
┌───────────────┼──────┼──────┼────────────┤
│ wild-category │ type │ type │ no         │
├───────────────┼──────┼──────┼────────────┤
│ pre-category  │ type │ set  │ no         │
├───────────────┼──────┼──────┼────────────┤
│ category      │ type │ set  │ yes        │
└───────────────┴──────┴──────┴────────────┘

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id) -- [[Alternatively, use ○ (\ci2). Another thing I've done is to use a different fond for "id", e.g. 𝓲𝓭. Probably things are fine like you have, for now.]]
open import Notation.UnderlyingType
open import UF.Base
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module Categories.Type where

\end{code}

We start by defining a wild category. This consists of the usual components of a
category, which is as follows.

[[I think it will be easier to read the following if you add a blank line between the items.]]

* A collection of objects, obj,
* for each pair of objects, A B : obj, a homomorphism between A and B, hom A B,
* for each object A : obj, an identity homomorphism id A : hom A A, and
* a composition operation, ∘, which for objects A B C : obj and homomorphisms
  f : hom A B, g : hom B C gives a new homomorphism, g ∘ f : hom A C.

Such that the following axioms hold.

* left-id: for objects A B : obj and morphism f : hom A B, f ∘ id ＝ f,
* right-id: for objects A B : obj and morphism f : hom A B, id ∘ f ＝ f, and
* associativity: for objects A B C D : obj and morphisms f : hom A B,
                 g : hom B C, h : hom C D, h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f.

[[Perhaps give the following reference for wild category.
https://arxiv.org/abs/1707.03693]]

\begin{code}

record WildCategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇  where
 constructor wildcat-make
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
  id : {a : obj} → hom a a

  _∘_ : {a b c : obj} → hom b c → hom a b → hom a c

  left-id : {a b : obj} (f : hom a b) → id ∘ f ＝ f  -- [[id-is-left-neutral.]]

  right-id : {a b : obj} (f : hom a b) → f ∘ id ＝ f -- [[Similar.]]

  assoc : {a b c d : obj}
          (f : hom a b)
          (g : hom b c)
          (h : hom c d)
        → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f

\end{code}

We can now define the property of being a precategory. This is exactly a wild
category where the homs are sets. We define precategories later (outside of the
record).

\begin{code}

 is-precategory : (𝓤 ⊔ 𝓥) ̇
 is-precategory = (a b : obj) → is-set (hom a b)

 being-precat-is-prop : (fe : Fun-Ext)
                      → is-prop (is-precategory)
 being-precat-is-prop fe = Π₂-is-prop fe (λ _ _ → being-set-is-prop fe)

\end{code}

An isomorphism in a category consists of a homomorphism, f : hom a b, and some
"inverse" homomorphism, g : hom b a, such that g ∘ f = id and f ∘ g ＝ id.

[[Perhaps use *inverse* which will eventually render as italics when we use markdown in the future.]]

We first define the property of being an isomorphism and then define the type of
isomorphisms between objects of a wild category.

\begin{code}

 is-iso : {a b : obj} (f : hom a b) → 𝓥 ̇
 is-iso {a} {b} f = Σ inv ꞉ hom b a , (inv ∘ f ＝ id) × (f ∘ inv ＝ id)
            -- [[   Σ f⁻¹ ꞉ hom b a , (f⁻¹ ∘ f ＝ id) × (f ∘ f⁻¹ ＝ id) ]]

 inv : {a b : obj}   -- [[We will try to get this to be _⁻¹.]] [[Maybe just hide ⁻¹ for now and use it.]] [[Or
       {f : hom a b}
     → is-iso f
     → hom b a
 inv = pr₁

 l-inv : {a b : obj}   -- [[We need as better name. E.g. `⁻¹-is-left-inverse` ]]
         {f : hom a b}
         (iso : is-iso f)
       → inv iso ∘ f ＝ id
 l-inv iso = pr₁ (pr₂ iso)

 r-inv : {a b : obj}  -- [[Similarly.]]
         {f : hom a b}
         (iso : is-iso f)
       → f ∘ inv iso ＝ id
 r-inv iso = pr₂ (pr₂ iso)

 _≅_ : (a b : obj) → 𝓥 ̇
 a ≅ b = Σ f ꞉ hom a b , is-iso f

 iso : {a b : obj} -- [[Maybe: `underlying-morphism`.]]
     → a ≅ b
     → hom a b
 iso = pr₁

 isomorphism-proof : {a b : obj} -- [[underlying-morphism-is-isomorphism.]]
                     (f : a ≅ b)
                   → Σ g ꞉ hom b a , (g ∘ iso f ＝ id) × (iso f ∘ g ＝ id)
 isomorphism-proof = pr₂

\end{code}

We can show that two inverses for a given isomorphism must be equal.

\begin{code}

 inverse-eq : {a b : obj} --[[at-most-one-inverse]]
              {f : hom a b}
              (x y : is-iso f)
            → inv x ＝ inv y
 inverse-eq {a} {b} {f} x y = inv x               ＝⟨ i ⟩
                              inv x ∘ id          ＝⟨ ii ⟩
                              inv x ∘ (f ∘ inv y) ＝⟨ iii ⟩
                              (inv x ∘ f) ∘ inv y ＝⟨ iv ⟩
                              id ∘ inv y          ＝⟨ v ⟩
                              inv y               ∎
  where
   i   = (right-id (inv x))⁻¹
   ii  = ap (inv x ∘_) (r-inv y)⁻¹
   iii = assoc _ _ _
   iv  = ap (_∘ inv y) (l-inv x)
   v   = left-id (inv y)

\end{code}

We can easily show that if a ＝ b, then a ≅ b. This is because if a ＝ b, then
by path induction we need to show that a ≅ a. This can be constructed as
follows.

\begin{code}

 id-comp-id-is-id : {a : obj} → id ∘ id ＝ id {a}
 id-comp-id-is-id = left-id id

 id-to-iso : (a b : obj)
           → a ＝ b
           → a ≅ b
 id-to-iso a b refl = id , id , id-comp-id-is-id , id-comp-id-is-id

\end{code}

We wish to combine the similar notions of equivalence, namely the internal
equality: a ＝ b and isomorphisms a ≅ b.

To bring into alignment the two different forms of equality, we define the
property of being a category, where identification is equivalent to isomorphism.
That is the above map is an equivalence. We define category outside of the
record similarly to precategory.

\begin{code}

 is-category : (𝓤 ⊔ 𝓥) ̇
 is-category = (a b : obj) → is-equiv (id-to-iso a b)

 being-cat-is-prop : (fe : Fun-Ext)
                   → is-prop (is-category)
 being-cat-is-prop fe x y = Π₂-is-prop fe I _ _
  where
   I : (a b : obj) → is-prop (is-equiv (id-to-iso a b))
   I a b = being-equiv-is-prop (λ x y → fe {x} {y}) (id-to-iso a b)

\end{code}

We define an object notation such that we can write obj W, obj P and obj C where
W, P and C are wild categories, precategories and categories respectively.

This works similarly to the method used in Notation.UnderlyingType.

\begin{code}

open WildCategory public using (is-precategory ; being-precat-is-prop
                               ; is-category ; being-cat-is-prop)


-- {- [[We usually to the above like this:]]

open WildCategory public using
                          (is-precategory
                         ; being-precat-is-prop
                         ; is-category
                         ; being-cat-is-prop)

-}


record OBJ {𝓤} {𝓥} (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇  where
 field
  obj : A → B

open OBJ {{...}} public

instance
 wildcatobj : {𝓤 𝓥 : Universe} → OBJ (WildCategory 𝓤 𝓥) (𝓤 ̇ )
 obj {{wildcatobj}} = WildCategory.obj

\end{code}

We now define some notation for categories. This way, if we are working with
wild categories C and D. We can simply write "open CategoryNotation C" and
"open CategoryNotation D" to have all operations available.

This works similarly to Notation.UnderlyingType, where we define records for
each different field. We then define instances of each of the fields we want
specific to the wild category used as input.

\begin{code}

module _ {𝓤 𝓥 : Universe} (W : WildCategory 𝓤 𝓥) where
 record HOM : 𝓤 ⊔ (𝓥 ⁺) ̇ where -- [[Remove round brackets. Then swap the universes.]]
  field
   hom : obj W → obj W → 𝓥 ̇

 open HOM {{...}} public

 instance
  defnhom : HOM
  hom {{defnhom}} = WildCategory.hom W

 record ID : 𝓤 ⊔ (𝓥 ⁺) ̇ where -- [[Same.]]
  field
   id : {a : obj W} → hom a a

 open ID {{...}} public

 instance
  defnid : ID
  id {{defnid}} = WildCategory.id W

 record COMP : 𝓤 ⊔ 𝓥 ̇  where
  field
   _∘_ : {a b c : obj W}
       → hom b c
       → hom a b
       → hom a c

 open COMP {{...}} public

 instance
  comp : COMP
  _∘_ {{comp}} = WildCategory._∘_ W

 record CATNotation : 𝓤 ⊔ (𝓥 ⁺) ̇  where
  field
   left-id : {a b : obj W} (f : hom a b) -- [[Perhaps separate type signature with blank lines for readability.]]
           → id ∘ f ＝ f
   right-id : {a b : obj W} (f : hom a b)
            → f ∘ id ＝ f
   assoc : {a b c d : obj W}
           (f : hom a b)
           (g : hom b c)
           (h : hom c d)
         → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
   is-iso : {a b : obj W} (f : hom a b) → 𝓥 ̇
   inv : {a b : obj W}
         {f : hom a b}
       → is-iso f
       → hom b a
   l-inv : {a b : obj W}
           {f : hom a b}
           (iso : is-iso f)
         → inv iso ∘ f ＝ id
   r-inv : {a b : obj W} {f : hom a b}
           (iso : is-iso f)
         → f ∘ inv iso ＝ id
   inverse-eq : {a b : obj W} {f : hom a b}
                (x y : is-iso f)
              → inv x ＝ inv y
   _≅_ : (a b : obj W) → 𝓥 ̇
   iso : {a b : obj W}
       → a ≅ b
       → hom a b
   isomorphism-proof : {a b : obj W}
                       (f : a ≅ b)
                     → Σ g ꞉ hom b a , (g ∘ iso f ＝ id) × (iso f ∘ g ＝ id)
   id-to-iso : (a b : obj W)
             → a ＝ b
             → a ≅ b

 open CATNotation {{...}} public

module CategoryNotation {𝓤 𝓥 : Universe} (W : WildCategory 𝓤 𝓥) where
 instance
  wildcathomnotation : HOM W
  hom {{wildcathomnotation}} = WildCategory.hom W

  wildcatidnotation : ID W
  id {{wildcatidnotation}} = WildCategory.id W

  wildcatcompnotation : COMP W
  _∘_ {{wildcatcompnotation}} = WildCategory._∘_ W

  wildcatnotation : CATNotation W
  left-id {{wildcatnotation}} = WildCategory.left-id W
  right-id {{wildcatnotation}} = WildCategory.right-id W
  assoc {{wildcatnotation}} = WildCategory.assoc W
  is-iso {{wildcatnotation}} = WildCategory.is-iso W
  inv {{wildcatnotation}} = WildCategory.inv W
  l-inv {{wildcatnotation}} = WildCategory.l-inv W
  r-inv {{wildcatnotation}} = WildCategory.r-inv W
  inverse-eq {{wildcatnotation}} = WildCategory.inverse-eq W
  _≅_ {{wildcatnotation}} = WildCategory._≅_ W
  iso {{wildcatnotation}} = WildCategory.iso W
  isomorphism-proof {{wildcatnotation}} = WildCategory.isomorphism-proof W
  id-to-iso {{wildcatnotation}} = WildCategory.id-to-iso W

\end{code}

We now define the notion of a precategory.

\begin{code}

Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Precategory 𝓤 𝓥 = Σ W ꞉ WildCategory 𝓤 𝓥 , WildCategory.is-precategory W -- [[From Anna. Shorten.]]

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
 open CategoryNotation ⟨ P ⟩

 inv-is-lc : {a b : obj P} -- [[`⁻¹-is-lc` will be bad. `inverses-are-lc`]]
             {f : hom a b}
             (x y : is-iso f)
           → inv x ＝ inv y
           → x ＝ y
 inv-is-lc x y refl = ap₂ (λ l r → inv x , l , r) l-eq r-eq
  where
   l-eq : l-inv x ＝ l-inv y
   l-eq = hom-is-set P (l-inv x) (l-inv y)

   r-eq : r-inv x ＝ r-inv y
   r-eq = hom-is-set P (r-inv x) (r-inv y)

 being-iso-is-prop : {a b : obj ⟨ P ⟩}
                     (f : hom a b)
                   → is-prop (is-iso f)
 being-iso-is-prop f x y = inv-is-lc x y (inverse-eq x y)

\end{code}

Following this, we can see that the type of isomorphisms is a set.

\begin{code}

 isomorphism-type-is-set : {a b : obj ⟨ P ⟩}
                         → is-set (a ≅ b)
 isomorphism-type-is-set = Σ-is-set (hom-is-set P)
                                    (λ f → props-are-sets (being-iso-is-prop f))

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

-- [[Perhaps: `cat-objs-form-a-1-type`.]]

cat-objs-are-1-types : (A : Category 𝓤 𝓥) → (a b : obj A) → is-set (a ＝ b)
cat-objs-are-1-types A a b = equiv-to-set id-equiv-iso
                                          (isomorphism-type-is-set ⟨ A ⟩)
 where
  open CategoryNotation ⟨ A ⟩
  id-equiv-iso : (a ＝ b) ≃ a ≅ b
  id-equiv-iso = id-to-iso a b , id-to-iso-is-equiv A a b

\end{code}

[[Perhaps split this into four files:

   * Categories.Wild
   * Categories.Pre
   * Categories.Type     -- Is there a better name? Don't call it Categories.Category
   * Categories.Univalent
   * Categories.Notation -- As you say, nobody really will be tempted to understand this one.
]]
