Anna Williams, 17 October 2025

Definitions of:
 * wild category
 * pre category
 * category

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
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

We start by defining the notion of a wild category.
This consists of the usual components of a category,
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
 constructor wildcat-make
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
  id : {a : obj} → hom a a
  
  _∘_ : {a b c : obj} → hom b c → hom a b → hom a c
  
  left-id : {a b : obj} → (f : hom a b) → id ∘ f ＝ f
  
  right-id : {a b : obj} → (f : hom a b) → f ∘ id ＝ f
  
  assoc : {a b c d : obj}
          (f : hom a b)
          (g : hom b c)
          (h : hom c d)
        → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f

\end{code}

We add instance argument versions of each field, apart from
obj, which we make explicit. We also add a syntax definition
for composition where the precategory cannot be inferred.

\begin{code}

open WildCategory {{...}} public hiding (obj)

obj : (W : WildCategory 𝓤 𝓥) → 𝓤 ̇
obj = WildCategory.obj

wildcat-comp-explicit : (W : WildCategory 𝓤 𝓥)
          {a b c : obj W}
          → hom {{W}} b c
          → hom {{W}} a b
          → hom {{W}} a c
wildcat-comp-explicit W g f = _∘_{{W}} g f

syntax wildcat-comp-explicit P g f = g ∘⟨ P ⟩ f

infixr 5 wildcat-comp-explicit

wildcat-comp : {{W : WildCategory 𝓤 𝓥}}
               {a b c : obj W}
             → hom b c
             → hom a b
             → hom a c
wildcat-comp g f = g ∘ f

infixr 5 wildcat-comp

\end{code}

An isomorphism in a category consists of a homomorphism f : hom a b
and some "inverse" homomorphism g : hom b a, such that g ∘ f = (id a)
and f ∘ g ＝ (id b).

We first define the property of being an isomorphism and then define
the type of isomorphisms between objects of a wild category.

\begin{code}

is-iso : {{ W : WildCategory 𝓤 𝓥 }} {a b : obj W} (f : hom a b) → 𝓥 ̇ 
is-iso {_} {_} {a} {b} f = Σ inv ꞉ hom b a , (inv ∘ f ＝ id) × (f ∘ inv ＝ id)

inv : {{ W : WildCategory 𝓤 𝓥 }}
      {a b : obj W}
      {f : hom a b}
    → is-iso f
    → hom b a
inv iso = pr₁ iso

l-inv : {{ W : WildCategory 𝓤 𝓥 }}
            {a b : obj W}
            {f : hom {{W}} a b}
            (iso : is-iso f)
          → inv iso ∘ f ＝ id 
l-inv iso = pr₁ (pr₂ iso)

r-inv : {{ W : WildCategory 𝓤 𝓥 }}
            {a b : obj W}
            {f : hom a b}
            (iso : is-iso f)
          → f ∘ inv iso ＝ id
r-inv iso = pr₂ (pr₂ iso)

_≅_ : {{ W : WildCategory 𝓤 𝓥 }} (a b : obj W) → 𝓥 ̇
a ≅ b = Σ f ꞉ hom a b , is-iso f

wildcat-iso-explicit : (W : WildCategory 𝓤 𝓥)
              (a b : obj W)
            → 𝓥 ̇
wildcat-iso-explicit W a b = _≅_ {{W}} a b

syntax wildcat-iso-explicit W a b = a ≅⟨ W ⟩ b

\end{code}

We can now define the notion of a precategory. This is a wild category
where the type homomorphisms between two objects is a set. This can be
shown to be a proposition.

\begin{code}

is-precategory : (W : WildCategory 𝓤 𝓥) → (𝓤 ⊔ 𝓥) ̇
is-precategory W = (a b : obj W) → is-set (hom {{W}} a b)

being-precat-is-prop : (fe : Fun-Ext)
                       (W : WildCategory 𝓤 𝓥)
                     → is-prop (is-precategory W)
being-precat-is-prop fe W p q = Π-is-prop fe
                                 (λ a → Π-is-prop fe
                                  (λ b → being-set-is-prop fe)) _ _

PreCategory : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
PreCategory 𝓤 𝓥 = Σ W ꞉ WildCategory 𝓤 𝓥 , is-precategory W

\end{code}

We also define the corresponding projections from a precategory.

\begin{code}

instance
  underlying-wildcategory-of-precategory
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (PreCategory 𝓤 𝓥) (WildCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-wildcategory-of-precategory}} (P , _) = P

hom-is-set : {{P : PreCategory 𝓤 𝓥}}
             {a b : obj ⟨ P ⟩}
           → is-set (hom {{⟨ P ⟩}} a b)
hom-is-set {{_ , p}} {a} {b} = p a b

\end{code}

We now show that in a precategory, for any given homomorphism, being an
isomorphism is a (mere) proposition. We argue that inverses are unique,
and then since the type of homomorphisms between two objects is a set,
equality between any two homomorphisms is a proposition, so our left and
right inverse equalities are a proposition.

\begin{code}

inv-is-lc : {{P : PreCategory 𝓤 𝓥}}
            {a b : obj ⟨ P ⟩}
            {f : hom {{⟨ P ⟩}} a b}
            (x y : is-iso {{⟨ P ⟩}} f)
          → inv {{⟨ P ⟩}} x ＝ inv {{⟨ P ⟩}} y
          → x ＝ y
inv-is-lc {{P}} x y refl = ap₂ (λ l r → inv {{⟨ P ⟩}} x , l , r) l-eq r-eq
 where
  l-eq : l-inv {{⟨ P ⟩}} x ＝ l-inv {{⟨ P ⟩}} y
  l-eq = hom-is-set (l-inv {{⟨ P ⟩}} x) (l-inv {{⟨ P ⟩}} y)

  r-eq : r-inv {{⟨ P ⟩}} x ＝ r-inv {{⟨ P ⟩}} y
  r-eq = hom-is-set (r-inv {{⟨ P ⟩}} x) (r-inv {{⟨ P ⟩}} y)

being-iso-is-prop : {{P : PreCategory 𝓤 𝓥}}
                    {a b : obj ⟨ P ⟩}
                    (f : hom {{⟨ P ⟩}} a b)
                  → is-prop (is-iso {{⟨ P ⟩}} f)
being-iso-is-prop {{P}} {a} {b} f x y = inv-is-lc x y (inverse-eq {{⟨ P ⟩}} x y)
 where  
  inverse-eq : {{W : WildCategory _ _}}
               {a b : obj W}
               {f : hom a b}
               (x y : is-iso f)
             → inv x ＝ inv y
  inverse-eq {{W}} {a} {b} {f} x y = inv x               ＝⟨ i ⟩
                                     inv x ∘ id          ＝⟨ ii ⟩
                                     inv x ∘ (f ∘ inv y) ＝⟨ iii ⟩
                                     (inv x ∘ f) ∘ inv y ＝⟨ iv ⟩
                                     id ∘ inv y          ＝⟨ v ⟩
                                     inv y               ∎
   where
    i   = (right-id (inv x))⁻¹
    ii  = ap (λ - → inv x ∘ -) (r-inv y)⁻¹
    iii = assoc _ _ _
    iv  = ap (λ - → - ∘ inv y) (l-inv x)
    v   = left-id (inv y)

\end{code}

Following this, we can see that the type of isomorphisms is a set.

\begin{code}

isomorphism-type-is-set : {{P : PreCategory 𝓤 𝓥}}
                          {a b : obj ⟨ P ⟩}
                        → is-set (a ≅⟨ ⟨ P ⟩ ⟩ b)
isomorphism-type-is-set {{P}} = Σ-is-set hom-is-set
                                 (λ f → props-are-sets (being-iso-is-prop f))

\end{code}

We wish to combine the similar notions of equivalence,
namely the internal equality: a ＝ b and isomorphisms a ≅ b.

We can in fact show that if a ＝ b, then a ≅ b. This is because if
a ＝ b, then by path induction we need to show that a ≅ a. This can
easily be constructed as follows. This map is typically called id-to-iso

\begin{code}

id-to-iso : {{ W : WildCategory 𝓤 𝓥 }}
            (a b : obj W )
          → a ＝ b
          → a ≅⟨ W ⟩ b
id-to-iso a b refl = id , (id , id-comp-id-is-id , id-comp-id-is-id)
 where
  id-comp-id-is-id : id ∘ id ＝ id
  id-comp-id-is-id = left-id id
\end{code}

To bring into alignment the two different forms of equality, we define a
category to be a precategory where identification is equivalent to isomorphism.
That is the above map is an equivalence.

\begin{code}

is-category : (P : PreCategory 𝓤 𝓥) → (𝓤 ⊔ 𝓥) ̇ 
is-category P = (a b : obj ⟨ P ⟩) → is-equiv (id-to-iso {{⟨ P ⟩}} a b)

being-cat-is-prop : (fe : Fun-Ext)
                    (P : PreCategory 𝓤 𝓥)
                  → is-prop (is-category P)
being-cat-is-prop fe P x y = Π₂-is-prop fe I _ _
 where
  I : (a b : obj ⟨ P ⟩) → is-prop (is-equiv (id-to-iso {{⟨ P ⟩}} a b))
  I a b e e' = being-equiv-is-prop (λ x y → fe {x} {y})
                                      (id-to-iso {{⟨ P ⟩}} a b) e e'

Category : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Category 𝓤 𝓥 = Σ P ꞉ PreCategory 𝓤 𝓥 , is-category P

\end{code}

Projections from category.

\begin{code}

instance
  underlying-precategory-of-category
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Category 𝓤 𝓥) (PreCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-precategory-of-category}} (P , _) = P

  underlying-wildcategory-of-category
   : {𝓤 𝓥 : Universe}
   → Underlying-Type (Category 𝓤 𝓥) (WildCategory 𝓤 𝓥)
  ⟨_⟩ {{underlying-wildcategory-of-category}} ((W , _) , _) = W


id-to-iso-is-equiv : (C : Category 𝓤 𝓥)
                   → is-category ⟨ C ⟩
id-to-iso-is-equiv C = pr₂ C

\end{code}

We can now show that the objects of any category are 1-types. This is because
equality between objects is given exactly by isomorphism, which we have shown
forms a set.

\begin{code}

cat-objs-are-1-types : (A : Category 𝓤 𝓥) → (a b : obj ⟨ A ⟩) → is-set (a ＝ b)
cat-objs-are-1-types A a b = equiv-to-set id-equiv-iso
                                          (isomorphism-type-is-set {{⟨ A ⟩}})
 where
  id-equiv-iso : (a ＝ b) ≃ (a ≅⟨ ⟨ A ⟩ ⟩ b)
  id-equiv-iso = id-to-iso {{⟨ A ⟩}} a b , id-to-iso-is-equiv A a b

\end{code}
