Anna Williams, 17 October 2025

Definition of Wild Category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.Base
open import UF.Equiv hiding (_≅_ ; inverse ; ⌜_⌝ ; ⌜_⌝⁻¹)
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module Categories.Wild where

\end{code}

We start by defining a wild category [1]. This consists of the usual components 
of a category, which is as follows.

 * A collection of objects, obj,

 * for each pair of objects, A B : obj, a homomorphism between A and B, hom A B,

 * for each object A : obj, an identity homomorphism id A : hom A A, and

 * a composition operation, ○, which for objects A B C : obj and homomorphisms
   f : hom A B, g : hom B C gives a new homomorphism, g ○ f : hom A C.

Such that the following axioms hold.

 * left-id: for objects A B : obj and morphism f : hom A B, f ○ id ＝ f,

 * right-id: for objects A B : obj and morphism f : hom A B, id ○ f ＝ f, and

 * associativity: for objects A B C D : obj and morphisms f : hom A B,
                  g : hom B C, h : hom C D, h ○ (g ○ f) ＝ (h ○ g) ○ f.


[1] Capriotti, Paolo and Nicolai Kraus (2017). Univalent Higher Categories via
Complete Semi-Segal Type. https://arxiv.org/abs/1707.03693.

\begin{code}

record WildCategory (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇  where
 constructor wildcategory
 field
  obj : 𝓤 ̇
  hom : obj → obj → 𝓥 ̇
  𝒊𝒅 : {a : obj} → hom a a
  
  _○_ : {a b c : obj} → hom b c → hom a b → hom a c

  𝒊𝒅-is-left-neutral : {a b : obj} (f : hom a b) → 𝒊𝒅 ○ f ＝ f
  
  𝒊𝒅-is-right-neutral : {a b : obj} (f : hom a b) → f ○ 𝒊𝒅 ＝ f

  assoc : {a b c d : obj}
          (f : hom a b)
          (g : hom b c)
          (h : hom c d)
        → h ○ (g ○ f) ＝ (h ○ g) ○ f

\end{code}

An isomorphism in a category consists of a homomorphism, f : hom a b, and some
*inverse* homomorphism, g : hom b a, such that g ∘ f = id and f ∘ g ＝ id.

We first define the property of being an isomorphism and then define the type of
isomorphisms between objects of a wild category.

\begin{code}

 inverse : {a b : obj} (f : hom a b) → 𝓥 ̇
 inverse {a} {b} f = Σ f⁻¹ ꞉ hom b a , (f⁻¹ ○ f ＝ 𝒊𝒅) × (f ○ f⁻¹ ＝ 𝒊𝒅)

 ⌞_⌟ : {a b : obj}
         {f : hom a b}
       → inverse f
       → hom b a
 ⌞_⌟ = pr₁

 ⌞_⌟-is-left-inverse : {a b : obj}
                         {f : hom a b}
                         (𝕗⁻¹ : inverse f)
                       → ⌞ 𝕗⁻¹ ⌟ ○ f ＝ 𝒊𝒅
 ⌞ 𝕗 ⌟-is-left-inverse = pr₁ (pr₂ 𝕗)

 ⌞_⌟-is-right-inverse : {a b : obj}
                          {f : hom a b}
                          (𝕗⁻¹ : inverse f)
                        → f ○ ⌞ 𝕗⁻¹ ⌟ ＝ 𝒊𝒅
 ⌞ 𝕗 ⌟-is-right-inverse = pr₂ (pr₂ 𝕗)

 _≅_ : (a b : obj) → 𝓥 ̇
 a ≅ b = Σ f ꞉ hom a b , inverse f

 ⌜_⌝ : {a b : obj}
     → a ≅ b
     → hom a b
 ⌜_⌝ = pr₁

 underlying-morphism-is-isomorphism
  : {a b : obj}
    (f : a ≅ b)
  → Σ f⁻¹ ꞉ hom b a , (f⁻¹ ○ ⌜ f ⌝ ＝ 𝒊𝒅) × (⌜ f ⌝ ○ f⁻¹ ＝ 𝒊𝒅)
 underlying-morphism-is-isomorphism = pr₂

\end{code}

We can show that two inverses for a given isomorphism must be equal.

\begin{code}

 at-most-one-inverse : {a b : obj}
                       {f : hom a b}
                       (g h : inverse f)
                     → ⌞ g ⌟ ＝ ⌞ h ⌟
 at-most-one-inverse {a} {b} {f} g h = ⌞ g ⌟               ＝⟨ i ⟩
                                       ⌞ g ⌟ ○ 𝒊𝒅           ＝⟨ ii ⟩
                                       ⌞ g ⌟ ○ (f ○ ⌞ h ⌟) ＝⟨ iii ⟩
                                       (⌞ g ⌟ ○ f) ○ ⌞ h ⌟ ＝⟨ iv ⟩
                                       𝒊𝒅 ○ ⌞ h ⌟          ＝⟨ v ⟩
                                       ⌞ h ⌟               ∎
  where
   i   = (𝒊𝒅-is-right-neutral ⌞ g ⌟)⁻¹
   ii  = ap (⌞ g ⌟ ○_) (⌞ h ⌟-is-right-inverse)⁻¹
   iii = assoc _ _ _
   iv  = ap (_○ ⌞ h ⌟) ⌞ g ⌟-is-left-inverse
   v   = 𝒊𝒅-is-left-neutral ⌞ h ⌟

\end{code}

We can easily show that if a ＝ b, then a ≅ b. This is because if a ＝ b, then
by path induction we need to show that a ≅ a. This can be constructed as
follows.

\begin{code}

 id-to-iso : (a b : obj)
           → a ＝ b
           → a ≅ b
 id-to-iso a b refl = 𝒊𝒅 , 𝒊𝒅 , 𝒊𝒅-is-left-neutral 𝒊𝒅 , 𝒊𝒅-is-left-neutral 𝒊𝒅

\end{code}
