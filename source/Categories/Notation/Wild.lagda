Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Wild

module Categories.Notation.Wild where

\end{code}

We define an object notation such that we can write obj W, obj P and obj C where
W, P and C are wild categories, precategories and categories respectively.

This works similarly to the method used in Notation.UnderlyingType.

\begin{code}

record OBJ {𝓤} {𝓥} (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇  where
 field
  obj : A → B

open OBJ {{...}} public

instance
 wildcatobj : {𝓤 𝓥 : Universe} → OBJ (WildCategory 𝓤 𝓥) (𝓤 ̇ )
 obj {{wildcatobj}} = WildCategory.obj

\end{code}

We now define some notation for categories. This way, if we are working with
wild categories C and D. We can simply write "open WildCategoryNotation C" and
"open WildCategoryNotation D" to have all operations available.

This works similarly to Notation.UnderlyingType, where we define records for
each different field. We then define instances of each of the fields we want
specific to the wild category used as input.

\begin{code}

module _ {𝓤 𝓥 : Universe} (W : WildCategory 𝓤 𝓥) where
 record HOM : 𝓥 ⁺ ⊔ 𝓤 ̇  where
  field
   hom : obj W → obj W → 𝓥 ̇

 open HOM {{...}} public

 instance
  defnhom : HOM
  hom {{defnhom}} = WildCategory.hom W

 record ID : 𝓥 ⁺ ⊔ 𝓤 ̇  where
  field
   𝒊𝒅 : {a : obj W} → hom a a

 open ID {{...}} public

 instance
  defnid : ID
  𝒊𝒅 {{defnid}} = WildCategory.𝒊𝒅 W

 record COMP : 𝓤 ⊔ 𝓥 ̇  where
  field
   _◦_ : {a b c : obj W}
       → hom b c
       → hom a b
       → hom a c

 open COMP {{...}} public

 instance
  comp : COMP
  _◦_ {{comp}} = WildCategory._◦_ W

 record CATNotation : 𝓥 ⁺ ⊔ 𝓤 ̇   where
  field
   𝒊𝒅-is-left-neutral : {a b : obj W} (f : hom a b)
           → 𝒊𝒅 ◦ f ＝ f
           
   𝒊𝒅-is-right-neutral : {a b : obj W} (f : hom a b)
            → f ◦ 𝒊𝒅 ＝ f
            
   assoc : {a b c d : obj W}
           (f : hom a b)
           (g : hom b c)
           (h : hom c d)
         → h ◦ (g ◦ f) ＝ (h ◦ g) ◦ f

   inverse : {a b : obj W} (f : hom a b) → 𝓥 ̇

   ⌞_⌟ : {a b : obj W}
         {f : hom a b}
       → inverse f
       → hom b a
  
   at-most-one-inverse : {a b : obj W}
                         {f : hom a b}
                         (𝕘 𝕙 : inverse f)
                       → ⌞ 𝕘 ⌟ ＝ ⌞ 𝕙 ⌟

   ⌞_⌟-is-left-inverse : {a b : obj W}
                         {f : hom a b}
                         (𝕗⁻¹ : inverse f)
                       → ⌞ 𝕗⁻¹ ⌟ ◦ f ＝ 𝒊𝒅

   ⌞_⌟-is-right-inverse : {a b : obj W}
                          {f : hom a b}
                          (𝕗⁻¹ : inverse f)
                        → f ◦ ⌞ 𝕗⁻¹ ⌟ ＝ 𝒊𝒅

   _≅_ : (a b : obj W) → 𝓥 ̇
   ⌜_⌝ : {a b : obj W}
       → a ≅ b
       → hom a b

   underlying-morphism-is-isomorphism : {a b : obj W}
                                        (f : a ≅ b)
                                      → Σ f⁻¹ ꞉ hom b a
                                        , (f⁻¹ ◦ ⌜ f ⌝ ＝ 𝒊𝒅)
                                        × (⌜ f ⌝ ◦ f⁻¹ ＝ 𝒊𝒅)

   id-to-iso : (a b : obj W)
             → a ＝ b
             → a ≅ b

 open CATNotation {{...}} public

module WildCategoryNotation {𝓤 𝓥 : Universe} (W : WildCategory 𝓤 𝓥) where
 instance
  wildcathomnotation : HOM W
  hom {{wildcathomnotation}} = WildCategory.hom W

  wildcatidnotation : ID W
  𝒊𝒅 {{wildcatidnotation}} = WildCategory.𝒊𝒅 W

  wildcatcompnotation : COMP W
  _◦_ {{wildcatcompnotation}} = WildCategory._◦_ W

  wildcatnotation : CATNotation W
  𝒊𝒅-is-left-neutral {{wildcatnotation}} = WildCategory.𝒊𝒅-is-left-neutral W
  𝒊𝒅-is-right-neutral {{wildcatnotation}} = WildCategory.𝒊𝒅-is-right-neutral W
  assoc {{wildcatnotation}} = WildCategory.assoc W
  inverse {{wildcatnotation}} = WildCategory.inverse W
  ⌞_⌟ {{wildcatnotation}} = WildCategory.⌞_⌟ W
  ⌞_⌟-is-left-inverse {{wildcatnotation}} = WildCategory.⌞_⌟-is-left-inverse W
  ⌞_⌟-is-right-inverse {{wildcatnotation}} = WildCategory.⌞_⌟-is-right-inverse W
  at-most-one-inverse {{wildcatnotation}} = WildCategory.at-most-one-inverse W
  _≅_ {{wildcatnotation}} = WildCategory._≅_ W
  ⌜_⌝ {{wildcatnotation}} = WildCategory.⌜_⌝ W
  underlying-morphism-is-isomorphism {{wildcatnotation}}
   = WildCategory.underlying-morphism-is-isomorphism W
  id-to-iso {{wildcatnotation}} = WildCategory.id-to-iso W

\end{code}
