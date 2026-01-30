Anna Williams 29/01

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Wild

module Categories.Notation where

\end{code}

We now define some notation for categories. This way, if we are working with
wild categories C and D. We can simply write "open CategoryNotation C" and
"open CategoryNotation D" to have all operations available.

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
   id : {a : obj W} → hom a a

 open ID {{...}} public

 instance
  defnid : ID
  id {{defnid}} = WildCategory.id W

 record COMP : 𝓤 ⊔ 𝓥 ̇  where
  field
   _○_ : {a b c : obj W}
       → hom b c
       → hom a b
       → hom a c

 open COMP {{...}} public

 instance
  comp : COMP
  _○_ {{comp}} = WildCategory._○_ W

 record CATNotation : 𝓥 ⁺ ⊔ 𝓤 ̇   where
  field
   id-is-left-neutral : {a b : obj W} (f : hom a b)
           → id ○ f ＝ f
           
   id-is-right-neutral : {a b : obj W} (f : hom a b)
            → f ○ id ＝ f
            
   assoc : {a b c d : obj W}
           (f : hom a b)
           (g : hom b c)
           (h : hom c d)
         → h ○ (g ○ f) ＝ (h ○ g) ○ f

   is-iso : {a b : obj W} (f : hom a b) → 𝓥 ̇

   ⌜_⌝⁻¹ : {a b : obj W}
           {f : hom a b}
         → is-iso f
         → hom b a

   ⌜_⌝⁻¹-is-left-inverse : {a b : obj W}
                           {f : hom a b}
                           (iso : is-iso f)
                         → ⌜ iso ⌝⁻¹ ○ f ＝ id

   ⌜_⌝⁻¹-is-right-inverse : {a b : obj W}
                            {f : hom a b}
                            (iso : is-iso f)
                          → f ○ ⌜ iso ⌝⁻¹ ＝ id

   at-most-one-inverse : {a b : obj W} {f : hom a b}
                (x y : is-iso f)
              → ⌜ x ⌝⁻¹ ＝ ⌜ y ⌝⁻¹

   _≅_ : (a b : obj W) → 𝓥 ̇
   ⌜_⌝ : {a b : obj W}
       → a ≅ b
       → hom a b

   underlying-morphism-is-isomorphism : {a b : obj W}
                                        (f : a ≅ b)
                                      → Σ f⁻¹ ꞉ hom b a
                                        , (f⁻¹ ○ ⌜ f ⌝ ＝ id) × (⌜ f ⌝ ○ f⁻¹ ＝ id)

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
  _○_ {{wildcatcompnotation}} = WildCategory._○_ W

  wildcatnotation : CATNotation W
  id-is-left-neutral {{wildcatnotation}} = WildCategory.id-is-left-neutral W
  id-is-right-neutral {{wildcatnotation}} = WildCategory.id-is-right-neutral W
  assoc {{wildcatnotation}} = WildCategory.assoc W
  is-iso {{wildcatnotation}} = WildCategory.is-iso W
  ⌜_⌝⁻¹ {{wildcatnotation}} = WildCategory.⌜_⌝⁻¹ W
  ⌜_⌝⁻¹-is-left-inverse {{wildcatnotation}} = WildCategory.⌜_⌝⁻¹-is-left-inverse W
  ⌜_⌝⁻¹-is-right-inverse {{wildcatnotation}} = WildCategory.⌜_⌝⁻¹-is-right-inverse W
  at-most-one-inverse {{wildcatnotation}} = WildCategory.at-most-one-inverse W
  _≅_ {{wildcatnotation}} = WildCategory._≅_ W
  ⌜_⌝ {{wildcatnotation}} = WildCategory.⌜_⌝ W
  underlying-morphism-is-isomorphism {{wildcatnotation}} = WildCategory.underlying-morphism-is-isomorphism W
  id-to-iso {{wildcatnotation}} = WildCategory.id-to-iso W

\end{code}

