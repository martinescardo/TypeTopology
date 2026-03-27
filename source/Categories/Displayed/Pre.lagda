Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.DependentEquality
open import UF.Sets
open import UF.Subsingletons
open import Categories.Pre
open import Categories.Notation.Pre

module Categories.Displayed.Pre where

\end{code}

We first define the notion of a displayed precategory. The objects and homs of
this are indexed by a given base precategory. We then derive the usual parts of
a precategory, including the usual axioms which now have dependent equalities.

More precisely, a displayed precategory over a precategory P consists of,

 - for each object p : obj P, a type of objects over c, denoted obj[p],

 - for each morphism f : a → b in P, x : obj[a] and y : obj[b] form a set of
   morphisms from x to y over f, denoted hom[f] x y,

 - for each p : obj P and x : obj[p], a morphism id : hom[id] x x, and

 - for all morphisms f : a → b and g : b → c in P and objects x : obj[a],
   y : obj[b], z : obj[c], a function
   
   ○ : hom[g] y z → hom[f] x y → hom[f ◦ g] x z.

Such that the following hold

 - f ○ id = id
 - id ○ f = f
 - f ○ (g ○ h) = (f ○ g) ○ h 

\begin{code}

record DisplayedPrecategory (𝓦 𝓣 : Universe)
                            (P : Precategory 𝓤 𝓥)
                          : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥)⁺ ̇  where
 open PrecategoryNotation P
 field
  obj[_] : (c : obj P) → 𝓦 ̇
  hom[_] : {a b : obj P}
           (f : hom a b)
           (x : obj[ a ])
           (y : obj[ b ])
         → 𝓣 ̇
  hom[-]-is-set : {a b : obj P}
                  {f : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → is-set (hom[ f ] x y)
  
  D-𝒊𝒅 : {c : obj P}
         {x : obj[ c ]}
       → hom[ 𝒊𝒅 ] x x

  _○_ : {a b c : obj P}
        {g : hom b c}
        {f : hom a b}
        {x : obj[ a ]}
        {y : obj[ b ]}
        {z : obj[ c ]}
      → hom[ g ] y z
      → hom[ f ] x y
      → hom[ g ◦ f ] x z

 private
  hom[-] : {a b : obj P}
           (x : obj[ a ])
           (y : obj[ b ])
         → hom a b
         → 𝓣 ̇
  hom[-] x y = λ - → hom[ - ] x y

 field
  D-𝒊𝒅-is-right-neutral : {a b : obj P}
                          {f : hom a b}
                          {x : obj[ a ]}
                          {y : obj[ b ]}
                          (𝕗 : hom[ f ] x y)
                        → 𝕗 ○ D-𝒊𝒅 ＝⟦ hom[-] x y , 𝒊𝒅-is-right-neutral f ⟧ 𝕗

  D-𝒊𝒅-is-left-neutral : {a b : obj P}
                         {f : hom a b}
                         {x : obj[ a ]}
                         {y : obj[ b ]}
                         (𝕗 : hom[ f ] x y)
                       → D-𝒊𝒅 ○ 𝕗 ＝⟦ hom[-] x y , 𝒊𝒅-is-left-neutral f ⟧ 𝕗
  
  D-assoc : {a b c d : obj P}
            {f : hom a b}
            {g : hom b c}
            {h : hom c d}
            {x : obj[ a ]}
            {y : obj[ b ]}
            {z : obj[ c ]}
            {w : obj[ d ]}
            {𝕗 : hom[ f ] x y}
            {𝕘 : hom[ g ] y z}
            {𝕙 : hom[ h ] z w}
          → 𝕙 ○ (𝕘 ○ 𝕗)
          ＝⟦ hom[-] x w , assoc f g h ⟧
            (𝕙 ○ 𝕘) ○ 𝕗

\end{code}

We can now define a displayed version of isomorphism between objects.

\begin{code}

 D-inverse : {a  b : obj P}
             {x : obj[ a ]}
             {y : obj[ b ]}
             (f : a ≅ b)
             (𝕗 : hom[ ⌜ f ⌝ ] x y)
           → 𝓣 ̇
 D-inverse {a} {b} {x} {y} f 𝕗
   = Σ 𝕗⁻¹ ꞉ hom[ ⌞ underlying-morphism-is-isomorphism f ⌟ ] y x
     , ((𝕗⁻¹ ○ 𝕗 ＝⟦ hom[-] x x , i ⟧ D-𝒊𝒅)
      × (𝕗 ○ 𝕗⁻¹ ＝⟦ hom[-] y y , ii ⟧ D-𝒊𝒅))
  where
   i = ⌞ underlying-morphism-is-isomorphism f ⌟-is-left-inverse
   ii = ⌞ underlying-morphism-is-isomorphism f ⌟-is-right-inverse

 _≅[_]_ : {a b : obj P}
          (x : obj[ a ])
          (f : a ≅ b)
          (y : obj[ b ])
        → 𝓣 ̇
 x ≅[ f ] y = Σ 𝕗 ꞉ hom[ ⌜ f ⌝ ] x y , D-inverse f 𝕗

\end{code}
