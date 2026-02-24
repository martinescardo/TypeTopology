Anna Williams 14 February 2026

Notation for displayed precategories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Sets
open import UF.DependentEquality
open import Categories.Pre
open import Categories.Notation.Pre
open import Categories.Displayed.Pre

module Categories.Displayed.Notation.Pre where

\end{code}

We now define some notation for displayed precategories similarly to that of
categories.

\begin{code}

record DOBJ {𝓤 𝓥 : Universe}
            {P : Precategory 𝓦 𝓣}
            (D : DisplayedPrecategory 𝓤 𝓥 P)
          : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj[_] : obj P → 𝓤 ̇

open DOBJ {{...}} public

module _ {𝓤 𝓥 : Universe}
         {P : Precategory 𝓦 𝓣}
         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 open PrecategoryNotation P

 instance
  d-obj-m : DOBJ D
  obj[_] {{d-obj-m}} = DisplayedPrecategory.obj[_] D

 record DHOM  : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[_] : {a b : obj P} → hom a b → obj[ a ] → obj[ b ] → 𝓥 ̇

 open DHOM {{...}} public

 instance
  d-hom-m : DHOM
  hom[_] {{d-hom-m}} = DisplayedPrecategory.hom[_] D

 record DCOMP : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   _○_ : {a b c : obj P}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {z : obj[ c ]}
       → hom[ g ] y z
       → hom[ f ] x y
       → hom[ g ◦ f ] x z

 open DCOMP {{...}} public

 record DID : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   D-𝒊𝒅 : {p : obj P}
          {x : obj[ p ]}
        → hom[ 𝒊𝒅 ] x x

 open DID {{...}} public

 instance
  dcomp-m : DCOMP 
  _○_ {{dcomp-m}} = DisplayedPrecategory._○_ D

 instance
  d-id-m : DID
  D-𝒊𝒅 {{d-id-m}} = DisplayedPrecategory.D-𝒊𝒅 D

 record DNotation : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   hom[-]-is-set : {a b : obj P}
                   {f : hom a b}
                   {x : obj[ a ]}
                   {y : obj[ b ]}
                 → is-set (hom[ f ] x y)
                 
   D-𝒊𝒅-is-right-neutral : {a b : obj P}
                  {f : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                  (𝕗 : hom[ f ] x y)
                → 𝕗 ○ D-𝒊𝒅
                ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-right-neutral f ⟧
                  𝕗

   D-𝒊𝒅-is-left-neutral : {a b : obj P}
                 {f : hom a b}
                 {x : obj[ a ]}
                 {y : obj[ b ]}
                 (𝕗 : hom[ f ] x y)
               → D-𝒊𝒅 ○ 𝕗
               ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-left-neutral f ⟧
                 𝕗
  
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
           ＝⟦ (λ - → hom[ - ] x w) , assoc f g h ⟧
             (𝕙 ○ 𝕘) ○ 𝕗

   D-inverse : {a b : obj P}
               {x : obj[ a ]}
               {y : obj[ b ]}
               (f : a ≅ b)
               (𝕗 : hom[ ⌜ f ⌝ ] x y)
             → 𝓥 ̇
   _≅[_]_ : {a b : obj P}
            (x : obj[ a ])
            (f : a ≅ b)
            (y : obj[ b ])
          → 𝓥 ̇
 open DNotation {{...}} public


module DispPrecatNotation {𝓦 𝓣 : Universe}
                          {P : Precategory 𝓦 𝓣}
                          (D : DisplayedPrecategory 𝓤 𝓥 P) where
 instance
  d-obj : DOBJ D
  obj[_] {{d-obj}} = DisplayedPrecategory.obj[_] D
  
 instance
  d-hom : DHOM D
  hom[_] {{d-hom}} = DisplayedPrecategory.hom[_] D

 instance
  d-id : DID D
  D-𝒊𝒅 {{d-id}} = DisplayedPrecategory.D-𝒊𝒅 D

 instance
  d-comp : DCOMP D
  _○_ {{d-comp}} = DisplayedPrecategory._○_ D

 instance
  d-notation : DNotation D
  hom[-]-is-set {{d-notation}} = DisplayedPrecategory.hom[-]-is-set D
  D-𝒊𝒅-is-right-neutral {{d-notation}}
   = DisplayedPrecategory.D-𝒊𝒅-is-right-neutral D
  D-𝒊𝒅-is-left-neutral {{d-notation}}
   = DisplayedPrecategory.D-𝒊𝒅-is-left-neutral D
  D-assoc {{d-notation}} = DisplayedPrecategory.D-assoc D
  D-inverse {{d-notation}} = DisplayedPrecategory.D-inverse D
  _≅[_]_ {{d-notation}} = DisplayedPrecategory._≅[_]_ D
  
\end{code}
