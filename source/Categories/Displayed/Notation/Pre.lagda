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

record DOBJ (A : 𝓤 ̇ ) (B : 𝓥 ̇ ) (C : 𝓦 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ̇ where
 field
  obj[_] : A → B → C

open DOBJ {{...}} public

instance
 d-pre-obj : {P : Precategory 𝓦 𝓣} → DOBJ (obj P) (DisplayedPrecategory 𝓤 𝓥 P) (𝓤 ̇ )
 obj[_] {{d-pre-obj}} = λ a b → DisplayedPrecategory.obj[ b ] a

module _ {𝓤 𝓥 : Universe}
         {P : Precategory 𝓦 𝓣}
         (D : DisplayedPrecategory 𝓤 𝓥 P) where
 open PrecategoryNotation P

 record DHOM  : (𝓦 ⊔ 𝓣 ⊔ 𝓤 ⊔ 𝓥)⁺ ̇  where
  field
   hom[_] : {a b : obj P} → hom a b → obj[ a ] D → obj[ b ] D → 𝓥 ̇

 open DHOM {{...}} public

 instance
  d-hom-m : DHOM
  hom[_] {{d-hom-m}} = DisplayedPrecategory.hom[_] D

 record DCOMP : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   _○_ : {a b c : obj P}
         {g : hom b c}
         {f : hom a b}
         {x : obj[ a ] D}
         {y : obj[ b ] D}
         {z : obj[ c ] D}
       → hom[ g ] y z
       → hom[ f ] x y
       → hom[ g ◦ f ] x z

 open DCOMP {{...}} public

 record DID : ((𝓦 ⊔ 𝓣) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
  field
   D-𝒊𝒅 : {p : obj P}
          {x : obj[ p ] D}
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
                   {x : obj[ a ] D}
                   {y : obj[ b ] D}
                 → is-set (hom[ f ] x y)
                 
   D-𝒊𝒅-is-right-neutral : {a b : obj P}
                  {f : hom a b}
                  {x : obj[ a ] D}
                  {y : obj[ b ] D}
                  (𝕗 : hom[ f ] x y)
                → 𝕗 ○ D-𝒊𝒅
                ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-right-neutral f ⟧
                  𝕗

   D-𝒊𝒅-is-left-neutral : {a b : obj P}
                 {f : hom a b}
                 {x : obj[ a ] D}
                 {y : obj[ b ] D}
                 (𝕗 : hom[ f ] x y)
               → D-𝒊𝒅 ○ 𝕗
               ＝⟦ (λ - → hom[ - ] x y) , 𝒊𝒅-is-left-neutral f ⟧
                 𝕗
  
   D-assoc : {a b c d : obj P}
             {f : hom a b}
             {g : hom b c}
             {h : hom c d}
             {x : obj[ a ] D}
             {y : obj[ b ] D}
             {z : obj[ c ] D}
             {w : obj[ d ] D}
             {𝕗 : hom[ f ] x y}
             {𝕘 : hom[ g ] y z}
             {𝕙 : hom[ h ] z w}
           → 𝕙 ○ (𝕘 ○ 𝕗)
           ＝⟦ (λ - → hom[ - ] x w) , assoc f g h ⟧
             (𝕙 ○ 𝕘) ○ 𝕗

   D-inverse : {a b : obj P}
               {x : obj[ a ] D}
               {y : obj[ b ] D}
               (f : a ≅ b)
               (𝕗 : hom[ ⌜ f ⌝ ] x y)
             → 𝓥 ̇
   _≅[_]_ : {a b : obj P}
            (x : obj[ a ] D)
            (f : a ≅ b)
            (y : obj[ b ] D)
          → 𝓥 ̇
   D-⌜_⌝ : {a b : obj P}
           {x : obj[ a ] D}
           {f : a ≅ b}
           {y : obj[ b ] D}
         → x ≅[ f ] y
         → hom[ ⌜ f ⌝ ] x y

   D-morphism-is-isomorphism : {a b : obj P}
                               {x : obj[ a ] D}
                               {f : a ≅ b}
                               {y : obj[ b ] D}
                             → (𝕗 : x ≅[ f ] y)
                             → D-inverse f D-⌜ 𝕗 ⌝

   D-⌞_⌟ : {a  b : obj P}
           {x : obj[ a ] D}
           {y : obj[ b ] D}
           {f : a ≅ b}
           {𝕗 : hom[ ⌜ f ⌝ ] x y}
         → D-inverse f 𝕗
         → hom[ ⌞ underlying-morphism-is-isomorphism f ⌟ ] y x

   D-⌞_⌟-is-left-inverse : {a  b : obj P}
           {x : obj[ a ] D}
           {y : obj[ b ] D}
           {f : a ≅ b}
           {𝕗 : hom[ ⌜ f ⌝ ] x y}
         → (𝕗⁻¹ : D-inverse f 𝕗)
         → D-⌞ 𝕗⁻¹ ⌟  ○ 𝕗
         ＝⟦ (λ - → hom[ - ] x x)
           , ⌞ underlying-morphism-is-isomorphism f ⌟-is-left-inverse ⟧
           D-𝒊𝒅

   D-⌞_⌟-is-right-inverse : {a  b : obj P}
           {x : obj[ a ] D}
           {y : obj[ b ] D}
           {f : a ≅ b}
           {𝕗 : hom[ ⌜ f ⌝ ] x y}
         → (𝕗⁻¹ : D-inverse f 𝕗)
         → 𝕗 ○ D-⌞ 𝕗⁻¹ ⌟
         ＝⟦ (λ - → hom[ - ] y y)
           , ⌞ underlying-morphism-is-isomorphism f ⌟-is-right-inverse ⟧
           D-𝒊𝒅
   to-≅[-]-＝ : {a b : obj P}
                {x : obj[ a ] D}
                {y : obj[ b ] D}
                {f : a ≅ b}
                {𝕗 𝕗' : x ≅[ f ] y}
              → D-⌜ 𝕗 ⌝ ＝ D-⌜ 𝕗' ⌝
              → 𝕗 ＝ 𝕗'
       
 open DNotation {{...}} public

module DisplayedPrecategoryNotation {𝓦 𝓣 : Universe}
                                    {P : Precategory 𝓦 𝓣}
                                    (D : DisplayedPrecategory 𝓤 𝓥 P) where
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
  D-⌜_⌝ {{d-notation}} = DisplayedPrecategory.D-⌜_⌝ D
  D-⌞_⌟ {{d-notation}} = DisplayedPrecategory.D-⌞_⌟ D
  D-⌞_⌟-is-left-inverse {{d-notation}}
   = DisplayedPrecategory.D-⌞_⌟-is-left-inverse D
  D-⌞_⌟-is-right-inverse {{d-notation}}
   = DisplayedPrecategory.D-⌞_⌟-is-right-inverse D
  D-morphism-is-isomorphism {{d-notation}}
   = DisplayedPrecategory.D-morphism-is-isomorphism D
  to-≅[-]-＝ {{d-notation}} = DisplayedPrecategory.to-≅[-]-＝ D
  
\end{code}
