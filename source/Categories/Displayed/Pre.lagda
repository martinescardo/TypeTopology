Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
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

 dep-hom-is-set : {a b : obj P}
                  {f : hom a b}
                  {g : hom a b}
                  {x : obj[ a ]}
                  {y : obj[ b ]}
                → {i : hom[ f ] x y}
                → {j : hom[ g ] x y}
                → {e : f ＝ g}
                → is-prop (i ＝⟦ hom[-] x y , e ⟧ j)
 dep-hom-is-set = to-dep-＝ hom[-]-is-set

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

 D-⌜_⌝ : {a b : obj P}
         {x : obj[ a ]}
         {f : a ≅ b}
         {y : obj[ b ]}
       → x ≅[ f ] y
       → hom[ ⌜ f ⌝ ] x y
 D-⌜_⌝ = pr₁

 D-morphism-is-isomorphism : {a b : obj P}
                             {x : obj[ a ]}
                             {f : a ≅ b}
                             {y : obj[ b ]}
                           → (𝕗 : x ≅[ f ] y)
                           → D-inverse f D-⌜ 𝕗 ⌝
 D-morphism-is-isomorphism = pr₂

 D-⌞_⌟ : {a  b : obj P}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {f : a ≅ b}
         {𝕗 : hom[ ⌜ f ⌝ ] x y}
       → D-inverse f 𝕗
       → hom[ ⌞ underlying-morphism-is-isomorphism f ⌟ ] y x
 D-⌞_⌟ = pr₁

 D-⌞_⌟-is-left-inverse : {a  b : obj P}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {f : a ≅ b}
         {𝕗 : hom[ ⌜ f ⌝ ] x y}
       → (𝕗⁻¹ : D-inverse f 𝕗)
       → D-⌞ 𝕗⁻¹ ⌟  ○ 𝕗
       ＝⟦ hom[-] x x ,
           ⌞ underlying-morphism-is-isomorphism f ⌟-is-left-inverse ⟧
         D-𝒊𝒅
 D-⌞_⌟-is-left-inverse 𝕗⁻¹ = pr₁ (pr₂ 𝕗⁻¹)

 D-⌞_⌟-is-right-inverse : {a  b : obj P}
         {x : obj[ a ]}
         {y : obj[ b ]}
         {f : a ≅ b}
         {𝕗 : hom[ ⌜ f ⌝ ] x y}
       → (𝕗⁻¹ : D-inverse f 𝕗)
       → 𝕗 ○ D-⌞ 𝕗⁻¹ ⌟
       ＝⟦ hom[-] y y ,
           ⌞ underlying-morphism-is-isomorphism f ⌟-is-right-inverse ⟧
         D-𝒊𝒅
 D-⌞_⌟-is-right-inverse 𝕗⁻¹ = pr₂ (pr₂ 𝕗⁻¹)

\end{code}

We show that being an isomorphism is a proposition.

\begin{code}

 D-inverse-is-lc : {a b : obj P}
                   {x : obj[ a ]}
                   {y : obj[ b ]}
                   {f : a ≅ b}
                   {𝕗 : hom[ ⌜ f ⌝ ] x y}
                   {𝕚 𝕛 : D-inverse f 𝕗}
                 → D-⌞ 𝕚 ⌟ ＝ D-⌞ 𝕛 ⌟
                 → 𝕚 ＝ 𝕛
 D-inverse-is-lc {_} {_} {x} {y} e
  = to-subtype-＝ (λ _ → ×-is-prop dep-hom-is-set dep-hom-is-set) e
     
 at-most-one-D-inverse : {a b : obj P}
                         {x : obj[ a ]}
                         {y : obj[ b ]}
                         {f : a ≅ b}
                         {𝕗 : hom[ ⌜ f ⌝ ] x y}
                         (𝕘 𝕙 : D-inverse f 𝕗)
                       → D-⌞ 𝕘 ⌟ ＝ D-⌞ 𝕙 ⌟
 at-most-one-D-inverse {_} {_} {x} {y} {f} {𝕗} 𝕘 𝕙
  = transport (λ - → _ ＝⟦ _ , - ⟧ _) (hom-is-set P _ _) inv-eq
  where
   f⁻¹ = underlying-morphism-is-isomorphism f

   inv-eq : D-⌞ 𝕘 ⌟
          ＝⟦ (λ - → hom[ - ] y x) , at-most-one-inverse f⁻¹ f⁻¹ ⟧
            D-⌞ 𝕙 ⌟
   inv-eq = D-⌞ 𝕘 ⌟                   ＝⟦⟨ I ⟩⟧
            D-⌞ 𝕘 ⌟ ○ D-𝒊𝒅            ＝⟦⟨ II ⟩⟧
            D-⌞ 𝕘 ⌟ ○ (𝕗 ○ D-⌞ 𝕙 ⌟)   ＝⟦⟨ III ⟩⟧
            (D-⌞ 𝕘 ⌟ ○ 𝕗) ○ D-⌞ 𝕙 ⌟   ＝⟦⟨ IV ⟩⟧
            D-𝒊𝒅 ○ D-⌞ 𝕙 ⌟            ＝⟦⟨ V ⟩⟧
            D-⌞ 𝕙 ⌟                   ∎
    where
     I = dep-sym (D-𝒊𝒅-is-right-neutral D-⌞ 𝕘 ⌟)
     II = dep-sym (dep-ap (D-⌞ 𝕘 ⌟ ○_) D-⌞ 𝕙 ⌟-is-right-inverse)
     III = D-assoc
     IV = dep-ap (_○ D-⌞ 𝕙 ⌟) (D-⌞ 𝕘 ⌟-is-left-inverse)
     V = D-𝒊𝒅-is-left-neutral D-⌞ 𝕙 ⌟

 being-D-iso-is-prop : {a b : obj P}
                       {x : obj[ a ]}
                       {y : obj[ b ]}
                       {f : a ≅ b}
                       (𝕗 : hom[ ⌜ f ⌝ ] x y)
                     → is-prop (D-inverse f 𝕗)
 being-D-iso-is-prop {_} {_} {x} {y} {f} 𝕗 𝕘 𝕙
  = D-inverse-is-lc (at-most-one-D-inverse 𝕘 𝕙)

\end{code}

Using this, we can define equality of displayed isomorphisms based upon equality
of the underlying morphism.

\begin{code}

 to-≅[-]-＝ : {a b : obj P}
              {x : obj[ a ]}
              {y : obj[ b ]}
              {f : a ≅ b}
              {𝕗 𝕗' : x ≅[ f ] y}
            → D-⌜ 𝕗 ⌝ ＝ D-⌜ 𝕗' ⌝
            → 𝕗 ＝ 𝕗'
 to-≅[-]-＝ = to-subtype-＝ being-D-iso-is-prop

open DisplayedPrecategory public using (being-D-iso-is-prop
                                      ; at-most-one-D-inverse)

\end{code}
 
