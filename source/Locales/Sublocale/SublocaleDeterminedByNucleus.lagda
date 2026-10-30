---
title:  Sublocale determined by a nucleus on a locale
author: Ayberk Tosun
date:   2026-10-30
---

In this module, we construct the sublocale of a locale determined by a nucleus
on that locale.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sublocale.SublocaleDeterminedByNucleus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        --  (pe : Prop-Ext)
       where

open import Locales.Frame pt fe
open import Locales.Sublocale.Nucleus pt fe
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.SubtypeClassifier using (Ω; _holds)

open AllCombinators pt fe
open Locale

\end{code}

We work in a module parameterized by a locale `X` and a nucleus `j : 𝒪 X → 𝒪 X`.

\begin{code}

module Sublocale-Determined-By-Nucleus
        (X : Locale (𝓤 ⁺) 𝓤 𝓤)
        (𝒿 : Nucleus (𝒪 X))
       where

 j = pr₁ 𝒿

\end{code}

We start by writing down the type of fixed point for `j`.

\begin{code}

 Fixed-Point : 𝓤 ⁺  ̇
 Fixed-Point = Σ U ꞉ ⟨ 𝒪 X ⟩ , j U ＝ U

 underlying-open : Fixed-Point → ⟨ 𝒪 X ⟩
 underlying-open (U , _) = U

\end{code}

The order is the same as that of `𝒪 X`.

\begin{code}

 _≤ᶠ_ : Fixed-Point → Fixed-Point → Ω 𝓤
 (U , _) ≤ᶠ (V , _) = U ≤[ poset-of (𝒪 X) ] V

 ≤ᶠ-is-reflexive : is-reflexive _≤ᶠ_ holds
 ≤ᶠ-is-reflexive = ≤-is-reflexive (poset-of (𝒪 X)) ∘ underlying-open

 ≤ᶠ-is-transitive : is-transitive _≤ᶠ_ holds
 ≤ᶠ-is-transitive (U , _) (V , _) (W , _) =
  ≤-is-transitive (poset-of (𝒪 X)) U V W

 ≤ᶠ-is-antisymmetric : is-antisymmetric _≤ᶠ_
 ≤ᶠ-is-antisymmetric {𝔘} {𝔙} p q = to-subtype-＝ † ‡
  where
   † : (U : ⟨ 𝒪 X ⟩) → is-prop (j U ＝ U)
   † _ = carrier-of-[ poset-of (𝒪 X) ]-is-set

   ‡ : underlying-open 𝔘 ＝ underlying-open 𝔙
   ‡ = ≤-is-antisymmetric (poset-of (𝒪 X)) p q

 ≤ᶠ-is-partial-order : is-partial-order Fixed-Point _≤ᶠ_
 ≤ᶠ-is-partial-order =
  (≤ᶠ-is-reflexive , ≤ᶠ-is-transitive) , ≤ᶠ-is-antisymmetric

 open Meets _≤ᶠ_

\end{code}

\begin{code}

 𝟏ᶠ : Fixed-Point
 𝟏ᶠ = 𝟏[ 𝒪 X ] , nucleus-preserves-top (𝒪 X) 𝒿

 𝟏ᶠ-is-top : Meets.is-top _≤ᶠ_ 𝟏ᶠ holds
 𝟏ᶠ-is-top (U , _) = 𝟏-is-top (𝒪 X) U

 fixed-points-are-closed-under-binary-meets
  : (U V : ⟨ 𝒪 X ⟩)
  → j U ＝ U
  → j V ＝ V
  → j (U ∧[ 𝒪 X ] V) ＝ U ∧[ 𝒪 X ] V
 fixed-points-are-closed-under-binary-meets U V p q =
    j (U ∧[ 𝒪 X ] V)   ＝⟨ Ⅰ ⟩
    j U ∧[ 𝒪 X ] j V   ＝⟨ Ⅱ ⟩
    U ∧[ 𝒪 X ] j V     ＝⟨ Ⅲ ⟩
    U ∧[ 𝒪 X ] V       ∎
     where
      Ⅰ = 𝓃₃ (𝒪 X) 𝒿 U V
      Ⅱ = ap (λ - → - ∧[ 𝒪 X ] j V) (p ⁻¹) ⁻¹
      Ⅲ = ap (λ - → U ∧[ 𝒪 X ] -) (q ⁻¹) ⁻¹

 _∧ᶠ_ : Fixed-Point → Fixed-Point → Fixed-Point
 (U , p) ∧ᶠ (V , q) = (U ∧[ 𝒪 X ] V) , †
  where
   † : j (U ∧[ 𝒪 X ] V) ＝ U ∧[ 𝒪 X ] V
   † = fixed-points-are-closed-under-binary-meets U V p q

 ∧ᶠ-gives-glb : (U V : Fixed-Point) → ((U ∧ᶠ V) is-glb-of (U , V)) holds
 ∧ᶠ-gives-glb 𝔘@(U , _) 𝔙@(V , _) = (β , γ) , δ
  where
   β : ((𝔘 ∧ᶠ 𝔙) ≤ᶠ 𝔘) holds
   β = ∧[ 𝒪 X ]-lower₁ U V

   γ : ((𝔘 ∧ᶠ 𝔙) ≤ᶠ 𝔙) holds
   γ = ∧[ 𝒪 X ]-lower₂ U V

   δ : ((𝔚 , _) : lower-bound (𝔘 , 𝔙)) → (𝔚 ≤ᶠ (𝔘 ∧ᶠ 𝔙)) holds
   δ (_ , p , q) = ∧[ 𝒪 X ]-greatest _ _ _ p q

 ⋁ᶠ_ : Fam 𝓤 Fixed-Point → Fixed-Point
 ⋁ᶠ 𝔘⃗ = j (⋁⟨ i ⟩ U⃗ [ i ]) , ≤-is-antisymmetric (poset-of (𝒪 X)) ‡ †
  where
   open JoinNotation (λ - → ⋁[ 𝒪 X ] -)
   open PosetReasoning (poset-of (𝒪 X))

   U⃗ : Fam 𝓤 ⟨ 𝒪 X ⟩
   U⃗ = ⁅ underlying-open 𝔘⃗ᵢ ∣ 𝔘⃗ᵢ ε 𝔘⃗ ⁆

   ‡ : (j (j (⋁⟨ i ⟩ U⃗ [ i ])) ≤[ poset-of (𝒪 X) ] j (⋁⟨ i ⟩ U⃗ [ i ])) holds
   ‡ = 𝓃₂ (𝒪 X) 𝒿 (⋁⟨ i ⟩ U⃗ [ i ])

   † : (j (⋁⟨ i ⟩ U⃗ [ i ]) ≤[ poset-of (𝒪 X) ] j (j (⋁⟨ i ⟩ U⃗ [ i ]))) holds
   † = 𝓃₁ (𝒪 X) 𝒿 (j (⋁⟨ i ⟩ U⃗ [ i ]))

 open Joins _≤ᶠ_

 ⋁ᶠ-gives-lub : (𝔘⃗ : Fam 𝓤 Fixed-Point) → ((⋁ᶠ 𝔘⃗) is-lub-of 𝔘⃗) holds
 ⋁ᶠ-gives-lub 𝔘⃗ = β , γ
  where
   open PosetReasoning (poset-of (𝒪 X))
   open JoinNotation (λ - → ⋁[ 𝒪 X ] -)

   U⃗ : Fam 𝓤 ⟨ 𝒪 X ⟩
   U⃗ = ⁅ underlying-open 𝔘⃗ᵢ ∣ 𝔘⃗ᵢ ε 𝔘⃗ ⁆

   β : ((⋁ᶠ 𝔘⃗) is-an-upper-bound-of 𝔘⃗) holds
   β i = U⃗ [ i ]                ≤⟨ Ⅰ ⟩
         ⋁⟨ i ⟩ U⃗ [ i ]         ≤⟨ Ⅱ ⟩
         j (⋁⟨ i ⟩ U⃗ [ i ])     ■
          where
           Ⅰ = ⋁[ 𝒪 X ]-upper U⃗ i
           Ⅱ = 𝓃₁ (𝒪 X) 𝒿 (⋁⟨ i ⟩ U⃗ [ i ])

   γ : ((𝔙 , _) : upper-bound 𝔘⃗) → ((⋁ᶠ 𝔘⃗) ≤ᶠ 𝔙) holds
   γ ((V , p) , φ) =
    j (⋁⟨ i ⟩ U⃗ [ i ])     ≤⟨ Ⅰ  ⟩
    j V                    ＝⟨ Ⅱ ⟩ₚ
    V                      ■
     where
      † : ((⋁⟨ i ⟩ U⃗ [ i ]) ≤[ poset-of (𝒪 X) ] V) holds
      † = ⋁[ 𝒪 X ]-least U⃗ (V , φ)

      Ⅰ = nuclei-are-monotone (𝒪 X) 𝒿 ((⋁[ 𝒪 X ] U⃗) , V) †
      Ⅱ = p

 quotient-frame-data : frame-data 𝓤 𝓤 Fixed-Point
 quotient-frame-data = _≤ᶠ_ , 𝟏ᶠ , _∧ᶠ_ , ⋁ᶠ_

 open JoinNotation ⋁ᶠ_

 distributivityᶠ
  : (𝔙 : Fixed-Point)
  → (𝔘⃗ : Fam 𝓤 Fixed-Point)
  → 𝔙 ∧ᶠ (⋁⟨ i ⟩ 𝔘⃗ [ i ]) ＝ ⋁⟨ i ⟩ 𝔙 ∧ᶠ (𝔘⃗ [ i ])
 distributivityᶠ 𝔙@(V , p) 𝔘⃗ = to-subtype-＝ β γ
  where

   U⃗ : Fam 𝓤 ⟨ 𝒪 X ⟩
   U⃗ = ⁅ underlying-open 𝔘⃗ᵢ ∣ 𝔘⃗ᵢ ε 𝔘⃗ ⁆
   β : (U : ⟨ 𝒪 X ⟩) → is-prop (j U ＝ U)
   β _ = carrier-of-[ poset-of (𝒪 X) ]-is-set

   γ : (𝔙 ∧ᶠ (⋁⟨ i ⟩ 𝔘⃗ [ i ])) .pr₁ ＝ (⋁⟨ i ⟩ 𝔙 ∧ᶠ (𝔘⃗ [ i ])) .pr₁
   γ = V ∧[ 𝒪 X ] j (⋁[ 𝒪 X ] U⃗)                        ＝⟨ refl ⟩
       V ∧[ 𝒪 X ] j (⋁[ 𝒪 X ] ⁅ Uᵢ ∣ Uᵢ ε U⃗ ⁆)          ＝⟨ Ⅰ    ⟩
       j V ∧[ 𝒪 X ] j (⋁[ 𝒪 X ] ⁅ Uᵢ ∣ Uᵢ ε U⃗ ⁆)        ＝⟨ Ⅱ    ⟩
       j (V ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ Uᵢ ∣ Uᵢ ε U⃗ ⁆))        ＝⟨ Ⅲ    ⟩
       j (⋁[ 𝒪 X ] ⁅ V ∧[ 𝒪 X ] Uᵢ ∣ Uᵢ ε U⃗ ⁆)          ∎
        where
         Ⅰ = ap (λ - → - ∧[ 𝒪 X ] j (⋁[ 𝒪 X ] U⃗)) (p ⁻¹)
         Ⅱ = 𝓃₃ (𝒪 X) 𝒿 V (⋁[ 𝒪 X ] U⃗) ⁻¹
         Ⅲ = ap j (distributivity (𝒪 X) V U⃗)

 quotient-frame-data-satisfies-frame-laws : satisfies-frame-laws quotient-frame-data
 quotient-frame-data-satisfies-frame-laws =
    ≤ᶠ-is-partial-order
  , (𝟏ᶠ-is-top , (λ { (𝔘 , 𝔙) →  ∧ᶠ-gives-glb 𝔘 𝔙  })
  , ⋁ᶠ-gives-lub
  , λ { (𝔙 , 𝔘⃗) → distributivityᶠ 𝔙 𝔘⃗ })

 quotient-frame-structure : frame-structure 𝓤 𝓤 Fixed-Point
 quotient-frame-structure =
  quotient-frame-data , quotient-frame-data-satisfies-frame-laws

 quotient-frame : Frame (𝓤 ⁺) 𝓤 𝓤
 quotient-frame = Fixed-Point , quotient-frame-structure

 sublocale : Locale (𝓤 ⁺) 𝓤 𝓤
 sublocale =
  record
   { ⟨_⟩ₗ         = Fixed-Point
   ; frame-str-of = quotient-frame-structure
   }

\end{code}
