---
title:        Subobjects in Synthetic Topology
author:       Martin Trucchi
date-started: 2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject

module SyntheticTopology.SubObjects
        (𝓤 𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import SyntheticTopology.Compactness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Discreteness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Overtness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.SetCombinators 𝓤 fe pe pt
open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓥 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

We define notions involving sub-objects (sub-overtness, sub-compactness...)
defined in [2].
We also prove some lemmas that are in [1] and [2].

Because of predicativity, we have to use definitions 2. of 7.2 and 8.2
for subcompactness and subovertness in [2].

\begin{code}

module subdefinitions (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  set-X = pr₂ 𝒳

 is-subcompact : (U : 𝓟 X) → Ω (𝓤 ⁺ ⊔ 𝓥)
 is-subcompact U =
  Ɐ (P , open-P) ꞉ 𝓞 𝒳
   , is-open-proposition (Ɐ x ꞉ X , (x ∈ₚ U) ⇒ x ∈ₚ P)

 is-subcompact' : (U : 𝓟 X) → Ω (𝓤 ⁺ ⊔ 𝓥)
 is-subcompact' U =
  Ɐ (P , open-P) ꞉ 𝓞 𝒳
   , is-open-proposition (Ɐ (x , Ux) ꞉ (𝕋 U) , x ∈ₚ P)

 is-subovert : (U : 𝓟 X) → Ω (𝓤 ⁺ ⊔ 𝓥)
 is-subovert U =
  Ɐ (P , open-P) ꞉ 𝓞 𝒳 , is-open-proposition (Ǝₚ (x , Ux) ꞉ (𝕋 U) , x ∈ₚ P)

\end{code}

First, we can prove that the two notions of subcompactness are equivalent.

\begin{code}

 sub-gives-sub' : (U : 𝓟 X) → is-subcompact U holds → is-subcompact' U holds
 sub-gives-sub' U sub-U (P , open-P) =
  ⇔-open (Ɐ x ꞉ X , x ∈ₚ U ⇒ x ∈ₚ P) (Ɐ (x , Ux) ꞉ (𝕋 U) , x ∈ₚ P)
          ((λ hyp (x , Ux) → hyp x Ux) , λ hyp x Ux → hyp (x , Ux))
          (sub-U ((λ x → x ∈ₚ P) , open-P))


 sub'-gives-sub : (U : 𝓟 X) → is-subcompact' U holds → is-subcompact U holds
 sub'-gives-sub U sub'-U (P , open-P) =
  ⇔-open (Ɐ (x , Ux) ꞉ (𝕋 U) , x ∈ₚ P) (Ɐ x ꞉ X , x ∈ₚ U ⇒ x ∈ₚ P)
          ((λ hyp x Ux → hyp (x , Ux)) , (λ hyp (x , Ux) → hyp x Ux))
          (sub'-U ((λ x → x ∈ₚ P) , open-P))

\end{code}

Then we prove some lemmas.

\begin{code}

 subovert-of-discrete-is-open : (U : 𝓟 X)
                              → is-subovert U holds
                              → is-discrete 𝒳 holds
                              → is-intrinsically-open 𝒳 U holds

 subovert-of-discrete-is-open U subovert-U discrete-X x =
  ⇔-open (Ǝₚ (y , Uy) ꞉ (𝕋 U) , (x ＝ₚ y)) (x ∈ₚ U) (p₁ , p₂) †
   where
    open Equality set-X

    p₁ : ((Ǝₚ (y , Uy) ꞉ (𝕋 U) , (x ＝ₚ y)) ⇒ x ∈ₚ U) holds
    p₁ ex-y = ∥∥-rec (holds-is-prop (x ∈ₚ U))
                     (λ ((y , Uy) , y-eq-x) → transport (_holds ∘ U)
                                                        (y-eq-x ⁻¹)
                                                        Uy)
                     ex-y

    p₂ : (x ∈ₚ U ⇒ Ǝₚ (y , Uy) ꞉ (𝕋 U) , (x ＝ₚ y)) holds
    p₂ Ux = ∣ (x , Ux) , refl ∣

    † : is-open-proposition (Ǝₚ (y , Uy) ꞉ (𝕋 U) , (x ＝ₚ y)) holds
    † = subovert-U ((λ y → x ＝ₚ y) , λ y → discrete-X (x , y))


 subovert-inter-open-subovert : closed-under-binary-meets holds
                              → (Ɐ A ꞉ (𝓟 X) ,
                                  Ɐ (U , _) ꞉ 𝓞 𝒳 ,
                                   is-subovert A
                                    ⇒ is-subovert (A ∩ U)) holds

 subovert-inter-open-subovert cl-∧ A (U , open-U) subovert-A (V , open-V) =
  ⇔-open T-A
         T-A∩U
         (p₁ , p₂)
         (subovert-A (U ∩ V , λ x → cl-∧ (U x) (V x) ((open-U x) , (open-V x))))
   where
    T-A : Ω 𝓤
    T-A = Ǝₚ (x , Ax) ꞉ (𝕋 A) , (x ∈ₚ (U ∩ V))

    T-A∩U : Ω 𝓤
    T-A∩U = Ǝₚ (x , A-U-x) ꞉ (𝕋 (A ∩ U)) , (x ∈ₚ V)

    p₁ : (T-A ⇒ T-A∩U) holds
    p₁ ex-U-V = ∥∥-rec (holds-is-prop T-A∩U)
                       (λ ((x , Ax) , Ux , Vx) → ∣ (x , Ax , Ux) , Vx  ∣)
                       ex-U-V

    p₂ : (T-A∩U ⇒ T-A) holds
    p₂ ex-V = ∥∥-rec (holds-is-prop T-A)
                     (λ ((x , Ax , Ux) , Vx) → ∣ (x , Ax) , Ux , Vx  ∣)
                     ex-V

 open-subset-of-overt-is-subovert : closed-under-binary-meets holds
                                  → (Ɐ (U , _) ꞉ 𝓞 𝒳 ,
                                     is-overt 𝒳 ⇒ is-subovert U) holds

 open-subset-of-overt-is-subovert cl-∧ (U , open-U) overt-X (V , open-V) =
  ⇔-open (Ǝₚ x ꞉ X , x ∈ₚ (U ∩ V))
         (Ǝₚ (x , Ux) ꞉ (𝕋 U) , (x ∈ₚ V))
         ((λ ex-U∩V → ∥∥-rec (holds-is-prop (Ǝₚ (x , Ux) ꞉ (𝕋 U) , (x ∈ₚ V)))
                             (λ (x , Ux , Vx) → ∣ (x , Ux) , Vx ∣)
                             ex-U∩V) ,
           (λ ex-V → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , (x ∈ₚ (U ∩ V))))
                             (λ ((x , Ux) , Vx) → ∣ x , Ux , Vx ∣)
                             ex-V))
         (overt-X ((U ∩ V) , (λ x → cl-∧ (x ∈ₚ U)
                                         (x ∈ₚ V)
                                         ((open-U x) , (open-V x)))))

\end{code}

We have some lemmas that states the consistency of "sub" definitions
related to "plain" ones.

\begin{code}

 compact-iff-subcompact-in-self
  : ((is-compact 𝒳 ⇔ (is-subcompact full))) holds

 compact-iff-subcompact-in-self =
  compact-gives-subcompact , subcompact-gives-compact

  where
    compact-gives-subcompact :
     (is-compact 𝒳 ⇒ is-subcompact full) holds
    compact-gives-subcompact compact-X (U , open-U) =
     ⇔-open (Ɐ x ꞉ X , x ∈ₚ U)
            (Ɐ x ꞉ X , ⊤ ⇒ U x)
            ((λ hyp x _ → hyp x) , (λ hyp x → hyp x ⊤-holds))
            (compact-X (U , open-U))

    subcompact-gives-compact :
     ( is-subcompact full ⇒ is-compact 𝒳) holds
    subcompact-gives-compact = λ subcompact-X (U , open-U) →
     ⇔-open (Ɐ x ꞉ X , ⊤ ⇒ x ∈ₚ U)
            (Ɐ x ꞉ X , x ∈ₚ U)
            ((λ hyp x → hyp x ⊤-holds) , (λ hyp x _ → hyp x))
            (subcompact-X ((λ z → z ∈ₚ U) , open-U))


 overt-iff-subovert-in-self
  : ((is-overt 𝒳 ⇔ (is-subovert full))) holds

 overt-iff-subovert-in-self =
  overt-gives-subovert , subovert-gives-overt
   where
    p₁ : (U : 𝓟 X)
       → ((Ǝₚ x ꞉ X , x ∈ₚ U) ⇒ (Ǝₚ (x , true) ꞉ (𝕋 full) , x ∈ₚ U)) holds
    p₁ U ex-U = ∥∥-rec (holds-is-prop (Ǝₚ (x , true) ꞉ (𝕋 full) , x ∈ₚ U))
                       (λ (x , Ux) → ∣ (x , ⊤-holds) , Ux ∣)
                       ex-U

    p₂ : (U : 𝓟 X)
       → ((Ǝₚ (x , true) ꞉ (𝕋 full) , x ∈ₚ U) ⇒ (Ǝₚ x ꞉ X , x ∈ₚ U)) holds
    p₂ U ex-full = ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , x ∈ₚ U))
                          (λ ((x , true) , Ux) → ∣ x , Ux ∣)
                          ex-full

    overt-gives-subovert :
     (is-overt 𝒳 ⇒ is-subovert full) holds

    overt-gives-subovert overt-X (U , open-U) =
     ⇔-open (Ǝₚ x ꞉ X , x ∈ₚ U)
            (Ǝₚ (x , true) ꞉ (𝕋 full) , U x)
            (p₁ U , p₂ U)
            (overt-X (U , open-U))

    subovert-gives-overt :
     ( is-subovert full ⇒ is-overt 𝒳) holds

    subovert-gives-overt = λ subovert-X (U , open-U) →
      ⇔-open (Ǝₚ (x , true) ꞉ (𝕋 full) , U x)
             (Ǝₚ x ꞉ X , x ∈ₚ U)
             (p₂ U , p₁ U)
             (subovert-X (U , open-U))
\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
