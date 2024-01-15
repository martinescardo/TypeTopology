Ayberk Tosun, 23 April 2022 (date started)

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Size

\end{code}

\begin{code}[hide]

module Locales.PatchProperties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
         where

open import UF.Subsingletons
open import UF.Logic
open import UF.Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Locales.Frame pt fe
open import Locales.AdjointFunctorTheoremForFrames pt fe

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.Nucleus pt fe
open import Locales.PatchLocale pt fe sr
open import Locales.HeytingImplication pt fe
open import Locales.Compactness pt fe
open import Locales.CompactRegular pt fe using (∨-is-scott-continuous)
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap    pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.CharacterisationOfContinuity pt fe
open import Locales.PerfectMaps pt fe
open import Locales.Complements pt fe
open import Locales.Clopen      pt fe sr
open import Locales.ZeroDimensionality pt fe sr
open import Locales.Stone pt fe sr
open import Locales.StoneImpliesSpectral pt fe sr
open import Locales.Regular pt fe sr

open Locale

\end{code}

\section{Basic properties}

\begin{code}

module BasicProperties (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral X holds) where

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X;
                                      Patch to Patch-of-X)

\end{code}

We first prove the following lemma about directed families of nuclei, which
amounts the fact that the directification of an already directed family is
cofinal in the original family.

\begin{code}

 directedness-lemma : (K : Fam 𝓦 Perfect-Nucleus-on-X)
                    → is-directed (𝒪 Patch-of-X) K holds
                    → let
                       K₀ = ⁅ pr₁ k ∣ k ε K ⁆
                      in
                       (is : index (𝔡𝔦𝔯 K₀))
                    → ∃ i ꞉ index K , (((𝔡𝔦𝔯 K₀ [ is ]) ≼₀ (K₀ [ i ])) holds )
 directedness-lemma K δ []       = ∥∥-rec ∃-is-prop γ β
  where
   open PosetReasoning (poset-of (𝒪 X))

   K₀ = ⁅ pr₁ k ∣ k ε K ⁆

   β : ∥ index K ∥
   β = directedness-entails-inhabitation (𝒪 Patch-of-X) K δ

   γ : index K → _
   γ i = ∣ i , 𝓃₁ (𝒪 X) (nucleus-of (K [ i ])) ∣
 directedness-lemma K δ (i ∷ is) = ∥∥-rec ∃-is-prop γ IH
  where
   open PosetReasoning (poset-of (𝒪 X))

   K₀ = ⁅ pr₁ k ∣ k ε K ⁆
   K₁ = ⁅ nucleus-of k ∣ k ε K ⁆

   γ : (Σ j ꞉ index K , (((𝔡𝔦𝔯 K₀ [ is ]) ≼₀ (K₀ [ j ])) holds))
     → _
   γ (j , φ) = ∥∥-rec ∃-is-prop ※ (pr₂ δ i j)
    where
     ※ : _ → _
     ※ (l , ψ₁ , ψ₂) = ∣ l , † ∣
      where
       † : ((𝔡𝔦𝔯 K₀ [ i ∷ is ]) ≼₀ (K₀ [ l ])) holds
       † U = (𝔡𝔦𝔯 K₀ [ is ]) ((K₀ [ i ]) U)    ≤⟨ ♥ ⟩
             (K₀ [ j ]) ((K₀ [ i ]) U)         ≤⟨ ♠ ⟩
             (K₀ [ j ]) ((K₀ [ l ]) U)         ≤⟨ ♣ ⟩
             (K₀ [ l ]) ((K₀ [ l ]) U)         ＝⟨ ♢ ⟩ₚ
             (K₀ [ l ]) U                      ■
              where
               ♥ = φ ((K₀ [ i ]) U)
               ♠ = nuclei-are-monotone (𝒪 X) (K₁ [ j ]) _ (ψ₁ U)
               ♣ = ψ₂ ((K₀ [ l ]) U)
               ♢ = nuclei-are-idempotent (𝒪 X) (K₁ [ l ]) U

   IH : ∃ j ꞉ index K , (((𝔡𝔦𝔯 K₀ [ is ]) ≼₀ (K₀ [ j ])) holds)
   IH = directedness-lemma K δ is

\end{code}

\begin{code}

 directed-joins-are-computed-pointwise : (K : Fam 𝓦 Perfect-Nucleus-on-X)
                                       → is-directed (𝒪 Patch-of-X) K holds
                                       → (U : ⟨ 𝒪 X ⟩)
                                       → (⋁[ 𝒪 Patch-of-X ] K) $ U ＝ ⋁[ 𝒪 X ] ⁅ k $ U ∣ k ε K ⁆
 directed-joins-are-computed-pointwise K δ U =
  ≤-is-antisymmetric (poset-of (𝒪 X)) β γ
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
    open PosetReasoning (poset-of (𝒪 X))

    𝓁𝒽𝓈 = (⋁[ 𝒪 Patch-of-X ] K) $ U
    𝓇𝒽𝓈 = ⋁[ 𝒪 X ] ⁅ k $ U ∣ k ε K ⁆

    K₀ = ⁅ _$_ k ∣ k ε K ⁆

    ‡ : cofinal-in (𝒪 X) ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ ⁅ k $ U ∣ k ε K ⁆ holds
    ‡ is = ∥∥-rec ∃-is-prop (λ (j , φ) → ∣ j , φ U ∣) (directedness-lemma K δ is)

    β : (𝓁𝒽𝓈 ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
    β = cofinal-implies-join-covered (𝒪 X) _ _ ‡

    γ : (𝓇𝒽𝓈 ≤[ poset-of (𝒪 X) ] 𝓁𝒽𝓈) holds
    γ = ⋁[ 𝒪 X ]-least ⁅ k $ U ∣ k ε K ⁆ (𝓁𝒽𝓈 , †)
     where
      † : (𝓁𝒽𝓈 is-an-upper-bound-of ⁅ k $ U ∣ k ε K ⁆) holds
      † i = ⋁[ 𝒪 Patch-of-X ]-upper K i U

\end{code}

\section{Open and closed nuclei}

\begin{code}

module ClosedNucleus (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral X holds) where

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)

 ‘_’ : ⟨ 𝒪 X ⟩ → Perfect-Nucleus-on-X
 ‘ U ’ = binary-join (𝒪 X) U , ∨-is-nucleus (𝒪 X) U , ∨-is-scott-continuous (𝒪 X) U

\end{code}

\begin{code}

module OpenNucleus (X  : Locale 𝓤 𝓥 𝓥)
                   (σᴰ : spectralᴰ X)
                   (sk : 𝒦 X is 𝓥 small) where

 private
  σ : is-spectral X holds
  σ = spectralᴰ-gives-spectrality X σᴰ

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)

 private
  X-has-small-basis : ∥ basisᴰ (𝒪 X) ∥
  X-has-small-basis = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 open HeytingImplicationConstruction X X-has-small-basis

 opn : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 opn U = U ==>_

 opn-monotone : (U : ⟨ 𝒪 X ⟩)
              → is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 X)) (opn U) holds
 opn-monotone U (V , W) p = heyting-implication₁ U W (U ==> V) †
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (((U ==> V) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] W) holds
   † = (U ==> V) ∧[ 𝒪 X ] U ≤⟨ mp-right U V ⟩ V ≤⟨ p ⟩ W ■

 opn-is-inflationary : (U : ⟨ 𝒪 X ⟩) → is-inflationary (𝒪 X) (opn U) holds
 opn-is-inflationary U V = heyting-implication₁ U V V (∧[ 𝒪 X ]-lower₁ V U)

 opn-is-idempotent : (U : ⟨ 𝒪 X ⟩) → is-idempotent (𝒪 X) (opn U) holds
 opn-is-idempotent U V = heyting-implication₁ U V (U ==> (U ==> V)) γ
  where
   open PosetReasoning (poset-of (𝒪 X))

   γ : (((U ==> (U ==> V)) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] V) holds
   γ = (U ==> (U ==> V)) ∧[ 𝒪 X ] U                ＝⟨ i    ⟩ₚ
       (U ==> (U ==> V)) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U)   ＝⟨ ii   ⟩ₚ
       ((U ==> (U ==> V)) ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] U   ≤⟨ iii  ⟩
       (U ==> V) ∧[ 𝒪 X ] U                        ≤⟨ iv   ⟩
       V                                           ■
        where
         i   = ap (λ - → (U ==> (U ==> V)) ∧[ 𝒪 X ] -) (∧[ 𝒪 X ]-is-idempotent U)
         ii  = ∧[ 𝒪 X ]-is-associative (U ==> (U ==> V)) U U
         iii = ∧[ 𝒪 X ]-left-monotone
                (modus-ponens X (==>-is-heyting-implication U (U ==> V)))
         iv  = modus-ponens X (==>-is-heyting-implication U V)

 opn-preserves-meets : (U : ⟨ 𝒪 X ⟩)
                     → preserves-binary-meets (𝒪 X) (𝒪 X) (opn U) holds
 opn-preserves-meets U V W = ≤-is-antisymmetric (poset-of (𝒪 X)) β γ
  where
   open PosetReasoning (poset-of (𝒪 X))

   β : ((U ==> (V ∧[ 𝒪 X ] W))
          ≤[ poset-of (𝒪 X) ]
        (U ==> V ∧[ 𝒪 X ] (U ==> W)))
       holds
   β = ∧[ 𝒪 X ]-greatest (U ==> V) (U ==> W) (U ==> meet-of (𝒪 X) V W) β₁ β₂
        where
         δ₁ : ((U ==> (V ∧[ 𝒪 X ] W) ∧[ 𝒪 X ] U) ≤ V) holds
         δ₁ = (U ==> (V ∧[ 𝒪 X ] W)) ∧[ 𝒪 X ] U  ≤⟨ mp-right U (V ∧[ 𝒪 X ] W) ⟩
              V ∧[ 𝒪 X ] W                       ≤⟨ ∧[ 𝒪 X ]-lower₁ V W       ⟩
              V                                  ■

         β₁ : ((U ==> (V ∧[ 𝒪 X ] W)) ≤[ poset-of (𝒪 X) ] (U ==> V)) holds
         β₁ = heyting-implication₁ U V (U ==> (V ∧[ 𝒪 X ] W)) δ₁

         δ₂ : ((U ==> (V ∧[ 𝒪 X ] W) ∧[ 𝒪 X ] U) ≤ W) holds
         δ₂ = (U ==> (V ∧[ 𝒪 X ] W)) ∧[ 𝒪 X ] U  ≤⟨ mp-right U (V ∧[ 𝒪 X ] W) ⟩
              V ∧[ 𝒪 X ] W                       ≤⟨ ∧[ 𝒪 X ]-lower₂ V W       ⟩
              W                                  ■

         β₂ : ((U ==> (V ∧[ 𝒪 X ] W)) ≤[ poset-of (𝒪 X) ] (U ==> W)) holds
         β₂ = heyting-implication₁ U W (U ==> (V ∧[ 𝒪 X ] W)) δ₂

   γ : (((U ==> V) ∧[ 𝒪 X ] (U ==> W))
          ≤[ poset-of (𝒪 X) ]
        (U ==> (V ∧[ 𝒪 X ] W)))
        holds
   γ = heyting-implication₁ U (V ∧[ 𝒪 X ] W) ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) δ
        where
         i   = ap
               (λ - → ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] -)
               (∧[ 𝒪 X ]-is-idempotent U)
         ii  = ∧[ 𝒪 X ]-is-associative (U ==> V) (U ==> W) (U ∧[ 𝒪 X ] U) ⁻¹
         iii = ap
               (λ - → (U ==> V) ∧[ 𝒪 X ] -)
               (∧[ 𝒪 X ]-is-associative (U ==> W) U U)
         iv  = ∧[ 𝒪 X ]-right-monotone (∧[ 𝒪 X ]-left-monotone (mp-right U W))
         v   = ap (λ - → meet-of (𝒪 X) (U ==> V) -) (∧[ 𝒪 X ]-is-commutative W U)
         vi  = ∧[ 𝒪 X ]-is-associative (U ==> V) U W
         vii = ∧[ 𝒪 X ]-left-monotone (mp-right U V)

         δ : ((((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] U)
               ≤[ poset-of (𝒪 X) ]
              (V ∧[ 𝒪 X ] W)) holds
         δ = ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] U               ＝⟨ i   ⟩ₚ
             ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U)  ＝⟨ ii  ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] ((U ==> W) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U))  ＝⟨ iii ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] (((U ==> W) ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] U)  ≤⟨ iv  ⟩
             (U ==> V) ∧[ 𝒪 X ] (W ∧[ 𝒪 X ] U)                       ＝⟨ v   ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] W)                       ＝⟨ vi  ⟩ₚ
             ((U ==> V) ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] W                       ≤⟨ vii ⟩
             V ∧[ 𝒪 X ] W ■

 opn-perfect : ((K , _) : 𝒦 X) → is-perfect (opn K) holds
 opn-perfect (K , κ) = characterisation-of-continuity X X σ (opn K) (opn-monotone K) γ
   where
    open PosetReasoning (poset-of (𝒪 X))

    γ : continuity-condition X X (opn K) holds
    γ K₂ U κ₂ p = ∣ (K ∧[ 𝒪 X ] K₂) , κ′ , ♠ , ♥ ∣
     where
      κ′ : is-compact-open X (K ∧[ 𝒪 X ] K₂) holds
      κ′ = binary-coherence X σ K K₂ κ κ₂

      ♠ : ((K ∧[ 𝒪 X ] K₂) ≤[ poset-of (𝒪 X) ] U) holds
      ♠ = K ∧[ 𝒪 X ] K₂          ≤⟨ i  ⟩
          K ∧[ 𝒪 X ] (K ==> U)   ≤⟨ ii ⟩
          U                      ■
           where
            i  = ∧[ 𝒪 X ]-right-monotone p
            ii = mp-left K U

      ♣ : ((K₂ ∧[ 𝒪 X ] K) ≤[ poset-of (𝒪 X) ] (K ∧[ 𝒪 X ] K₂)) holds
      ♣ = reflexivity+ (poset-of (𝒪 X)) (∧[ 𝒪 X ]-is-commutative K₂ K)

      ♥ : (K₂ ≤[ poset-of (𝒪 X) ] opn K (K ∧[ 𝒪 X ] K₂)) holds
      ♥ = heyting-implication₁ K (K ∧[ 𝒪 X ] K₂) K₂ ♣

 opn-is-nucleus : (U : ⟨ 𝒪 X ⟩) → is-nucleus (𝒪 X) (opn U) holds
 opn-is-nucleus U = opn-is-inflationary U
                  , opn-is-idempotent U
                  , opn-preserves-meets U

 ¬‘_’ : 𝒦 X → Perfect-Nucleus-on-X
 ¬‘ (K , κ) ’ = K ==>_ , (opn-is-nucleus K , opn-perfect (K , κ))

\end{code}

\begin{code}

 opn-reverses-binary-joins : (U V : ⟨ 𝒪 X ⟩) → opn (U ∨[ 𝒪 X ] V) ＝ opn U ⋏₀ opn V
 opn-reverses-binary-joins U V = dfunext fe γ
  where
   open PosetReasoning (poset-of (𝒪 X))

   γ : opn (U ∨[ 𝒪 X ] V) ∼ (opn U ⋏₀ opn V)
   γ W = ≤-is-antisymmetric (poset-of (𝒪 X)) δ ε
    where
     δ : (((U ∨[ 𝒪 X ] V) ==> W) ≤ (U ==> W ∧[ 𝒪 X ] V ==> W)) holds
     δ = ∧[ 𝒪 X ]-greatest (U ==> W) (V ==> W) _ δ₁ δ₂
      where
       † : (((opn (U ∨[ 𝒪 X ] V) W) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] W) holds
       † = ((U ∨[ 𝒪 X ] V) ==> W) ∧[ 𝒪 X ] U               ≤⟨ i ⟩
           ((U ∨[ 𝒪 X ] V) ==> W) ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)  ≤⟨ ii ⟩
           W                                               ■
            where
             i   = ∧[ 𝒪 X ]-right-monotone (∨[ 𝒪 X ]-upper₁ U V)
             ii  = modus-ponens X (==>-is-heyting-implication (U ∨[ 𝒪 X ] V) W)

       ‡ : ((opn (U ∨[ 𝒪 X ] V) W ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 X) ] W) holds
       ‡ = opn (U ∨[ 𝒪 X ] V) W ∧[ 𝒪 X ] V               ≤⟨ i  ⟩
           opn (U ∨[ 𝒪 X ] V) W ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)  ≤⟨ ii ⟩
           W ■
            where
             i  = ∧[ 𝒪 X ]-right-monotone (∨[ 𝒪 X ]-upper₂ U V)
             ii = modus-ponens X (==>-is-heyting-implication (U ∨[ 𝒪 X ] V) W)

       δ₁ : (opn (U ∨[ 𝒪 X ] V) W ≤[ poset-of (𝒪 X) ] (U ==> W)) holds
       δ₁ = heyting-implication₁ U W _ †

       δ₂ :  (opn (U ∨[ 𝒪 X ] V) W ≤[ poset-of (𝒪 X) ] (V ==> W)) holds
       δ₂ = heyting-implication₁ V W _ ‡

     ε₁ : ((U ==> W ∧[ 𝒪 X ] V ==> W ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)) ≤ W) holds
     ε₁ =
      T ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)                                              ＝⟨ i   ⟩ₚ
      (T ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] (T ∧[ 𝒪 X ] V)                                 ≤⟨ ii  ⟩
      (U ==> W ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] ((U ==> W ∧[ 𝒪 X ] V ==> W) ∧[ 𝒪 X ] V)  ≤⟨ iii ⟩
      W ∨[ 𝒪 X ] ((U ==> W ∧[ 𝒪 X ] V ==> W) ∧[ 𝒪 X ] V)                     ≤⟨ iv  ⟩
      W ∨[ 𝒪 X ] (V ==> W ∧[ 𝒪 X ] V)                                        ≤⟨ v   ⟩
      W ∨[ 𝒪 X ] W                                                           ≤⟨ vi  ⟩
      W                                                                      ■
       where
        T   = (U ==> W) ∧[ 𝒪 X ] (V ==> W)
        i   = binary-distributivity (𝒪 X) _ U V
        ii  = ∨[ 𝒪 X ]-left-monotone
               (∧[ 𝒪 X ]-left-monotone
               (∧[ 𝒪 X ]-lower₁ (opn U W) (opn V W)))
        iii = ∨[ 𝒪 X ]-left-monotone
               (modus-ponens
               X
               (==>-is-heyting-implication U W))
        iv  = ∨[ 𝒪 X ]-right-monotone
               (∧[ 𝒪 X ]-left-monotone
               (∧[ 𝒪 X ]-lower₂ (U ==> W) (V ==> W)))
        v   = ∨[ 𝒪 X ]-right-monotone
               (modus-ponens X (==>-is-heyting-implication V W))
        vi  = ∨[ 𝒪 X ]-least
               (≤-is-reflexive (poset-of (𝒪 X)) W)
               (≤-is-reflexive (poset-of (𝒪 X)) W)

     ε : ((opn U W ∧[ 𝒪 X ] opn V W)
            ≤[ poset-of (𝒪 X) ]
          opn (U ∨[ 𝒪 X ] V) W) holds
     ε = heyting-implication₁ (U ∨[ 𝒪 X ] V) W (opn U W ∧[ 𝒪 X ] opn V W) ε₁

 nuclei-preserve-==> : (U V : ⟨ 𝒪 X ⟩) ((j , _) : Nucleus (𝒪 X))
                                      → ((U ==> V) ≤[ poset-of (𝒪 X) ] (j U ==> j V)) holds
 nuclei-preserve-==> U V 𝒿@(j , _) = U ==> V        ≤⟨ † ⟩
                                     U ==> j V      ≤⟨ ‡ ⟩
                                     j U ==> j V    ■
  where
   open PosetReasoning (poset-of (𝒪 X))

   ♠ : (((U ==> V) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] j V) holds
   ♠ = (U ==> V) ∧[ 𝒪 X ] U ≤⟨ mp-right U V ⟩ V ≤⟨ 𝓃₁ (𝒪 X) 𝒿 V ⟩ j V ■

   ♣ : (((U ==> j V) ∧[ 𝒪 X ] (j U)) ≤[ poset-of (𝒪 X) ] j V) holds
   ♣ = (U ==> j V) ∧[ 𝒪 X ] j U     ≤⟨ i  ⟩
       j (U ==> j V) ∧[ 𝒪 X ] j U   ＝⟨ ii ⟩ₚ
       j ((U ==> j V) ∧[ 𝒪 X ] U)   ≤⟨ iii ⟩
       j (j V)                      ＝⟨ iv ⟩ₚ
       j V                          ■
        where
         i   = ∧[ 𝒪 X ]-left-monotone (𝓃₁ (𝒪 X) 𝒿 (U ==> j V))
         ii  = 𝓃₃ (𝒪 X) 𝒿 (U ==> j V) U ⁻¹
         iii = nuclei-are-monotone (𝒪 X) 𝒿 _ (mp-right U (j V))
         iv  = nuclei-are-idempotent (𝒪 X) 𝒿 V

   † = heyting-implication₁ U (j V) (U ==> V) ♠
   ‡ = heyting-implication₁ (j U) (j V) (U ==> j V) ♣

\end{code}

\begin{code}

module Epsilon (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ X) where

 private
  σ : is-spectral X holds
  σ = spectralᴰ-gives-spectrality X σᴰ

  ℬ↑ : Fam 𝓤 ⟨ 𝒪 X ⟩
  ℬ↑ = basisₛ X σᴰ

  d : directed-basisᴰ (𝒪 X)
  d = ℬ↑ , basisₛ-is-directed-basis X σᴰ

  β : has-basis (𝒪 X) holds
  β = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

  κ : consists-of-compact-opens X ℬ↑ holds
  κ = basisₛ-consists-of-compact-opens X σᴰ

 sk : 𝒦 X is 𝓤 small
 sk = 𝒦-is-small X d κ (local-smallness X)

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)
 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open ClosedNucleus X σ
 open OpenNucleus X σᴰ sk
 open HeytingImplicationConstruction X β

 𝟎ₖ : 𝒦 X
 𝟎ₖ = 𝟎[ 𝒪 X ] , 𝟎-is-compact X

 ¬‘’-reflects-𝟎 : ¬‘ 𝟎ₖ ’ ＝ 𝟏[ 𝒪 Patchₛ-X ]
 ¬‘’-reflects-𝟎 = only-𝟏-is-above-𝟏 (𝒪 Patchₛ-X) ¬‘ 𝟎ₖ ’ †
  where
   open PosetReasoning (poset-of (𝒪 X))

   † :  (𝟏[ 𝒪 Patchₛ-X ] ≤[ poset-of (𝒪 Patchₛ-X) ] ¬‘ 𝟎ₖ ’) holds
   † i = ex-falso-quodlibet (ℬ [ i ])

 ϵ-preserves-𝟏 : ‘ 𝟏[ 𝒪 X ] ’ ＝ 𝟏[ 𝒪 Patchₛ-X ]
 ϵ-preserves-𝟏 = perfect-nuclei-eq ‘ 𝟏[ 𝒪 X ] ’ 𝟏[ 𝒪 Patchₛ-X ] (dfunext fe †)
  where
   † : (U : ⟨ 𝒪 X ⟩) → 𝟏[ 𝒪 X ] ∨[ 𝒪 X ] U ＝ 𝟏[ 𝒪 X ]
   † U = 𝟏-left-annihilator-for-∨ (𝒪 X) U

 ϵ-preserves-⋁ : let
                  open Joins (λ x y → x ≤[ poset-of (𝒪 Patchₛ-X) ] y)
                 in
                  (Ɐ S ꞉ Fam 𝓤 ⟨ 𝒪 X ⟩ , ‘ ⋁[ 𝒪 X ] S ’ is-lub-of ⁅ ‘ U ’ ∣ U ε S ⁆) holds
 ϵ-preserves-⋁ S = † , ‡
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 Patchₛ-X) ] y)
   open PosetReasoning (poset-of (𝒪 X))

   † : (‘ ⋁[ 𝒪 X ] S ’ is-an-upper-bound-of ⁅ ‘ U ’ ∣ U ε S ⁆) holds
   † i j = ∨[ 𝒪 X ]-least ♥ ♠
      where
       ♥ : ((S [ i ]) ≤[ poset-of (𝒪 X) ] ‘ ⋁[ 𝒪 X ] S ’ .pr₁ (ℬ [ j ])) holds
       ♥ = S [ i ]                         ≤⟨ ⋁[ 𝒪 X ]-upper S i ⟩
           ⋁[ 𝒪 X ] S                      ≤⟨ ∨[ 𝒪 X ]-upper₁ (⋁[ 𝒪 X ] S) (ℬ [ j ]) ⟩
           (⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (ℬ [ j ]) ■

       ♠ : ((ℬ [ j ]) ≤[ poset-of (𝒪 X) ] ((⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (ℬ [ j ]))) holds
       ♠ = ∨[ 𝒪 X ]-upper₂ (⋁[ 𝒪 X ] S) (ℬ [ j ])

   ‡ : (Ɐ (𝒿 , _) ꞉ upper-bound ⁅ ‘ U ’ ∣ U ε S ⁆ ,
         ‘ ⋁[ 𝒪 X ] S ’ ≤[ poset-of (𝒪 Patchₛ-X) ] 𝒿) holds
   ‡ (𝒿@(j , _) , ψ) i =
    ∨[ 𝒪 X ]-least δ (𝓃₁ (𝒪 X) (nucleus-of 𝒿) (ℬ [ i ]))
     where
      δ : ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] j (ℬ [ i ])) holds
      δ = ⋁[ 𝒪 X ]-least S (j (ℬ [ i ]) , ε)
       where
        open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
         renaming (_is-an-upper-bound-of_ to _is-an-upper-bound-of₀_)

        ε : (j (ℬ [ i ]) is-an-upper-bound-of₀ S) holds
        ε l =
         S [ l ]                      ≤⟨ ∨[ 𝒪 X ]-upper₁ (S [ l ]) (ℬ [ i ]) ⟩
         (S [ l ]) ∨[ 𝒪 X ] (ℬ [ i ]) ≤⟨ ψ l i                               ⟩
         j (ℬ [ i ])                  ■

 ϵ : Patchₛ-X ─c→ X
 ϵ = ‘_’ , ϵ-preserves-𝟏 , β′ , ϵ-preserves-⋁
  where
   β′ : preserves-binary-meets (𝒪 X) (𝒪 Patchₛ-X) ‘_’ holds
   β′ U V = perfect-nuclei-eq
            ‘ U ∧[ 𝒪 X ] V ’
            (‘ U ’ ∧[ 𝒪 Patchₛ-X ] ‘ V ’)
            (dfunext fe †)
    where
     † : (W : ⟨ 𝒪 X ⟩) → ‘ U ∧[ 𝒪 X ] V ’ $ W ＝ (‘ U ’ ∧[ 𝒪 Patchₛ-X ] ‘ V ’) $ W
     † W = (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] W                ＝⟨ i   ⟩
           W ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] V)                ＝⟨ ii  ⟩
           (W ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] V)   ＝⟨ iii ⟩
           (U ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] V)   ＝⟨ iv  ⟩
           (U ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] (V ∨[ 𝒪 X ] W)   ∎
            where
             i   = ∨[ 𝒪 X ]-is-commutative (U ∧[ 𝒪 X ] V) W
             ii  = binary-distributivity-op (𝒪 X) W U V
             iii = ap
                    (λ - → - ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] V))
                    (∨[ 𝒪 X ]-is-commutative W U)
             iv  = ap
                    (λ - →  (U ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] -)
                    (∨[ 𝒪 X ]-is-commutative W V)

   open Joins (λ x y → x ≤[ poset-of (𝒪 Patchₛ-X) ] y)

 𝒷 : has-basis (𝒪 X) holds
 𝒷 = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 open PerfectMaps Patchₛ-X X
 open AdjointFunctorTheorem Patchₛ-X X 𝒷
 open BasicProperties X σ
 open PatchConstruction X σ using () renaming (Patch to Patch-of-X)

\end{code}

The right adjoint `ϵ⁎` of `ϵ` is the function applying a given perfect nucleus
to the bottom element `𝟎` of the locale in consideration.

\begin{code}

 ϵ⁎-is-application-to-𝟎 : (𝒿 : Perfect-Nucleus-on-X)
                        → ϵ ⁎· 𝒿 ＝ 𝒿 $ 𝟎[ 𝒪 X ]
 ϵ⁎-is-application-to-𝟎 𝒿@(j , _) =
  ≤-is-antisymmetric (poset-of (𝒪 X)) β′ γ
   where

\end{code}

We break this up into two directions by using antisymmetry: `β` and `γ`.
The nontrivial direction is the `β` direction, so let's get the trivial
`γ` direction out of the way first:

\begin{code}

    γ : (j 𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] (ϵ ⁎· 𝒿)) holds
    γ = adjunction-inequality-forward ϵ 𝒿 (j 𝟎[ 𝒪 X ]) †
     where
      † : (‘ j 𝟎[ 𝒪 X ] ’ ≤[ poset-of (𝒪 Patchₛ-X) ] 𝒿) holds
      † i = ∨[ 𝒪 X ]-least ‡₁ ‡₂
       where
        ‡₁ : (j 𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] j (ℬ [ i ])) holds
        ‡₁ = nuclei-are-monotone (𝒪 X) (nucleus-of 𝒿) _ (𝟎-is-bottom (𝒪 X) (ℬ [ i ]))

        ‡₂ : ((ℬ [ i ]) ≤[ poset-of (𝒪 X) ] j (ℬ [ i ])) holds
        ‡₂ = 𝓃₁ (𝒪 X) (nucleus-of 𝒿) (ℬ [ i ])

\end{code}

We use Yoneda for the `β` direction.

\begin{code}

    β′ : ((ϵ ⁎· 𝒿) ≤[ poset-of (𝒪 X) ] j 𝟎[ 𝒪 X ]) holds
    β′ = yoneda (𝒪 X) (ϵ ⁎· 𝒿) (j 𝟎[ 𝒪 X ]) †
     where
      open PosetReasoning (poset-of (𝒪 X))

      † : (z : ⟨ 𝒪 X ⟩)
        → (rel-syntax (poset-of (𝒪 X)) z (ϵ ⁎· (j , _))
        ⇒ rel-syntax (poset-of (𝒪 X)) z (j 𝟎[ 𝒪 X ])) holds
      † U φ = U                   ≤⟨ ∨[ 𝒪 X ]-upper₁ U 𝟎[ 𝒪 X ] ⟩
              U ∨[ 𝒪 X ] 𝟎[ 𝒪 X ] ≤⟨ η                          ⟩
              j 𝟎[ 𝒪 X ]          ■
       where
        ζ : (‘ U ’ ≤[ poset-of (𝒪 Patchₛ-X) ] 𝒿) holds
        ζ = adjunction-inequality-backward ϵ 𝒿 U φ

        η : ((U ∨[ 𝒪 X ] 𝟎[ 𝒪 X ]) ≤[ poset-of (𝒪 X) ] j 𝟎[ 𝒪 X ]) holds
        η = ≼ᵏ-implies-≼ ‘ U ’ 𝒿 ζ 𝟎[ 𝒪 X ]

\end{code}

\begin{code}

 ϵ-is-a-perfect-map : is-perfect-map 𝒷 ϵ holds
 ϵ-is-a-perfect-map 𝒦 δ =
  transport (λ - → (- is-lub-of ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆) holds) (γ ⁻¹) †
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    δ′ : is-directed (𝒪 Patch-of-X) 𝒦 holds
    δ′ = pr₁ δ , ζ
     where
      ζ : (Ɐ i ꞉ index 𝒦 , Ɐ j ꞉ index 𝒦 ,
            Ǝ k ꞉ index 𝒦 , (((𝒦 [ i ]) ≼ (𝒦 [ k ])) holds)
                          × (((𝒦 [ j ]) ≼ (𝒦 [ k ])) holds)) holds
      ζ i j = ∥∥-rec ∃-is-prop η (pr₂ δ i j)
       where
        η : _
        η (k , φ , ψ) =
                      ∣ k
                      , ≼ᵏ-implies-≼ (𝒦 [ i ]) (𝒦 [ k ]) φ
                      , ≼ᵏ-implies-≼ (𝒦 [ j ]) (𝒦 [ k ]) ψ
                      ∣

    γ : ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦) ＝ ⋁[ 𝒪 X ] ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆
    γ = ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦)            ＝⟨ i   ⟩
        (⋁[ 𝒪 Patchₛ-X ] 𝒦) $ 𝟎[ 𝒪 X ]      ＝⟨ ii  ⟩
        ⋁[ 𝒪 X ] ⁅ k $ 𝟎[ 𝒪 X ] ∣ k ε 𝒦 ⁆   ＝⟨ iii ⟩
        ⋁[ 𝒪 X ] ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆         ∎
          where
           ※   : (i : index 𝒦) → (𝒦 [ i ]) $ 𝟎[ 𝒪 X ] ＝ ϵ ⁎· (𝒦 [ i ])
           ※   = λ i → ϵ⁎-is-application-to-𝟎 (𝒦 [ i ]) ⁻¹

           i   = ϵ⁎-is-application-to-𝟎 (⋁[ 𝒪 Patchₛ-X ] 𝒦)
           ii  = directed-joins-are-computed-pointwise 𝒦 δ′ 𝟎[ 𝒪 X ]
           iii = ap (λ - → ⋁[ 𝒪 X ] (index 𝒦 , -)) (dfunext fe ※)

    † : ((⋁[ 𝒪 X ] ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆) is-lub-of ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆) holds
    † = ⋁[ 𝒪 X ]-upper ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆ , ⋁[ 𝒪 X ]-least ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆

\end{code}

\section{Open and Closed Nuclei are Complements}

\begin{code}

module PatchComplementation (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ X) where

 σ : is-spectral X holds
 σ = spectralᴰ-gives-spectrality X σᴰ

 ℬ↑ : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬ↑ = basisₛ X σᴰ

 d : directed-basisᴰ (𝒪 X)
 d = ℬ↑ , basisₛ-is-directed-basis X σᴰ

 β : has-basis (𝒪 X) holds
 β = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 κ : consists-of-compact-opens X ℬ↑ holds
 κ = basisₛ-consists-of-compact-opens X σᴰ

 sk : 𝒦 X is 𝓤 small
 sk = 𝒦-is-small X d κ (local-smallness X)

 X-has-small-basis : ∥ basisᴰ (𝒪 X) ∥
 X-has-small-basis = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open PatchConstruction X σ using (_$_; 𝔡𝔦𝔯)
 open ClosedNucleus X σ
 open OpenNucleus   X σᴰ sk
 open HeytingImplicationConstruction X X-has-small-basis

 open-complements-closed : (K : ⟨ 𝒪 X ⟩)
                         → (κ : is-compact-open X K holds)
                         → (is-boolean-complement-of (𝒪 Patchₛ-X) ¬‘ (K , κ) ’ ‘ K ’ ) holds
 open-complements-closed K κ = † , ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   †₁ : ((‘ K ’ ∧[ 𝒪 Patchₛ-X ] ¬‘ (K , κ) ’)
         ≤[ poset-of (𝒪 Patchₛ-X) ]
         𝟎[ 𝒪 Patchₛ-X ]) holds
   †₁ l =
    (K ∨[ 𝒪 X ] (ℬ [ l ])) ∧[ 𝒪 X ] ((K ==> (ℬ [ l ])))                           ＝⟨ Ⅰ ⟩ₚ
    (K ∧[ 𝒪 X ] (K ==> (ℬ [ l ]))) ∨[ 𝒪 X ] (ℬ [ l ] ∧[ 𝒪 X ] (K ==> (ℬ [ l ])))  ≤⟨ Ⅱ ⟩
    (ℬ [ l ]) ∨[ 𝒪 X ] (ℬ [ l ] ∧[ 𝒪 X ] (K ==> (ℬ [ l ])))                       ≤⟨ Ⅲ ⟩
    ℬ [ l ]                                                                       ＝⟨ Ⅳ ⟩ₚ
    𝟎[ 𝒪 Patchₛ-X ] $ (ℬ [ l ])                                                   ■
     where
      Ⅰ =  binary-distributivity-right (𝒪 X)
      Ⅱ = ∨[ 𝒪 X ]-left-monotone (mp-left K (ℬ [ l ]))
      Ⅲ = ∨[ 𝒪 X ]-least ♥ ♠
           where
            ♥ = ≤-is-reflexive (poset-of (𝒪 X)) (ℬ [ l ])
            ♠ = ∧[ 𝒪 X ]-lower₁ (ℬ [ l ]) (K ==> (ℬ [ l ]))
      Ⅳ = 𝟎-is-id (ℬ [ l ]) ⁻¹

   ‡₁ : (𝟏[ 𝒪 Patchₛ-X ] ≼ᵏ (‘ K ’ ∨[ 𝒪 Patchₛ-X ] ¬‘ (K , κ) ’)) holds
   ‡₁ l =
     𝟏[ 𝒪 X ]                                                 ≤⟨ Ⅰ ⟩
     K ==> (K ∨[ 𝒪 X ] (ℬ [ l ]))                             ≤⟨ Ⅱ ⟩
     (‘ K ’ ∨[ 𝒪 Patchₛ-X ] ¬‘ (K , κ) ’) $ (ℬ [ l ])         ■
      where
       ※ : ((𝟏[ 𝒪 X ] ∧[ 𝒪 X ] K) ≤[ poset-of (𝒪 X) ] (K ∨[ 𝒪 X ] ℬ [ l ])) holds
       ※ = 𝟏[ 𝒪 X ] ∧[ 𝒪 X ] K   ≤⟨ ∧[ 𝒪 X ]-lower₂ (𝟏[ 𝒪 X ]) K ⟩
           K                     ≤⟨ ∨[ 𝒪 X ]-upper₁ K (ℬ [ l ])  ⟩
           K ∨[ 𝒪 X ] ℬ [ l ]    ■

       Ⅰ = heyting-implication₁ K (K ∨[ 𝒪 X ] (ℬ [ l ])) 𝟏[ 𝒪 X ] ※
       Ⅱ = ⋁[ 𝒪 X ]-upper _ (inl ⋆ ∷ inr ⋆ ∷ [])

   † : ‘ K ’ ∧[ 𝒪 Patchₛ-X ] ¬‘ (K , κ) ’ ＝ 𝟎[ 𝒪 Patchₛ-X ]
   † = only-𝟎-is-below-𝟎 (𝒪 Patchₛ-X) _ †₁

   ‡ : ‘ K ’ ∨[ 𝒪 Patchₛ-X ] ¬‘ (K , κ) ’ ＝ 𝟏[ 𝒪 Patchₛ-X ]
   ‡ = only-𝟏-is-above-𝟏 (𝒪 Patchₛ-X) _ ‡₁

 closed-complements-open : (K : ⟨ 𝒪 X ⟩)
                         → (κ : is-compact-open X K holds)
                         → is-boolean-complement-of (𝒪 Patchₛ-X) ‘ K ’ ¬‘ (K , κ) ’ holds
 closed-complements-open K κ =
  complementation-is-symmetric (𝒪 Patchₛ-X) ¬‘ (K , κ) ’ ‘ K ’ ※
   where
    ※ = open-complements-closed K κ

\end{code}

I define below an alternative version of the module above due to a technical
problem. Consider a spectral locale `A` with a proof `σ` of spectrality. When
the module above is called with the data contained in `σ` (let's call this
`σᴰ`), Agda does not recognise the fact that `σ = ∣ σᴰ ∣`. To circumvent this
problem, I'm defining a version of this module that takes as argument the proof
of spectrality instead of the structure contained within.

\begin{code}

-- module PatchComplementationAlternative (X : Locale (𝓤 ⁺) 𝓤 𝓤)
--                                        (σ : is-spectral (𝒪 X) holds) where

--  open PatchConstruction X σ renaming (Patch to Patch-X)
--  open ClosedNucleus     X σ
--  open OpenNucleus       X σ

--  X-has-basis : has-basis (𝒪 X) holds
--  X-has-basis = spectral-frames-have-bases (𝒪 X) σ

--  open HeytingImplicationConstruction X X-has-basis

--  𝟎-is-id : (U : ⟨ 𝒪 X ⟩) → 𝟎[ 𝒪 Patch-X ] $ U ＝ U
--  𝟎-is-id U = ≤-is-antisymmetric (poset-of (𝒪 X)) † (‡ U)
--   where
--    † : ((𝟎[ 𝒪 Patch-X ] $ U) ≤[ poset-of (𝒪 X) ] U) holds
--    † = 𝟎-is-bottom (𝒪 Patch-X) idₙ U

--    ‡ : (idₙ ≤[ poset-of (𝒪 Patch-X) ] 𝟎[ 𝒪 Patch-X ]) holds
--    ‡ U = U ≤⟨ ※ ⟩ (⋁[ 𝒪 Patch-X ] ∅ 𝓤) $ U ＝⟨ refl ⟩ₚ 𝟎[ 𝒪 Patch-X ] $ U ■
--     where
--      open PosetReasoning (poset-of (𝒪 X))

--      ※ : (U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 Patch-X ] ∅ 𝓤) $ U) holds
--      ※ = ⋁[ 𝒪 X ]-upper ⁅ α U ∣ α ε 𝔡𝔦𝔯 (∅ 𝓤) ⁆ []

--  open-complements-closed : (K : ⟨ 𝒪 X ⟩)
--                          → (κ : is-compact-open (𝒪 X) K holds)
--                          → (is-boolean-complement-of (𝒪 Patch-X) ¬‘ (K , κ) ’ ‘ K ’ ) holds
--  open-complements-closed K κ = † , ‡
--   where
--    ※ : (U : ⟨ 𝒪 X ⟩) → (K ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] (K ==> U) ＝ 𝟎[ 𝒪 Patch-X ] $ U
--    ※ U = (K ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] (K ==> U)  ＝⟨ Ⅰ            ⟩
--          (U ∨[ 𝒪 X ] K) ∧[ 𝒪 X ] (K ==> U)  ＝⟨ Ⅱ            ⟩
--          U                                  ＝⟨ 𝟎-is-id U ⁻¹ ⟩
--          𝟎[ 𝒪 Patch-X ] $ U                 ∎
--           where
--            Ⅰ = ap (λ - → - ∧[ 𝒪 X ] (K ==> U)) (∨[ 𝒪 X ]-is-commutative K U)
--            Ⅱ = H₈ U K ⁻¹

--    † : ‘ K ’ ∧[ 𝒪 Patch-X ] ¬‘ (K , κ) ’ ＝ 𝟎[ 𝒪 Patch-X ]
--    † = perfect-nuclei-eq
--         (‘ K ’ ∧[ 𝒪 Patch-X ] ¬‘ K , κ ’)
--         𝟎[ 𝒪 Patch-X ]
--         (dfunext fe ※)

--    ϟ : (𝟏[ 𝒪 Patch-X ] ≤[ poset-of (𝒪 Patch-X) ] (‘ K ’ ∨[ 𝒪 Patch-X ] ¬‘ (K , κ) ’)) holds
--    ϟ U =
--     𝟏[ 𝒪 X ]                                ≤⟨ Ⅰ ⟩
--     K ==> (K ∨[ 𝒪 X ] U)                    ≤⟨ Ⅱ ⟩
--     (‘ K ’ ∨[ 𝒪 Patch-X ] ¬‘ (K , κ) ’) $ U ■
--      where
--       open PosetReasoning (poset-of (𝒪 X))

--       ϡ : ((𝟏[ 𝒪 X ] ∧[ 𝒪 X ] K) ≤[ poset-of (𝒪 X) ] (K ∨[ 𝒪 X ] U)) holds
--       ϡ = 𝟏[ 𝒪 X ] ∧[ 𝒪 X ] K   ≤⟨ ∧[ 𝒪 X ]-lower₂ 𝟏[ 𝒪 X ] K ⟩
--           K                     ≤⟨ ∨[ 𝒪 X ]-upper₁ K U        ⟩
--           K ∨[ 𝒪 X ] U          ■

--       Ⅰ = heyting-implication₁ K (K ∨[ 𝒪 X ] U) 𝟏[ 𝒪 X ] ϡ
--       Ⅱ = ⋁[ 𝒪 X ]-upper _ (inl ⋆ ∷ inr ⋆ ∷ [])

--    ‡ : ‘ K ’ ∨[ 𝒪 Patch-X ] ¬‘ (K , κ) ’ ＝ 𝟏[ 𝒪 Patch-X ]
--    ‡ = only-𝟏-is-above-𝟏
--         (𝒪 Patch-X)
--         (‘ K ’ ∨[ 𝒪 Patch-X ] ¬‘ (K , κ) ’)
--         ϟ

\end{code}

\section{Basis of Patch}

\begin{code}

module BasisOfPatch (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ X) where

 σ : is-spectral X holds
 σ = spectralᴰ-gives-spectrality X σᴰ

 ℬ↑ : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬ↑ = basisₛ X σᴰ

 d : directed-basisᴰ (𝒪 X)
 d = ℬ↑ , basisₛ-is-directed-basis X σᴰ

 β : has-basis (𝒪 X) holds
 β = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 κ : consists-of-compact-opens X ℬ↑ holds
 κ = basisₛ-consists-of-compact-opens X σᴰ

 sk : 𝒦 X is 𝓤 small
 sk = 𝒦-is-small X d κ (local-smallness X)

 open PatchConstruction X σ
  using (_≼_; _⋏_; nucleus-of; _$_; ⋁ₙ)
  renaming (Patch to Patch-X; Perfect-Nucleus to Perfect-Nucleus-on-X)
 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open HeytingImplicationConstruction X ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣
 open ClosedNucleus X σ
 open OpenNucleus X σᴰ sk

\end{code}

For convenience, we define the following auxiliary notation for the open nucleus:

\begin{code}

 𝔠 : index ℬ → ⟨ 𝒪 Patchₛ-X ⟩
 𝔠 i = ‘ ℬ [ i ] ’

 𝔬 : index ℬ → ⟨ 𝒪 Patchₛ-X ⟩
 𝔬 i = ¬‘ ℬ [ i ] , pr₁ (pr₂ (pr₂ σᴰ)) i ’

 𝕜 : (i : index ℬ) → is-compact-open X (ℬ [ i ]) holds
 𝕜 = pr₁ (pr₂ (pr₂ σᴰ))

\end{code}

We define the following basis for Patch:

\begin{code}

 ℬ-patch : Fam 𝓤 ⟨ 𝒪 Patchₛ-X ⟩
 ℬ-patch = ⁅ 𝔠 k ⋏ 𝔬 l ∣ (k , l) ∶ (index ℬ × index ℬ) ⁆

 ℬ-patch-consists-of-clopens : consists-of-clopens (𝒪 Patch-X) ℬ-patch holds
 ℬ-patch-consists-of-clopens (k , l) = (𝔬 k ∨[ 𝒪 Patch-X ] 𝔠 l) , ※
  where
   open PatchComplementation X σᴰ

   † : is-boolean-complement-of (𝒪 Patch-X) (𝔠 k) (𝔬 k) holds
   † = closed-complements-open (ℬ [ k ]) (𝕜 k)

   ‡ : is-boolean-complement-of (𝒪 Patch-X) (𝔬 l) (𝔠 l) holds
   ‡ = open-complements-closed (ℬ [ l ]) (𝕜 l)

   ※ : is-boolean-complement-of
        (𝒪 Patch-X)
        (𝔬 k ∨[ 𝒪 Patch-X ] 𝔠 l)
        (𝔠 k ∧[ 𝒪 Patch-X ] 𝔬 l) holds
   ※ = ∧-complement (𝒪 Patch-X) † ‡

 ℬ-patchₛ-consists-of-clopens : consists-of-clopens (𝒪 Patchₛ-X) ℬ-patch holds
 ℬ-patchₛ-consists-of-clopens (k , l) = (𝔬 k ∨[ 𝒪 Patchₛ-X ] 𝔠 l) , ※
  where
   open PatchComplementation X σᴰ

   abstract
    † : is-boolean-complement-of (𝒪 Patchₛ-X) (𝔠 k) (𝔬 k) holds
    † = closed-complements-open (ℬ [ k ]) (𝕜 k)

    ‡ : is-boolean-complement-of (𝒪 Patchₛ-X) (𝔬 l) (𝔠 l) holds
    ‡ = open-complements-closed (ℬ [ l ]) (𝕜 l)

    ※ : is-boolean-complement-of
         (𝒪 Patchₛ-X)
         (𝔬 k ∨[ 𝒪 Patchₛ-X ] 𝔠 l)
         (𝔠 k ∧[ 𝒪 Patch-X ] 𝔬 l)
        holds
    ※ = ∧-complement (𝒪 Patchₛ-X) † ‡

 ℬ-patch-↑ : Fam 𝓤 ⟨ 𝒪 Patchₛ-X ⟩
 ℬ-patch-↑ = directify (𝒪 Patchₛ-X) ℬ-patch

{--

 ℬ-patch-↑-consists-of-clopens : consists-of-clopens (𝒪 Patchₛ-X) ℬ-patch-↑ holds
 ℬ-patch-↑-consists-of-clopens = {! directification-preserves-clopenness (𝒪 Patchₛ-X) ? ? !}
  -- directification-preserves-clopenness
  --  (𝒪 Patch-X)
  --  ℬ-patch ℬ-patch-consists-of-clopens

--}

\end{code}

Given a perfect nucleus `j : 𝓞(X) → 𝓞(X)`, the basic covering family for it
is given by the restriction of the family, given by the function `𝕔𝕠𝕧`

\begin{code}

 basic-below : Perfect-Nucleus-on-X → 𝓤  ̇
 basic-below 𝒿@(j , _) =
  Σ (k , l) ꞉ (index ℬ × index ℬ) , ((ℬ [ k ]) ≤[ poset-of (𝒪 X) ] j (ℬ [ l ])) holds

 proj : (𝒿 : Perfect-Nucleus-on-X) → basic-below 𝒿 → index ℬ × index ℬ
 proj 𝒿 ((k , l) , _)= k , l

 𝕔𝕠𝕧₁ : Perfect-Nucleus-on-X → Fam 𝓤 ⟨ 𝒪 Patchₛ-X ⟩
 𝕔𝕠𝕧₁ 𝒿@(j , _) = ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-X ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆

 𝕜′ : Perfect-Nucleus-on-X → index ℬ → ⟨ 𝒪 Patchₛ-X ⟩
 𝕜′ (j , _) l = ‘ j (ℬ [ l ]) ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 l

 𝕔𝕠𝕧₂ : Perfect-Nucleus-on-X → Fam 𝓤 ⟨ 𝒪 Patchₛ-X ⟩
 𝕔𝕠𝕧₂ 𝒿 = ⁅ 𝕜′ 𝒿 i ∣ i ∶ index ℬ ⁆

\end{code}

\begin{code}

 𝕜ⱼi-is-below-j : (𝒿 : Perfect-Nucleus-on-X) (i : index ℬ) → (𝕜′ 𝒿 i ≼ᵏ 𝒿) holds
 𝕜ⱼi-is-below-j 𝒿@(j , _) i l =
  𝕜′ 𝒿 i $ (ℬ [ l ])                                         ＝⟨ refl ⟩ₚ
  (j ℬᵢ ∨[ 𝒪 X ] ℬₗ) ∧[ 𝒪 X ] (ℬᵢ ==> ℬₗ)                    ≤⟨ ᚠ ⟩
  (j ℬᵢ ∨[ 𝒪 X ] ℬₗ) ∧[ 𝒪 X ] (j ℬᵢ ==> j ℬₗ)                ≤⟨ ᚣ ⟩
  (j ℬᵢ ∨[ 𝒪 X ] ℬₗ) ∧[ 𝒪 X ] ((j ℬᵢ ∨[ 𝒪 X ] ℬₗ) ==> j ℬₗ)  ≤⟨ ᚬ ⟩
  j (ℬ [ l ])                                                ■
   where
    open PosetReasoning (poset-of (𝒪 X))
    ℬᵢ = ℬ [ i ]
    ℬₗ = ℬ [ l ]

    Ⅰ = binary-distributivity (𝒪 X) (j ℬᵢ ==> j ℬₗ) (j ℬᵢ) ℬₗ
    Ⅱ = ∨[ 𝒪 X ]-left-monotone (mp-right (j ℬᵢ) (j ℬₗ))
    Ⅲ = ∨[ 𝒪 X ]-right-monotone (∧[ 𝒪 X ]-lower₂ (j ℬᵢ ==> j ℬₗ) ℬₗ)
    Ⅳ = ∨[ 𝒪 X ]-least (≤-is-reflexive (poset-of (𝒪 X)) (j ℬₗ)) (𝓃₁ (𝒪 X) (nucleus-of 𝒿) ℬₗ)

    ♣ : ((j ℬᵢ ==> j ℬₗ ∧[ 𝒪 X ] (j ℬᵢ ∨[ 𝒪 X ] ℬₗ)) ≤[ poset-of (𝒪 X) ] j ℬₗ) holds
    ♣ = j ℬᵢ ==> j ℬₗ ∧[ 𝒪 X ] (j ℬᵢ ∨[ 𝒪 X ] ℬₗ)                             ＝⟨ Ⅰ ⟩ₚ
        ((j ℬᵢ ==> j ℬₗ) ∧[ 𝒪 X ] j ℬᵢ) ∨[ 𝒪 X ] (j ℬᵢ ==> j ℬₗ) ∧[ 𝒪 X ] ℬₗ  ≤⟨ Ⅱ ⟩
        j ℬₗ ∨[ 𝒪 X ] (j ℬᵢ ==> j ℬₗ) ∧[ 𝒪 X ] ℬₗ                             ≤⟨ Ⅲ ⟩
        j ℬₗ ∨[ 𝒪 X ] ℬₗ                                                      ≤⟨ Ⅳ ⟩
        j ℬₗ                                                                  ■


    ♠ : ((j ℬᵢ ==> j ℬₗ) ≤[ poset-of (𝒪 X) ] ((j ℬᵢ ∨[ 𝒪 X ] ℬₗ) ==> j ℬₗ)) holds
    ♠ = heyting-implication₁ _ (j ℬₗ) (j ℬᵢ ==> j ℬₗ) ♣

    ᚠ = ∧[ 𝒪 X ]-right-monotone (nuclei-preserve-==> ℬᵢ ℬₗ (nucleus-of 𝒿))
    ᚣ = ∧[ 𝒪 X ]-right-monotone ♠
    ᚬ = mp-left (j ℬᵢ ∨[ 𝒪 X ] ℬₗ) (j ℬₗ)

\end{code}

This lemma can be strengthened to an equality in the case where `𝕜ⱼ(i)` is being
applied to `ℬⱼ`.

\begin{code}

 𝕜-𝒿-eq : (𝒿 : Perfect-Nucleus-on-X) (i : index ℬ) → 𝕜′ 𝒿 i $ (ℬ [ i ]) ＝ 𝒿 $ (ℬ [ i ])
 𝕜-𝒿-eq 𝒿@(j , _) i = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   ℬᵢ = ℬ [ i ]

   † : (((𝕜′ 𝒿 i) $ (ℬ [ i ])) ≤[ poset-of (𝒪 X) ] (𝒿 $ (ℬ [ i ]))) holds
   † = 𝕜ⱼi-is-below-j 𝒿 i i

   Ⅰ = ∨[ 𝒪 X ]-upper₁ (j (ℬ [ i ])) (ℬ [ i ])
   Ⅱ = 𝟏-right-unit-of-∧ (𝒪 X) (j (ℬ [ i ]) ∨[ 𝒪 X ] ℬ [ i ]) ⁻¹
   Ⅲ = ap
       (λ - → (j (ℬ [ i ]) ∨[ 𝒪 X ] ℬ [ i ]) ∧[ 𝒪 X ] -)
       (heyting-implication-identity (ℬ [ i ]) ⁻¹)

   ‡ : ((𝒿 $ (ℬ [ i ])) ≤[ poset-of (𝒪 X) ] (𝕜′ 𝒿 i $ (ℬ [ i ]))) holds
   ‡ = 𝒿 $ (ℬ [ i ])                                                     ≤⟨ Ⅰ ⟩
       j (ℬ [ i ]) ∨[ 𝒪 X ] ℬ [ i ]                                      ＝⟨ Ⅱ ⟩ₚ
       (j (ℬ [ i ]) ∨[ 𝒪 X ] ℬ [ i ]) ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                  ＝⟨ Ⅲ ⟩ₚ
       (j (ℬ [ i ]) ∨[ 𝒪 X ] ℬ [ i ]) ∧[ 𝒪 X ] ((ℬ [ i ]) ==> (ℬ [ i ])) ＝⟨ refl ⟩ₚ
       𝕜′ 𝒿 i $ (ℬ [ i ])                                                 ■

\end{code}

The first lemma we prove is the fact that `𝒿 = 𝕔𝕠𝕧₂ 𝒿` which we call
*Johnstone's lemma*.

\begin{code}

 lemma-johnstone : (𝒿 : Perfect-Nucleus-on-X) → 𝒿 ＝ ⋁[ 𝒪 Patchₛ-X ] 𝕔𝕠𝕧₂ 𝒿
 lemma-johnstone 𝒿@(j , _) = ⋁[ 𝒪 Patchₛ-X ]-unique (𝕔𝕠𝕧₂ 𝒿) 𝒿 († , ‡)
  where
   open Joins (λ 𝒿 𝓀 → 𝒿 ≤[ poset-of (𝒪 Patchₛ-X) ] 𝓀)
   open PosetReasoning (poset-of (𝒪 X))

   † : (𝒿 is-an-upper-bound-of 𝕔𝕠𝕧₂ 𝒿) holds
   † = 𝕜ⱼi-is-below-j 𝒿

   ‡ : ((𝓀 , _) : upper-bound (𝕔𝕠𝕧₂ 𝒿)) → (𝒿 ≼ᵏ 𝓀) holds
   ‡ (𝓀 , υ) l = j (ℬ [ l ])        ＝⟨ 𝕜-𝒿-eq 𝒿 l ⁻¹ ⟩ₚ
                 𝕜′ 𝒿 l $ (ℬ [ l ]) ≤⟨ υ l l ⟩
                 𝓀 $ (ℬ [ l ])      ■

\end{code}

\begin{code}

 open Epsilon X σᴰ

 ‘’-is-monotone : (U V : ⟨ 𝒪 X ⟩)
                → (U ≤[ poset-of (𝒪 X) ] V) holds
                → (‘ U ’ ≤[ poset-of (𝒪 Patch-X) ] ‘ V ’) holds
 ‘’-is-monotone U V p W = ∨[ 𝒪 X ]-least † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (U ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
   † = U ≤⟨ p ⟩ V ≤⟨ ∨[ 𝒪 X ]-upper₁ V W ⟩ V ∨[ 𝒪 X ] W ■

   ‡ : (W ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
   ‡ = ∨[ 𝒪 X ]-upper₂ V W

 𝕔𝕠𝕧₁=𝕔𝕠𝕧₂ : (𝒿 : Perfect-Nucleus-on-X) → ⋁ₙ (𝕔𝕠𝕧₁ 𝒿) ＝ ⋁ₙ (𝕔𝕠𝕧₂ 𝒿)
 𝕔𝕠𝕧₁=𝕔𝕠𝕧₂ 𝒿@(j , _) = ≤-is-antisymmetric (poset-of (𝒪 Patch-X)) † ‡
  where

   β′ : cofinal-in (𝒪 Patch-X) (𝕔𝕠𝕧₁ 𝒿) (𝕔𝕠𝕧₂ 𝒿) holds
   β′ ((k , l) , p) = ∣ l , ※ ∣
    where
     open PosetReasoning (poset-of (𝒪 Patch-X))

     ♠ : ((𝔠 k ∧[ 𝒪 Patch-X ] 𝔬 l)
          ≤[ poset-of (𝒪 Patch-X) ]
          (‘ j (ℬ [ l ]) ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 l)) holds
     ♠ = ∧[ 𝒪 Patch-X ]-left-monotone (‘’-is-monotone (ℬ [ k ]) (j (ℬ [ l ])) p)

     ※ : ((𝕔𝕠𝕧₁ 𝒿 [ (k , l) , p ]) ≤[ poset-of (𝒪 Patch-X) ] ((𝕔𝕠𝕧₂ 𝒿) [ l ])) holds
     ※ = 𝕔𝕠𝕧₁ 𝒿 [ (k , l) , p ]                ＝⟨ refl ⟩ₚ
         𝔠 k ∧[ 𝒪 Patch-X ] 𝔬 l                ≤⟨ ♠ ⟩
         ‘ j (ℬ [ l ]) ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 l   ＝⟨ refl ⟩ₚ
         𝕔𝕠𝕧₂ 𝒿 [ l ]                          ■

   † : (⋁ₙ (𝕔𝕠𝕧₁ 𝒿) ≼ ⋁ₙ (𝕔𝕠𝕧₂ 𝒿)) holds
   † = cofinal-implies-join-covered (𝒪 Patch-X) (𝕔𝕠𝕧₁ 𝒿) (𝕔𝕠𝕧₂ 𝒿) β′

   ‡ : (⋁ₙ (𝕔𝕠𝕧₂ 𝒿) ≤[ poset-of (𝒪 Patch-X) ] (⋁ₙ (𝕔𝕠𝕧₁ 𝒿))) holds
   ‡ = ⋁[ 𝒪 Patch-X ]-least (𝕔𝕠𝕧₂ 𝒿) (⋁ₙ (𝕔𝕠𝕧₁ 𝒿) , ※)
    where
     open Joins (λ x y → x ≤[ poset-of (𝒪 Patch-X) ] y)
     open PosetReasoning (poset-of (𝒪 X))


     ※ : (⋁ₙ (𝕔𝕠𝕧₁ 𝒿) is-an-upper-bound-of (𝕔𝕠𝕧₂ 𝒿)) holds
     ※ i U =
      (𝕔𝕠𝕧₂ 𝒿 [ i ]) $ U                                                  ＝⟨ refl ⟩ₚ
      𝕜′ 𝒿 i $ U                                                          ＝⟨ refl ⟩ₚ
      (‘ j (ℬ [ i ]) ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i) $ U                           ＝⟨ Ⅰ    ⟩ₚ
      (‘ ⋁[ 𝒪 X ] ⁅ ℬ [ l ] ∣ l ε ℒ ⁆ ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i) $ U          ＝⟨ Ⅱ    ⟩ₚ
      ((⋁[ 𝒪 Patchₛ-X ] ⁅ ‘ ℬ [ l ] ’ ∣ l ε ℒ ⁆) ∧[ 𝒪 Patchₛ-X ] 𝔬 i) $ U ＝⟨ Ⅲ    ⟩ₚ
      ((⋁[ 𝒪 Patchₛ-X ] ⁅ ‘ ℬ [ l ] ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i ∣ l ε ℒ ⁆) $ U) ≤⟨ ♥     ⟩
      ⋁ₙ (𝕔𝕠𝕧₁ 𝒿) $ U                                                     ■
       where
        ℒ : Fam 𝓤 (index ℬ)
        ℒ = cover-indexₛ X σᴰ (𝒿 $ (ℬ [ i ]))

        p : j (ℬ [ i ]) ＝ ⋁[ 𝒪 X ] ⁅ ℬ [ l ] ∣ l ε ℒ ⁆
        p = (⋁[ 𝒪 X ]-unique ⁅ ℬ [ l ] ∣ l ε ℒ ⁆
               (j (ℬ [ i ]))
               (basisₛ-covers-do-cover X σᴰ (j (ℬ [ i ]))))

        Ⅰ = ap (λ - → (‘ - ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i) $ U) p
        Ⅱ = ap
             (λ - → (- ∧[ 𝒪 Patchₛ-X ] 𝔬 i) $ U)
             (⋁[ 𝒪 Patchₛ-X ]-unique
               ⁅ ‘ ℬ [ l ] ’ ∣ l ε ℒ ⁆
               _
               (ϵ-preserves-⋁ ⁅ ℬ [ l ] ∣ l ε ℒ ⁆))
        Ⅲ = ap (λ - → - $ U) (distributivity′-right _ _ _)

        ♣ : (l : index ℒ)
          → ((‘ ℬ [ ℒ [ l ] ] ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i) ≤[ poset-of (𝒪 Patchₛ-X) ] (⋁[ 𝒪 Patchₛ-X ] 𝕔𝕠𝕧₁ 𝒿)) holds
        ♣ l = ⋁[ 𝒪 Patchₛ-X ]-upper (𝕔𝕠𝕧₁ 𝒿) ((ℒ [ l ] , i) , γ)
         where
          γ : ((ℬ [ ℒ [ l ] ]) ≤[ poset-of (𝒪 X) ] j (ℬ [ i ])) holds
          γ = ℬ [ ℒ [ l ] ]                  ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ ℬ [ l ] ∣ l ε ℒ ⁆ l ⟩
              ⋁[ 𝒪 X ] ⁅ ℬ [ l ] ∣ l ε ℒ ⁆   ＝⟨ p ⁻¹ ⟩ₚ
              j (ℬ [ i ])                    ■

        ♠ = ⋁[ 𝒪 Patchₛ-X ]-least
             ⁅ ‘ ℬ [ l ] ’ ∧[ 𝒪 Patchₛ-X ] 𝔬 i ∣ l ε ℒ ⁆
             ((⋁[ 𝒪 Patchₛ-X ] 𝕔𝕠𝕧₁ 𝒿) , ♣)

        ♥ = ≼ᵏ-implies-≼ _ _ ♠ U

\end{code}

We first prove that this forms a basis.

\begin{code}

 main-covering-lemma : (𝒿 : Perfect-Nucleus-on-X) → 𝒿 ＝ ⋁[ 𝒪 Patch-X ] (𝕔𝕠𝕧₁ 𝒿)
 main-covering-lemma 𝒿 =
  𝒿                          ＝⟨ lemma-johnstone 𝒿 ⟩
  ⋁[ 𝒪 Patch-X ] (𝕔𝕠𝕧₂ 𝒿)    ＝⟨ (𝕔𝕠𝕧₁=𝕔𝕠𝕧₂ 𝒿) ⁻¹  ⟩
  ⋁[ 𝒪 Patch-X ] (𝕔𝕠𝕧₁ 𝒿)    ∎

 ℬ-is-basis-for-patch : is-basis-for (𝒪 Patch-X) ℬ-patch
 ℬ-is-basis-for-patch 𝒿 = (basic-below 𝒿 , proj 𝒿) , ※
  where
   open Joins _≼_

   ※ : (𝒿 is-lub-of (𝕔𝕠𝕧₁ 𝒿)) holds
   ※ = transport
        (λ - → (- is-lub-of (𝕔𝕠𝕧₁ 𝒿)) holds)
        (main-covering-lemma 𝒿 ⁻¹)
        ((⋁[ 𝒪 Patch-X ]-upper (𝕔𝕠𝕧₁ 𝒿) , ⋁[ 𝒪 Patch-X ]-least (𝕔𝕠𝕧₁ 𝒿)))

 ℬ-is-basis-for-patchₛ : is-basis-for (𝒪 Patchₛ-X) ℬ-patch
 ℬ-is-basis-for-patchₛ 𝒿 = (basic-below 𝒿 , proj 𝒿) , ※
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 Patchₛ-X) ] y)

   ※ : (𝒿 is-lub-of 𝕔𝕠𝕧₁ 𝒿) holds
   ※ = transport
        (λ - → (- is-lub-of (𝕔𝕠𝕧₁ 𝒿)) holds)
        (main-covering-lemma 𝒿 ⁻¹)
        (⋁[ 𝒪 Patchₛ-X ]-upper (𝕔𝕠𝕧₁ 𝒿) , ⋁[ 𝒪 Patchₛ-X ]-least (𝕔𝕠𝕧₁ 𝒿))

\end{code}

\begin{code}

module PatchStoneᴰ (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ X) where

 private
  σ : is-spectral X holds
  σ = spectralᴰ-gives-spectrality X σᴰ

 ℬ↑ : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬ↑ = basisₛ X σᴰ

 d : directed-basisᴰ (𝒪 X)
 d = ℬ↑ , basisₛ-is-directed-basis X σᴰ

 β : has-basis (𝒪 X) holds
 β = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 κ : consists-of-compact-opens X ℬ↑ holds
 κ = basisₛ-consists-of-compact-opens X σᴰ

 sk : 𝒦 X is 𝓤 small
 sk = 𝒦-is-small X d κ (local-smallness X)

 open ClosedNucleus X σ
 open OpenNucleus   X σᴰ
 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open PatchConstruction X σ using (_≼_; ⋁ₙ) renaming (Patch to Patch-X)
 open Epsilon X σᴰ

 open PerfectMaps Patchₛ-X X 𝒷

 X-is-compact : is-compact X holds
 X-is-compact = spectral-implies-compact X σ

\end{code}

\begin{code}

 patchₛ-is-compact : is-compact Patchₛ-X holds
 patchₛ-is-compact = compact-codomain-of-perfect-map-implies-compact-domain
                      ϵ
                      ϵ-is-a-perfect-map
                      X-is-compact

 patch-is-compact : is-compact Patch-X holds
 patch-is-compact S δ p = ∥∥-rec ∃-is-prop γ (patchₛ-is-compact S ζ †)
  where
   γ : (Σ i ꞉ index S , (𝟏[ 𝒪 Patchₛ-X ] ≼ᵏ (S [ i ])) holds)
     → ∃ i ꞉ index S , (𝟏[ 𝒪 Patch-X ] ≼ (S [ i ])) holds
   γ (i , q) = ∣ i , ≼ᵏ-implies-≼ 𝟏[ 𝒪 Patch-X ] (S [ i ]) q ∣

   ζ : is-directed (𝒪 Patchₛ-X) S holds
   ζ = pr₁ δ , †
    where
     † : (i j : index S) → (Ǝ k ꞉ index S , (((S [ i ]) ≼ᵏ (S [ k ]))
                                           ∧ ((S [ j ]) ≼ᵏ (S [ k ]))) holds) holds
     † i j = ∥∥-rec ∃-is-prop ‡ (pr₂ δ i j)
      where
       ‡ : _
       ‡ (k , φ , ψ) = ∣ k
                       , ≼-implies-≼ᵏ (S [ i ]) (S [ k ]) φ
                       , ≼-implies-≼ᵏ (S [ j ]) (S [ k ]) ψ ∣

   † : (𝟏[ 𝒪 Patch-X ] ≼ᵏ ⋁ₙ S) holds
   † = ≼-implies-≼ᵏ 𝟏[ 𝒪 Patch-X ] (⋁ₙ S) p

\end{code}

\begin{code}

 open BasisOfPatch X σᴰ

 ℬ-patch-β↑ : directed-basis-forᴰ (𝒪 Patch-X) ℬ-patch-↑
 ℬ-patch-β↑ U = pr₁ Σ-assoc (β↑ U , δ)
  where
   β↑ : is-basis-for (𝒪 Patch-X) (directify (𝒪 Patch-X) ℬ-patch)
   β↑ = directified-basis-is-basis (𝒪 Patch-X) ℬ-patch ℬ-is-basis-for-patch

   δ : is-directed (𝒪 Patch-X) ⁅ ℬ-patch-↑ [ j ] ∣ j ε pr₁ (β↑ U) ⁆ holds
   δ = covers-of-directified-basis-are-directed
        (𝒪 Patch-X)
        ℬ-patch
        ℬ-is-basis-for-patch
        U

 ℬ-patchₛ-β↑ : directed-basis-forᴰ (𝒪 Patchₛ-X) ℬ-patch-↑
 ℬ-patchₛ-β↑ U = pr₁ Σ-assoc (β↑ U , δ)
  where
   β↑ : is-basis-for (𝒪 Patchₛ-X) (directify (𝒪 Patchₛ-X) ℬ-patch)
   β↑ = directified-basis-is-basis (𝒪 Patchₛ-X) ℬ-patch ℬ-is-basis-for-patchₛ

   δ : is-directed (𝒪 Patchₛ-X) ⁅ ℬ-patch-↑ [ j ] ∣ j ε pr₁ (β↑ U) ⁆ holds
   δ = covers-of-directified-basis-are-directed
        (𝒪 Patchₛ-X)
        ℬ-patch
        ℬ-is-basis-for-patchₛ
        U

 patch-zero-dimensionalᴰ : zero-dimensionalᴰ (𝒪 Patch-X)
 patch-zero-dimensionalᴰ = ℬ-patch-↑ , ℬ-patch-β↑ , †
  where
   †  : consists-of-clopens (𝒪 Patch-X) ℬ-patch-↑ holds
   † []       = 𝟎-is-clopen (𝒪 Patch-X)
   † (i ∷ is) = clopens-are-closed-under-∨ (𝒪 Patch-X) (ℬ-patch [ i ]) (ℬ-patch-↑ [ is ]) (ℬ-patch-consists-of-clopens i) († is)

 patch-zero-dimensional : is-zero-dimensional (𝒪 Patch-X) holds
 patch-zero-dimensional = ∣ patch-zero-dimensionalᴰ ∣

 ℬ-patch-↑-is-directed-basisₛ : is-directed-basis (𝒪 Patchₛ-X) ℬ-patch-↑
 ℬ-patch-↑-is-directed-basisₛ =
  β′ , covers-of-directified-basis-are-directed (𝒪 Patchₛ-X) ℬ-patch ℬ-is-basis-for-patchₛ
   where
    β′ : is-basis-for (𝒪 Patchₛ-X) ℬ-patch-↑
    β′ = directified-basis-is-basis (𝒪 Patchₛ-X) ℬ-patch ℬ-is-basis-for-patchₛ

 patchₛ-zero-dimensionalᴰ : zero-dimensionalᴰ (𝒪 Patchₛ-X)
 patchₛ-zero-dimensionalᴰ = ℬ-patch-↑ , ℬ-patchₛ-β↑ , γ
  where
   β′ : is-basis-for (𝒪 Patchₛ-X) ℬ-patch-↑
   β′ = directified-basis-is-basis (𝒪 Patchₛ-X) ℬ-patch ℬ-is-basis-for-patchₛ

   γ : consists-of-clopens (𝒪 Patchₛ-X) ℬ-patch-↑ holds
   γ []       = 𝟎-is-clopen (𝒪 Patchₛ-X)
   γ (i ∷ is) = clopens-are-closed-under-∨
                 (𝒪 Patchₛ-X)
                 (ℬ-patch [ i ])
                 (ℬ-patch-↑ [ is ])
                 (ℬ-patchₛ-consists-of-clopens i)
                 (γ is)

 patchₛ-is-stone : is-stone Patchₛ-X holds
 patchₛ-is-stone =
  stoneᴰ-implies-stone Patchₛ-X (patchₛ-is-compact , patchₛ-zero-dimensionalᴰ)

 patchₛ-spectralᴰ : spectralᴰ Patchₛ-X
 patchₛ-spectralᴰ = stoneᴰ-implies-spectralᴰ
                     Patchₛ-X
                     (patchₛ-is-compact , patchₛ-zero-dimensionalᴰ)

 patchₛ-is-spectral : is-spectral Patchₛ-X holds
 patchₛ-is-spectral =
  spectralᴰ-gives-spectrality Patchₛ-X patchₛ-spectralᴰ

\end{code}

\begin{code}


{--

module PatchStone (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral X holds) where

 open PatchConstruction X σ renaming (Patch to Patch-X)

 patch-is-stone : is-stone Patch-X holds
 patch-is-stone = ∥∥-rec (holds-is-prop (is-stone (𝒪 Patch-X))) γ σ
  where
   γ : spectralᴰ X → is-stone Patch-X holds
   γ σᴰ = let
           open PatchStoneᴰ X σᴰ
          in
           patch-is-compact , patch-zero-dimensional

 patch-is-spectral : is-spectral (𝒪 Patch-X) holds
 patch-is-spectral = stone-locales-are-spectral (𝒪 Patch-X) patch-is-stone

--}


\end{code}

\begin{code}

module OpenMeetClosedLemmata (X  : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ X) (sk : 𝒦 X is 𝓤 small) where

 private
  σ : is-spectral X holds
  σ = spectralᴰ-gives-spectrality X σᴰ

  β : has-basis (𝒪 X) holds
  β = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 open ClosedNucleus X σ
 open OpenNucleus   X σᴰ sk
 open SmallPatchConstruction X σᴰ using    (𝟎-is-id)
                                  renaming (SmallPatch to Patchₛ-X)
 open PatchConstruction X σ
 open HeytingImplicationConstruction X β

 closed-meet-open-𝟎-lemma : (C D : ⟨ 𝒪 X ⟩)
                          → (κ : is-compact-open X D holds)
                          → (‘ C ’ ∧[ 𝒪 Patchₛ-X ] ¬‘ (D , κ) ’) ＝ 𝟎[ 𝒪 Patchₛ-X ]
                          → (C ≤[ poset-of (𝒪 X) ] D) holds
 closed-meet-open-𝟎-lemma C D κ p = connecting-lemma₃ (𝒪 X) (‡ ⁻¹)
  where
   † : (C ∨[ 𝒪 X ] D) ∧[ 𝒪 X ] (D ==> D) ＝ 𝟎[ 𝒪 Patchₛ-X ] $ D
   † =
    perfect-nuclei-eq-inverse
     (‘ C ’ ∧[ 𝒪 Patchₛ-X ] ¬‘ D , κ ’)
     𝟎[ 𝒪 Patchₛ-X ]
     p
     D

   ‡ : C ∨[ 𝒪 X ] D ＝ D
   ‡ = C ∨[ 𝒪 X ] D                               ＝⟨ Ⅰ ⟩
       (C ∨[ 𝒪 X ] D) ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]           ＝⟨ Ⅱ ⟩
       (C ∨[ 𝒪 X ] D) ∧[ 𝒪 X ] (D ==> D)          ＝⟨ Ⅲ ⟩
       𝟎[ 𝒪 Patchₛ-X ] $ D                        ＝⟨ Ⅳ ⟩
       D                                          ∎
        where
         Ⅰ = 𝟏-right-unit-of-∧ (𝒪 X) (C ∨[ 𝒪 X ] D) ⁻¹
         Ⅱ = ap
              (λ - → (C ∨[ 𝒪 X ] D) ∧[ 𝒪 X ] -)
              (heyting-implication-identity D ⁻¹)
         Ⅲ = †
         Ⅳ = 𝟎-is-id D

module AdditionalLemmata (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 ∨-distributivity-over-⋁ : (S T : Fam 𝓤 ⟨ 𝒪 X ⟩)
                         → ∥ index S ∥
                         → ∥ index T ∥
                         → (⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (⋁[ 𝒪 X ] T)
                         ＝ ⋁[ 𝒪 X ] ⁅ (S [ i ]) ∨[ 𝒪 X ] (T [ j ])
                                      ∣ (i , j) ∶ (index S × index T) ⁆
 ∨-distributivity-over-⋁ S T ∣i∣ ∣j∣ = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
   open PosetReasoning (poset-of (𝒪 X))

   𝓁𝒽𝓈 = (⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (⋁[ 𝒪 X ] T)
   𝓇𝒽𝓈 = ⋁[ 𝒪 X ] ⁅ (S [ i ]) ∨[ 𝒪 X ] (T [ j ]) ∣ (i , j) ∶ (index S × index T) ⁆

   † : (𝓁𝒽𝓈 ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
   † = ∨[ 𝒪 X ]-least †₁ †₂
    where
     ♣₁ : index T → ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
     ♣₁ j = ⋁[ 𝒪 X ]-least S (𝓇𝒽𝓈 , ※)
      where
       ※ : (𝓇𝒽𝓈 is-an-upper-bound-of S) holds
       ※ i =
        S [ i ]                         ≤⟨ ∨[ 𝒪 X ]-upper₁ (S [ i ]) (T [ j ]) ⟩
        (S [ i ]) ∨[ 𝒪 X ] (T [ j ])    ≤⟨ ⋁[ 𝒪 X ]-upper _ (i , j)            ⟩
        𝓇𝒽𝓈                             ■

     †₁ : ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
     †₁ = ∥∥-rec (holds-is-prop ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈)) ♣₁ ∣j∣

     ♣₂ : index S → ((⋁[ 𝒪 X ] T) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
     ♣₂ i = ⋁[ 𝒪 X ]-least T (𝓇𝒽𝓈 , ※)
      where
       ※ : (𝓇𝒽𝓈 is-an-upper-bound-of T) holds
       ※ j =
        T [ j ]                        ≤⟨ ∨[ 𝒪 X ]-upper₂ (S [ i ]) (T [ j ]) ⟩
        (S [ i ]) ∨[ 𝒪 X ] (T [ j ])   ≤⟨ ⋁[ 𝒪 X ]-upper _ (i , j)            ⟩
        𝓇𝒽𝓈 ■

     †₂ : ((⋁[ 𝒪 X ] T) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈) holds
     †₂ = ∥∥-rec (holds-is-prop ((⋁[ 𝒪 X ] T) ≤[ poset-of (𝒪 X) ] 𝓇𝒽𝓈)) ♣₂ ∣i∣

   ‡ : (𝓇𝒽𝓈 ≤[ poset-of (𝒪 X) ] 𝓁𝒽𝓈) holds
   ‡ = ⋁[ 𝒪 X ]-least
        ⁅ (S [ i ]) ∨[ 𝒪 X ] (T [ j ]) ∣ (i , j) ∶ (index S × index T) ⁆
        (𝓁𝒽𝓈 , ※)
        where
         ※ : (𝓁𝒽𝓈
               is-an-upper-bound-of
              ⁅ (S [ i ]) ∨[ 𝒪 X ] (T [ j ]) ∣ (i , j) ∶ (index S × index T) ⁆)
             holds
         ※ (i , j) = (S [ i ])    ∨[ 𝒪 X ] (T [ j ])     ≤⟨ Ⅰ ⟩
                     (⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (T [ j ])     ≤⟨ Ⅱ ⟩
                     (⋁[ 𝒪 X ] S) ∨[ 𝒪 X ] (⋁[ 𝒪 X ] T)  ■
                      where
                       Ⅰ = ∨[ 𝒪 X ]-left-monotone (⋁[ 𝒪 X ]-upper S i)
                       Ⅱ = ∨[ 𝒪 X ]-right-monotone (⋁[ 𝒪 X ]-upper T j)

module BasicComplements (X : Locale 𝓤 𝓥 𝓦) (𝕜 : is-compact X holds) (zᴰ : zero-dimensionalᴰ (𝒪 X)) where

 private
  ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
  ℬ = pr₁ zᴰ

 𝕣 : is-regular (𝒪 X) holds
 𝕣 = zero-dimensional-locales-are-regular (𝒪 X) ∣ zᴰ ∣

 ¬ₓ_ : Σ c ꞉ ⟨ 𝒪 X ⟩ , is-compact-open X c holds → ⟨ 𝒪 X ⟩
 ¬ₓ_ (c , κ) = pr₁ (compacts-are-clopen-in-regular-frames X 𝕣 c κ)

 ¬ₓ-gives-complement : (c : ⟨ 𝒪 X ⟩)
                     → (κ : is-compact-open X c holds)
                     → is-boolean-complement-of (𝒪 X) (¬ₓ (c , κ)) c holds
 ¬ₓ-gives-complement c κ = pr₂ (compacts-are-clopen-in-regular-frames X 𝕣 c κ)

module SomeOtherLemmata
        (A   X               : Locale (𝓤 ⁺) 𝓤 𝓤)
        (σᴰ                  : spectralᴰ A)
        (𝕜                   : is-compact X holds)
        (𝕫ᴰ                  : zero-dimensionalᴰ (𝒪 X))
        (𝒻                   : X ─c→ A)
        (f-is-a-spectral-map : is-spectral-map A X 𝒻 holds)
         where

 open BasicComplements X 𝕜 𝕫ᴰ
 open ContinuousMapNotation X A

 ℬA : Fam 𝓤 ⟨ 𝒪 A ⟩
 ℬA = basisₛ A σᴰ

 ℬX : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬX = pr₁ 𝕫ᴰ

 ¬𝒻 : index ℬA → ⟨ 𝒪 X ⟩
 ¬𝒻 i = ¬ₓ (𝒻 ⋆∙ (ℬA [ i ]) , κ)
         where
          κ : is-compact-open X (𝒻 ⋆∙ (ℬA [ i ])) holds
          κ = f-is-a-spectral-map (ℬA [ i ]) (pr₁ (pr₂ (pr₂ σᴰ)) i)


 -- ¬𝒻-lemma : (i : index ℬA) (ℬᵢ′ : ⟨ 𝒪 A ⟩)
 --         → is-complement-of (𝒪 A) ℬᵢ′ (ℬA [ i ])
 --         → ¬𝒻 i ＝ 𝒻 ⋆∙ ℬᵢ′
 -- ¬𝒻-lemma i ℬᵢ′ (p , q) =
 --  complements-are-unique (𝒪 X) (𝒻 ⋆∙ (ℬA [ i ])) (¬𝒻 i) (𝒻 ⋆∙ ℬᵢ′) † ‡
 --   where
 --   † : is-complement-of (𝒪 X) (¬𝒻 i) (𝒻 ⋆∙ (ℬA [ i ]))
 --   † = ¬ₓ-gives-complement (𝒻 ⋆∙ (ℬA [ i ])) {!!}

 --   ‡₁ : ℬᵢ′ ∧[ 𝒪 A ] (ℬA [ i ]) ＝ 𝟎[ 𝒪 A ]
 --   ‡₁ = ℬᵢ′     ∧[ 𝒪 A ] (ℬA [ i ]) ＝⟨ ∧[ 𝒪 A ]-is-commutative ℬᵢ′ (ℬA [ i ]) ⟩
 --         ℬA [ i ] ∧[ 𝒪 A ] ℬᵢ′      ＝⟨ p                                     ⟩
 --         𝟎[ 𝒪 A ]                   ∎

 --   ‡₂ : ℬᵢ′ ∨[ 𝒪 A ] (ℬA [ i ]) ＝ 𝟏[ 𝒪 A ]
 --   ‡₂ = ℬᵢ′ ∨[ 𝒪 A ] (ℬA [ i ])     ＝⟨ ∨[ 𝒪 A ]-is-commutative ℬᵢ′ (ℬA [ i ]) ⟩
 --         (ℬA [ i ]) ∨[ 𝒪 A ] ℬᵢ′    ＝⟨ q ⟩
 --         𝟏[ 𝒪 A ]                   ∎

 --   ‡ : is-complement-of (𝒪 X) (𝒻 ⋆∙ ℬᵢ′) (𝒻 ⋆∙ (ℬA [ i ]))
 --   ‡ = frame-homomorphisms-preserve-complements (𝒪 A) (𝒪 X) 𝒻 (‡₁ , ‡₂)

 -- ¬𝒻-antitone : (i j : index ℬA)
 --             → ((ℬA [ i ]) ≤[ poset-of (𝒪 A) ] (ℬA [ j ])) holds
 --             → (¬𝒻 j ≤[ poset-of (𝒪 X) ] ¬𝒻 i) holds
 -- ¬𝒻-antitone i j p = {!!}
 --  where
 --   open PosetReasoning (poset-of (𝒪 X))

 --   ♣ : ((¬𝒻 j ∧[ 𝒪 X ] 𝒻 ⋆∙ (ℬA [ j ])) ≤[ poset-of (𝒪 X) ] 𝟎[ 𝒪 X ]) holds
 --   ♣ = ¬𝒻 j ∧[ 𝒪 X ] 𝒻 ⋆∙ (ℬA [ j ])                   ≤⟨ {!!} ⟩
 --       𝒻 ⋆∙ (¬ₓ (ℬA [ i ])) ∧[ 𝒪 X ] 𝒻 ⋆∙ (ℬA [ j ])   ≤⟨ {!!} ⟩
 --       𝟎[ 𝒪 X ]                                        ■

-- module Hauptsatz (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral (𝒪 X) holds) where

--  open PatchConstruction X σ

--  hauptsatz₁ : (U : ⟨ 𝒪 X ⟩) (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
--             → is-nucleus (𝒪 X) j holds
--             → is-nucleus (𝒪 X) k holds
--             → cofinal-in
--                (𝒪 X)
--                ⁅ α U     ∣ α ε 𝔡𝔦𝔯 (binary-family 𝓤 j k) ⁆
--                ⁅ α (j U) ∣ α ε 𝔡𝔦𝔯 (binary-family 𝓤 j k) ⁆
--               holds
--  hauptsatz₁ U j k φ ψ is = ∣ is , † ∣
--   where
--    S : Fam 𝓤 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
--    S = ⁅ j , k ⁆

--    both-j-and-k-are-prenuclei : (b : (𝟙 + 𝟙))
--                               → is-prenucleus (𝒪 X) (⁅ j , k ⁆ [ b ]) holds
--    both-j-and-k-are-prenuclei (inl ⋆) = pr₂ (nucleus-pre (𝒪 X) (j , φ))
--    both-j-and-k-are-prenuclei (inr ⋆) = pr₂ (nucleus-pre (𝒪 X) (k , ψ))

--    † : ((𝔡𝔦𝔯 (binary-family 𝓤 j k) [ is ]) U
--          ≤[ poset-of (𝒪 X) ]
--         (𝔡𝔦𝔯 (binary-family 𝓤 j k) [ is ]) (j U)) holds
--    † = prenuclei-are-monotone
--         (𝒪 X)
--         ( 𝔡𝔦𝔯 (binary-family 𝓤 j k) [ is ]
--         , 𝔡𝔦𝔯-prenuclei (binary-family 𝓤 j k) both-j-and-k-are-prenuclei is)
--         (U , j U)
--         (𝓃₁ (𝒪 X) (j , φ) U)

--  hauptsatz₂ : (U : ⟨ 𝒪 X ⟩) (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
--             → is-nucleus (𝒪 X) j holds
--             → cofinal-in
--                (𝒪 X)
--                ⁅ α (j U) ∣ α ε 𝔡𝔦𝔯 (binary-family 𝓤 j k) ⁆
--                ⁅ α U     ∣ α ε 𝔡𝔦𝔯 (binary-family 𝓤 j k) ⁆
--               holds
--  hauptsatz₂ U j k φ is = ∣ (inl ⋆ ∷ is) , † ∣
--   where
--    † : ((𝔡𝔦𝔯 (binary-family 𝓤 j k) [ is ]) (j U)
--          ≤[ poset-of (𝒪 X) ]
--         ((𝔡𝔦𝔯 (binary-family 𝓤 j k) [ inl ⋆ ∷ is ]) U)) holds
--    † = ≤-is-reflexive (poset-of (𝒪 X)) ((𝔡𝔦𝔯 (binary-family 𝓤 j k) [ is ]) (j U))

--  lemma₁ : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
--         → is-prenucleus (𝒪 X) j holds
--         → is-prenucleus (𝒪 X) k holds
--         → (j ≼₀ (j ∘ k)) holds
--  lemma₁ j k (jn₁ , jn₂) (kn₁ , kn₂) x =
--   prenuclei-are-monotone (𝒪 X) (j , jn₁ , jn₂) (x , k x) (kn₁ x)

--  lemma₂ : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
--         → is-prenucleus (𝒪 X) j holds
--         → is-prenucleus (𝒪 X) k holds
--         → (k ≼₀ (j ∘ k)) holds
--  lemma₂ j k (jn₁ , jn₂) (kn₁ , kn₂) x = jn₁ (k x)

\end{code}

The following lemma was proved by Igor Arrieta for the purpose of solving the
binary join preservation problem that arose when proving the universal property
of Patch.

\begin{code}

module IgorsLemma (X Y : Locale (𝓤 ⁺) 𝓤 𝓤) (𝒷 : has-basis (𝒪 Y) holds) where

 open ContinuousMapNotation X Y
 open HeytingImplicationConstruction Y 𝒷

 igors-lemma-⇒ : (f : X ─c→ Y) (U V : ⟨ 𝒪 Y ⟩) (W : ⟨ 𝒪 X ⟩)
               → ((f ⋆∙ U) ≤[ poset-of (𝒪 X) ] (W ∨[ 𝒪 X ] (f ⋆∙ V))) holds
               → (T : ⟨ 𝒪 Y ⟩)
               → ((f ⋆∙ (U ∨[ 𝒪 Y ] T) ∧[ 𝒪 X ] (f ⋆∙ (V ==> T)))
                  ≤[ poset-of (𝒪 X) ]
                  (W ∨[ 𝒪 X ] f ⋆∙ T))
                 holds
 igors-lemma-⇒ f U V W p T =
  f ⋆∙ (U ∨[ 𝒪 Y ] T) ∧[ 𝒪 X ] f ⋆∙ (V ==> T)                                        ＝⟨ Ⅰ ⟩ₚ
  (f ⋆∙ U ∨[ 𝒪 X ] f ⋆∙ T) ∧[ 𝒪 X ] f ⋆∙ (V ==> T)                                   ≤⟨ Ⅱ  ⟩
  ((W ∨[ 𝒪 X ] (f ⋆∙ V)) ∨[ 𝒪 X ] f ⋆∙ T) ∧[ 𝒪 X ] f ⋆∙ (V ==> T)                    ＝⟨ Ⅲ ⟩ₚ
  (W ∨[ 𝒪 X ] ((f ⋆∙ V) ∨[ 𝒪 X ] f ⋆∙ T)) ∧[ 𝒪 X ] f ⋆∙ (V ==> T)                    ＝⟨ Ⅳ ⟩ₚ
  (W ∨[ 𝒪 X ] (f ⋆∙ (V ∨[ 𝒪 Y ] T))) ∧[ 𝒪 X ] f ⋆∙ (V ==> T)                         ＝⟨ Ⅴ ⟩ₚ
  f ⋆∙ (V ==> T) ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] (f ⋆∙ (V ∨[ 𝒪 Y ] T)))                         ＝⟨ Ⅵ ⟩ₚ
  ((f ⋆∙ (V ==> T)) ∧[ 𝒪 X ] W) ∨[ 𝒪 X ] (f ⋆∙ (V ==> T) ∧[ 𝒪 X ] f ⋆∙ (V ∨[ 𝒪 Y ] T)) ≤⟨ Ⅷ ⟩
  W ∨[ 𝒪 X ] (f ⋆∙ (V ==> T) ∧[ 𝒪 X ] f ⋆∙ (V ∨[ 𝒪 Y ] T))                           ＝⟨ Ⅸ ⟩ₚ
  W ∨[ 𝒪 X ] (f ⋆∙ ((V ==> T) ∧[ 𝒪 Y ] (V ∨[ 𝒪 Y ] T)))                              ＝⟨ ♣ ⟩ₚ
  W ∨[ 𝒪 X ] (f ⋆∙ T)                                                                ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    Ⅰ = ap
         (λ - → - ∧[ 𝒪 X ] f ⋆∙ (V ==> T))
         (frame-homomorphisms-preserve-binary-joins (𝒪 Y) (𝒪 X) f U T)
    Ⅱ = ∧[ 𝒪 X ]-left-monotone (∨[ 𝒪 X ]-left-monotone p)
    Ⅲ = ap
         (λ - → - ∧[ 𝒪 X ] f ⋆∙ (V ==> T))
         (∨[ 𝒪 X ]-assoc W (f ⋆∙ V) (f ⋆∙ T))
    Ⅳ = ap
         (λ - → (W ∨[ 𝒪 X ] -) ∧[ 𝒪 X ] (f ⋆∙ (V ==> T)))
         (frame-homomorphisms-preserve-binary-joins (𝒪 Y) (𝒪 X) f V T ⁻¹)

    Ⅴ = ∧[ 𝒪 X ]-is-commutative
         (W ∨[ 𝒪 X ] (f ⋆∙ (V ∨[ 𝒪 Y ] T)))
         (f ⋆∙ (V ==> T))

    Ⅵ = binary-distributivity (𝒪 X) (f ⋆∙ (V ==> T)) W (f ⋆∙ (V ∨[ 𝒪 Y ] T))

    Ⅷ = ∨[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₂ (f ⋆∙ (V ==> T)) W)

    Ⅸ = ap
         (λ - → W ∨[ 𝒪 X ] -)
         (frame-homomorphisms-preserve-meets (𝒪 Y) (𝒪 X) f (V ==> T) (V ∨[ 𝒪 Y ] T) ⁻¹)

    ♣₀ = f ⋆∙ ((V ==> T) ∧[ 𝒪 Y ] (V ∨[ 𝒪 Y ] T))  ＝⟨ ap (λ - → f ⋆∙ ((V ==> T) ∧[ 𝒪 Y ] -)) (∨[ 𝒪 Y ]-is-commutative V T) ⟩
         f ⋆∙ ((V ==> T) ∧[ 𝒪 Y ] (T ∨[ 𝒪 Y ] V))  ＝⟨ ap (f ⋆∙_) (∧[ 𝒪 Y ]-is-commutative (V ==> T) (T ∨[ 𝒪 Y ] V)) ⟩
         f ⋆∙ ((T ∨[ 𝒪 Y ] V) ∧[ 𝒪 Y ]  (V ==> T)) ＝⟨ ap (f ⋆∙_) (H₈ T V ⁻¹) ⟩
         (f ⋆∙ T) ∎

    ♣ = ap (λ - → W ∨[ 𝒪 X ] -) ♣₀

 igors-lemma-⇐ : (f : X ─c→ Y) (U V : ⟨ 𝒪 Y ⟩) (W : ⟨ 𝒪 X ⟩)
               → ((T : ⟨ 𝒪 Y ⟩)
                  → ((f ⋆∙ (U ∨[ 𝒪 Y ] T) ∧[ 𝒪 X ] (f ⋆∙ (V ==> T)))
                      ≤[ poset-of (𝒪 X) ]
                     (W ∨[ 𝒪 X ] f ⋆∙ T)) holds)
               → ((f ⋆∙ U) ≤[ poset-of (𝒪 X) ] (W ∨[ 𝒪 X ] (f ⋆∙ V))) holds
 igors-lemma-⇐ f U V W φ =
  f ⋆∙ U                           ≤⟨ I  ⟩
  W ∨[ 𝒪 X ] f ⋆∙ (U ∧[ 𝒪 Y ] V)   ≤⟨ II ⟩
  W ∨[ 𝒪 X ] f ⋆∙ V                ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    ♣ : ((f ⋆∙ (U ∨[ 𝒪 Y ] (V ∧[ 𝒪 Y ] U)) ∧[ 𝒪 X ] f ⋆∙ (V ==> (V ∧[ 𝒪 Y ] U)))
            ≤[ poset-of (𝒪 X) ]
           (W ∨[ 𝒪 X ] f ⋆∙ (V ∧[ 𝒪 Y ] U))) holds
    ♣ = φ (V ∧[ 𝒪 Y ] U)

    II : ((W ∨[ 𝒪 X ] (f ⋆∙ (U ∧[ 𝒪 Y ] V)))
           ≤[ poset-of (𝒪 X) ]
          (W ∨[ 𝒪 X ] f ⋆∙ V)) holds
    II = ∨[ 𝒪 X ]-right-monotone
          (frame-morphisms-are-monotonic
            (𝒪 Y)
            (𝒪 X)
            (f .pr₁)
            (f .pr₂)
            (_ , _)
            (∧[ 𝒪 Y ]-lower₂ U V))

    I : ((f ⋆∙ U) ≤[ poset-of (𝒪 X) ] (W ∨[ 𝒪 X ] f ⋆∙ (U ∧[ 𝒪 Y ] V))) holds
    I =
     f ⋆∙ U                                                                  ≤⟨ 𝕒 ⟩
     f ⋆∙ (U ∧[ 𝒪 Y ] (V ==> U))                                             ＝⟨ 𝕓 ⟩ₚ
     (f ⋆∙ U) ∧[ 𝒪 X ] (f ⋆∙ (V ==> U))                                      ＝⟨ 𝕔 ⟩ₚ
     (f ⋆∙ U) ∧[ 𝒪 X ] (f ⋆∙ (V ==> (V ∧[ 𝒪 Y ] U)))                         ≤⟨ 𝕕 ⟩
     f ⋆∙ (U ∨[ 𝒪 Y ] (V ∧[ 𝒪 Y ] U)) ∧[ 𝒪 X ] f ⋆∙ (V ==> (V ∧[ 𝒪 Y ] U))   ≤⟨ 𝕖 ⟩
     W ∨[ 𝒪 X ] f ⋆∙ (V ∧[ 𝒪 Y ] U)                                          ＝⟨ 𝕗 ⟩ₚ
     W ∨[ 𝒪 X ] f ⋆∙ (U ∧[ 𝒪 Y ] V)                                          ■
      where
       𝕒 = frame-morphisms-are-monotonic
            (𝒪 Y)
            (𝒪 X)
            (f .pr₁)
            (f .pr₂)
            (_ , _)
            (∧[ 𝒪 Y ]-greatest _ _ _
              (≤-is-reflexive (poset-of (𝒪 Y)) U) (weakening V U))
       𝕓 = frame-homomorphisms-preserve-meets (𝒪 Y) (𝒪 X) f U (V ==> U)
       𝕔 = ap (λ - → f ⋆∙ U ∧[ 𝒪 X ] (f ⋆∙ -)) (heyting-implication-law₄ V U)
       𝕕 = ∧[ 𝒪 X ]-left-monotone
            (frame-morphisms-are-monotonic
              (𝒪 Y)
              (𝒪 X)
              (f .pr₁)
              (f .pr₂)
              (_ , _)
              (∨[ 𝒪 Y ]-upper₁ U (V ∧[ 𝒪 Y ] U)))
       𝕖 = ♣
       𝕗 = ap (λ - → W ∨[ 𝒪 X ] (f ⋆∙ -)) (∧[ 𝒪 Y ]-is-commutative V U)

\end{code}
