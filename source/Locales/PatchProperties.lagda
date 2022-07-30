Ayberk Tosun, 23 April 2022 (date started)

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])

\end{code}

\begin{code}[hide]

module Locales.PatchProperties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import UF.Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.AdjointFunctorTheoremForFrames pt fe

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.Nucleus pt fe
open import Locales.CompactRegular pt fe
open import Locales.PatchLocale pt fe
open import Locales.HeytingImplication pt fe

open Locale

\end{code}

\section{Basic properties}

\begin{code}

module BasicProperties (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral (𝒪 X) holds) where

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X;
                                      Patch to Patch-of-X)

\end{code}

We first prove the following lemma about directed families of nuclei, which
amounts the fact that the directification of an already directed family is
cofinal in the original family.

\begin{code}

 directedness-lemma : (K : Fam 𝓦 Perfect-Nucleus-on-X)
                    → is-directed (poset-of (𝒪 Patch-of-X)) K holds
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
             (K₀ [ l ]) ((K₀ [ l ]) U)         ≡⟨ ♢ ⟩ₚ
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
                                       → is-directed (poset-of (𝒪 Patch-of-X)) K holds
                                       → (U : ⟨ 𝒪 X ⟩)
                                       → (⋁[ 𝒪 Patch-of-X ] K) $ U ≡ ⋁[ 𝒪 X ] ⁅ k $ U ∣ k ε K ⁆
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

module ClosedNucleus (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral (𝒪 X) holds) where

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)

 ‘_’ : ⟨ 𝒪 X ⟩ → Perfect-Nucleus-on-X
 ‘ U ’ = binary-join (𝒪 X) U , ∨-is-nucleus (𝒪 X) U , ∨-is-scott-continuous (𝒪 X) U

\end{code}

\begin{code}

module OpenNucleus (X : Locale 𝓤 𝓥 𝓥) (σ : is-spectral (𝒪 X) holds) where

 open PatchConstruction X σ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)

 X-has-small-basis : has-basis (𝒪 X) holds
 X-has-small-basis = spectral-frames-have-bases (𝒪 X) σ

 𝒦 : 𝓤 ⊔ 𝓥 ⁺ ̇
 𝒦 = Σ K ꞉ ⟨ 𝒪 X ⟩ , is-compact-open (𝒪 X) K holds

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
   γ = (U ==> (U ==> V)) ∧[ 𝒪 X ] U                ≡⟨ i    ⟩ₚ
       (U ==> (U ==> V)) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U)   ≡⟨ ii   ⟩ₚ
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
         δ = ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] U               ≡⟨ i   ⟩ₚ
             ((U ==> V) ∧[ 𝒪 X ] (U ==> W)) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U)  ≡⟨ ii  ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] ((U ==> W) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] U))  ≡⟨ iii ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] (((U ==> W) ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] U)  ≤⟨ iv  ⟩
             (U ==> V) ∧[ 𝒪 X ] (W ∧[ 𝒪 X ] U)                       ≡⟨ v   ⟩ₚ
             (U ==> V) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] W)                       ≡⟨ vi  ⟩ₚ
             ((U ==> V) ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] W                       ≤⟨ vii ⟩
             V ∧[ 𝒪 X ] W ■

 opn-perfect : ((K , _) : 𝒦) → is-perfect (opn K) holds
 opn-perfect (K , κ) =
  characterisation-of-continuity (𝒪 X) (𝒪 X) σ (opn K) (opn-monotone K) γ
   where
    open PosetReasoning (poset-of (𝒪 X))

    γ : continuity-condition (𝒪 X) (𝒪 X) (opn K) holds
    γ K₂ U κ₂ p = ∣ (K ∧[ 𝒪 X ] K₂) , κ′ , ♠ , ♥ ∣
     where
      κ′ : is-compact-open (𝒪 X) (K ∧[ 𝒪 X ] K₂) holds
      κ′ = compacts-closed-under-∧-in-spectral-frames (𝒪 X) σ K K₂ κ κ₂

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

 ¬‘_’ : 𝒦 → Perfect-Nucleus-on-X
 ¬‘ (K , κ) ’ = K ==>_ , opn-is-nucleus K , opn-perfect (K , κ)

\end{code}

\begin{code}

 opn-reverses-binary-joins : (U V : ⟨ 𝒪 X ⟩) → opn (U ∨[ 𝒪 X ] V) ≡ opn U ⋏₀ opn V
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
      T ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)                                              ≡⟨ i   ⟩ₚ
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


\end{code}

\begin{code}

module Epsilon (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ (𝒪 X)) where

 open PatchConstruction X ∣ σᴰ ∣ renaming (Perfect-Nucleus to Perfect-Nucleus-on-X)
 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open ClosedNucleus X ∣ σᴰ ∣

 ϵ-preserves-𝟏 : ‘ 𝟏[ 𝒪 X ] ’ ≡ 𝟏[ 𝒪 Patchₛ-X ]
 ϵ-preserves-𝟏 = perfect-nuclei-eq ‘ 𝟏[ 𝒪 X ] ’ 𝟏[ 𝒪 Patchₛ-X ] (dfunext fe †)
  where
   † : (U : ⟨ 𝒪 X ⟩) → 𝟏[ 𝒪 X ] ∨[ 𝒪 X ] U ≡ 𝟏[ 𝒪 X ]
   † U = 𝟏-left-annihilator-for-∨ (𝒪 X) U

 ϵ : Patchₛ-X ─c→ X
 ϵ = ‘_’ , ϵ-preserves-𝟏 , β , γ
  where
   β : preserves-binary-meets (𝒪 X) (𝒪 Patchₛ-X) ‘_’ holds
   β U V = perfect-nuclei-eq
            ‘ U ∧[ 𝒪 X ] V ’
            (‘ U ’ ∧[ 𝒪 Patchₛ-X ] ‘ V ’)
            (dfunext fe †)
    where
     † : (W : ⟨ 𝒪 X ⟩) → ‘ U ∧[ 𝒪 X ] V ’ $ W ≡ (‘ U ’ ∧[ 𝒪 Patchₛ-X ] ‘ V ’) $ W
     † W = (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] W                ≡⟨ i   ⟩
           W ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] V)                ≡⟨ ii  ⟩
           (W ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] V)   ≡⟨ iii ⟩
           (U ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] (W ∨[ 𝒪 X ] V)   ≡⟨ iv  ⟩
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

   γ : (Ɐ S ∶ Fam 𝓤 ⟨ 𝒪 X ⟩ , ‘ ⋁[ 𝒪 X ] S ’ is-lub-of ⁅ ‘ U ’ ∣ U ε S ⁆) holds
   γ S = † , ‡
    where
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

     ‡ : (Ɐ (𝒿 , _) ∶ upper-bound ⁅ ‘ U ’ ∣ U ε S ⁆ ,
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

 𝒷 : has-basis (𝒪 X) holds
 𝒷 = spectral-frames-have-bases (𝒪 X) ∣ σᴰ ∣

 open PerfectMaps Patchₛ-X X
 open AdjointFunctorTheorem Patchₛ-X X 𝒷
 open BasicProperties X ∣ σᴰ ∣
 open PatchConstruction X ∣ σᴰ ∣ using () renaming (Patch to Patch-of-X)

\end{code}

The right adjoint `ϵ⁎` of `ϵ` is the function applying a given perfect nucleus
to the bottom element `𝟎` of the locale in consideration.

\begin{code}

 ϵ⁎-is-application-to-𝟎 : (𝒦 : Fam 𝓦 ⟨ 𝒪 X ⟩)
                        → {!!}
 ϵ⁎-is-application-to-𝟎 = {!!}

\end{code}

\begin{code}

 ϵ-is-a-perfect-map : is-perfect-map 𝒷 ϵ holds
 ϵ-is-a-perfect-map 𝒦 δ = {!!}
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

   δ′ : is-directed (poset-of (𝒪 Patch-of-X)) 𝒦 holds
   δ′ = pr₁ δ , ζ
    where
     ζ : (Ɐ i ∶ index 𝒦 , Ɐ j ∶ index 𝒦 ,
           Ǝ k ∶ index 𝒦 , (((𝒦 [ i ]) ≼ (𝒦 [ k ])) holds)
                         × (((𝒦 [ j ]) ≼ (𝒦 [ k ])) holds)) holds
     ζ i j = ∥∥-rec ∃-is-prop η (pr₂ δ i j)
      where
       η : _
       η (k , φ , ψ) =
                     ∣ k
                     , ≼ᵏ-implies-≼ (𝒦 [ i ]) (𝒦 [ k ]) φ
                     , ≼ᵏ-implies-≼ (𝒦 [ j ]) (𝒦 [ k ]) ψ
                     ∣

   † : ((ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦)) is-an-upper-bound-of ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆) holds
   † i = pr₂ (right-adjoint-of ϵ) _ (⋁[ 𝒪 Patchₛ-X ]-upper 𝒦 i)

   ‡ : ((𝓊 , _) : upper-bound ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆)
     → ((ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦)) ≤[ poset-of (𝒪 X) ] 𝓊) holds
   ‡ (𝓊 , φ) = {!!}

   γ : ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦) ≡ ⋁[ 𝒪 X ] ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆
   γ = ϵ ⁎· (⋁[ 𝒪 Patchₛ-X ] 𝒦)          ≡⟨ i   ⟩
       (⋁[ 𝒪 Patchₛ-X ] 𝒦) $ 𝟎[ 𝒪 X ]    ≡⟨ ii  ⟩
       ⋁[ 𝒪 X ] ⁅ k $ 𝟎[ 𝒪 X ] ∣ k ε 𝒦 ⁆ ≡⟨ iii ⟩
       ⋁[ 𝒪 X ] ⁅ ϵ ⁎· k ∣ k ε 𝒦 ⁆       ∎
         where
          i   = {!!}
          ii  = directed-joins-are-computed-pointwise 𝒦 δ′ 𝟎[ 𝒪 X ]
          iii = {!!}
\end{code}

\begin{code}

module PatchStone (X : Locale (𝓤 ⁺) 𝓤 𝓤) (σᴰ : spectralᴰ (𝒪 X)) where

 open ClosedNucleus X ∣ σᴰ ∣
 open OpenNucleus   X ∣ σᴰ ∣
 open SmallPatchConstruction X σᴰ renaming (SmallPatch to Patchₛ-X)
 open Epsilon X σᴰ

 open PerfectMaps Patchₛ-X X 𝒷

 X-is-compact : is-compact (𝒪 X) holds
 X-is-compact = spectral-implies-compact (𝒪 X) ∣ σᴰ ∣

\end{code}

\begin{code}

 patch-is-compact : is-compact (𝒪 Patchₛ-X) holds
 patch-is-compact =
  perfect-map-implies-compactness ϵ {!!} X-is-compact

\end{code}
