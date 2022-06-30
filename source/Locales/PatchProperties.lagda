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

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.Nucleus pt fe
open import Locales.CompactRegular pt fe
open import Locales.PatchLocale pt fe
open import Locales.HeytingImplication pt fe

open Locale

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

module PatchStone (X : Locale 𝓤 𝓥 𝓦) where

 patch-is-stone : {!!}
 patch-is-stone = {!!}

\end{code}
