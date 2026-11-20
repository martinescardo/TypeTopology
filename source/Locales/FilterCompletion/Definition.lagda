---
title:        The localic filter completion
author:       Ayberk Tosun
date-started: 2026-10-28
---

This module contains a definition of the frame of downward-closed subsets of a
poset. We refer to the locale this defines as the _localic filter completion_.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size hiding (is-locally-small)
open import UF.Subsingletons

module Locales.FilterCompletion.Definition
        (𝓤  : Universe)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext) where

open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.DownSet pt fe
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Slice.Family
open import UF.Logic
open import UF.Powerset
open import UF.SubtypeClassifier

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

We work in a module parameterized by a poset `P`.

\begin{code}

module Downward-Closed-Subset-Frame (P : Poset 𝓤 𝓤) where

 open PropositionalSubsetInclusionNotation fe

 private
  _≤_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓤
  _≤_ = λ x y → x ≤[ P ] y

\end{code}

Given a downward-closed subset `𝔘`, we define the notation `x ε 𝔘` for `𝔘`'s
underlying subset.

\begin{code}

 underlying-subset-syntax : Downward-Closed-Subsetₚ P → 𝓟 {𝓤} ∣ P ∣ₚ
 underlying-subset-syntax (U , _) = U

 syntax underlying-subset-syntax 𝔘 x = x ε 𝔘
 infix 8 underlying-subset-syntax

 underlying-subset-is-downward-closed : (U : Downward-Closed-Subsetₚ P)
                                      → is-downward-closed _≤_ (λ - → - ε U) holds
 underlying-subset-is-downward-closed (_ , φ) = φ

\end{code}

This forms a frame when ordered under inclusion. We make use of the powerset
frame from `Locales.DiscreteLocale.Definition` when carrying out this
construction.

\begin{code}

 _⊑_ : Downward-Closed-Subsetₚ P → Downward-Closed-Subsetₚ P → Ω 𝓤
 (U , _) ⊑ (V , _) = U ⊆ₚ V

 infix 30 _⊑_

 powerset-frame : Frame (𝓤 ⁺) 𝓤 𝓤
 powerset-frame =
  DefnOfDiscreteLocale.frame-of-subsets ∣ P ∣ₚ carrier-of-[ P ]-is-set

 powerset-poset : Poset (𝓤 ⁺) 𝓤
 powerset-poset = poset-of powerset-frame

 ⊑-is-reflexive : is-reflexive _⊑_ holds
 ⊑-is-reflexive (U , _) = ≤-is-reflexive powerset-poset U

 ⊑-is-transitive : is-transitive _⊑_ holds
 ⊑-is-transitive (U , _) (V , _) (W , _) = ≤-is-transitive powerset-poset U V W

 ⊑-is-antisymmetric : is-antisymmetric _⊑_
 ⊑-is-antisymmetric β γ =
  to-subtype-＝
   (holds-is-prop ∘ is-downward-closed _≤_)
   (≤-is-antisymmetric powerset-poset β γ)

 ⊑-is-partial-order : is-partial-order (Downward-Closed-Subsetₚ P) _⊑_
 ⊑-is-partial-order = (⊑-is-reflexive , ⊑-is-transitive)
                    , ⊑-is-antisymmetric

 top↓ : Downward-Closed-Subsetₚ P
 top↓ = full , †
  where
   † : is-downward-closed _≤_ full holds
   † _ ⋆ _ _ = ⋆

 top↓-is-top : (U : Downward-Closed-Subsetₚ P) → (U ⊑ top↓) holds
 top↓-is-top _ _ _ = ⋆

 _⊓↓_ : Downward-Closed-Subsetₚ P
      → Downward-Closed-Subsetₚ P
      → Downward-Closed-Subsetₚ P
 (U , φ) ⊓↓ (V , ψ) = U ∩ V , †
  where
   † : is-downward-closed _≤_ (U ∩ V) holds
   † x (β , γ) y p = φ x β y p , ψ x γ y p

 infixl 35 _⊓↓_

 open Meets _⊑_

 ⊓↓-gives-glb : (U V : Downward-Closed-Subsetₚ P)
              → ((U ⊓↓ V) is-glb-of (U , V)) holds
 ⊓↓-gives-glb U V = (β , γ) , δ
  where
   β : (U ⊓↓ V ⊑ U) holds
   β = ∧[ powerset-frame ]-lower₁ (λ - → - ε U) (λ - → - ε V)

   γ : (U ⊓↓ V ⊑ V) holds
   γ = ∧[ powerset-frame ]-lower₂ (λ - → - ε U) (λ - → - ε V)

   δ : ((W , _) : lower-bound (U , V)) → (W ⊑ U ⊓↓ V) holds
   δ (W , p , q) = ∧[ powerset-frame ]-greatest _ _ _ p q

 ⨆_ : Fam 𝓤 (Downward-Closed-Subsetₚ P) → Downward-Closed-Subsetₚ P
 ⨆ S = ⋃ (λ i - → - ε (S [ i ])) , †
  where
   open unions-of-small-families pt 𝓤 𝓤 ∣ P ∣ₚ

   † : is-downward-closed _≤_ (⋃ (λ i - → - ε (S [ i ]))) holds
   † a β x p = ∥∥-functor ‡ β
    where
     ‡ : (Σ i ꞉ index S , (a ε (S [ i ])) holds)
       → (Σ i ꞉ index S , (x ε (S [ i ])) holds)
     ‡ (i , β) = i , underlying-subset-is-downward-closed (S [ i ]) a β x p

 open Joins _⊑_

 ⨆-gives-lub : (S : Fam 𝓤 (Downward-Closed-Subsetₚ P))
             → ((⨆ S) is-lub-of S) holds
 ⨆-gives-lub S = † , ‡
  where
   † : ((⨆ S) is-an-upper-bound-of S) holds
   † i _ p = ∣ i , p ∣

   ‡ : ((U , _) : upper-bound S) → ((⨆ S) ⊑ U) holds
   ‡ ((U , δ) , p) x q = ∥∥-rec (holds-is-prop (U x)) γ q
    where
     γ : Σ i ꞉ index S , (x ε S [ i ]) holds
       → U x holds
     γ (i , r) = p i x r

\end{code}

Finally, we record the frame distributivity law and package everything up
into a frame.

\begin{code}

 downward-closed-subset-frame-data : frame-data 𝓤 𝓤 (Downward-Closed-Subsetₚ P)
 downward-closed-subset-frame-data = _⊑_ , top↓ , _⊓↓_ , ⨆_

 distributivity↓
  : (U : Downward-Closed-Subsetₚ P)
  → (S : Fam 𝓤 (Downward-Closed-Subsetₚ P))
  → U ⊓↓ (⨆ S) ＝ ⨆ ⁅ U ⊓↓ V ∣ V ε S ⁆
 distributivity↓ U S = ⊑-is-antisymmetric † ‡
  where
   † : (U ⊓↓ (⨆ S) ⊑ (⨆ ⁅ U ⊓↓ V ∣ V ε S ⁆)) holds
   † x (p , q) =
    ∥∥-rec (holds-is-prop (x ε (⨆ ⁅ U ⊓↓ V ∣ V ε S ⁆))) †₀ q
    where
     †₀ : Σ i ꞉ index S , (x ε S [ i ]) holds
        → (x ε (⨆ ⁅ U ⊓↓ V ∣ V ε S ⁆)) holds
     †₀ (i , r) = ∣ i , p , r ∣

   ‡ : ((⨆ ⁅ U ⊓↓ V ∣ V ε S ⁆) ⊑ U ⊓↓ (⨆ S)) holds
   ‡ x p = ∥∥-rec (holds-is-prop (x ε U ⊓↓ (⨆ S))) ‡₀ p
    where
     ‡₀ : (Σ i ꞉ index S , (x ε U ⊓↓ (S [ i ])) holds) → (x ε U ⊓↓ (⨆ S)) holds
     ‡₀ (i , q , r) = q , ∣ i , r ∣

 downward-closed-subset-frame-structure
  : frame-structure 𝓤 𝓤 (Downward-Closed-Subsetₚ P)
 downward-closed-subset-frame-structure = downward-closed-subset-frame-data
                                        , ⊑-is-partial-order
                                        , top↓-is-top
                                        , (λ (U , V) → ⊓↓-gives-glb U V)
                                        , ⨆-gives-lub
                                        , λ (U , S) → distributivity↓ U S

 downward-closed-subset-frame : Frame (𝓤 ⁺) 𝓤 𝓤
 downward-closed-subset-frame =
  Downward-Closed-Subsetₚ P , downward-closed-subset-frame-structure

\end{code}

The locale defined by this frame is called the _filter completion_.

\begin{code}

 filter-completion : Locale (𝓤 ⁺) 𝓤 𝓤
 filter-completion =
  record
  { ⟨_⟩ₗ         = Downward-Closed-Subsetₚ P
  ; frame-str-of = downward-closed-subset-frame-structure
  }

\end{code}
