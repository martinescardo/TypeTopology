---
title:        The Alexandroff locale
author:       Ayberk Tosun
date-started: 2026-10-28
---

This module contains a definition of the frame of downward-closed subsets of a
poset. We refer to the locale this defines as the _Alexandroff locale_.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size hiding (is-locally-small)
open import UF.Subsingletons

module Locales.Alexandroff.Definition
        (𝓤  : Universe)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext) where

open import Locales.DiscreteLocale.Definition fe pe pt
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

\end{code}

We start by writing down the type of downward-closed subsets of `P`.

\begin{code}

 is-downward-closed : (∣ P ∣ₚ → Ω 𝓤) → Ω 𝓤
 is-downward-closed U = Ɐ u x ꞉ ∣ P ∣ₚ , u ∈ₚ U ⇒ x ≤[ P ] u ⇒ x ∈ₚ U

 Downward-Closed-Subset : 𝓤 ⁺  ̇
 Downward-Closed-Subset = Σ U ꞉ 𝓟 ∣ P ∣ₚ , is-downward-closed U holds

\end{code}

Given a downward-closed subset `𝔘`, we define the notation `x ε 𝔘` for `𝔘`'s
underlying subset.

\begin{code}

 underlying-subset-syntax : Downward-Closed-Subset → 𝓟 {𝓤} ∣ P ∣ₚ
 underlying-subset-syntax (U , _) = U

 syntax underlying-subset-syntax 𝔘 x = x ε 𝔘
 infix 8 underlying-subset-syntax

 underlying-subset-is-downward-closed : (U : Downward-Closed-Subset)
                                      → is-downward-closed (λ - → - ε U) holds
 underlying-subset-is-downward-closed (_ , φ) = φ

\end{code}

This forms a frame when ordered under inclusion. We make use of the powerset
frame from `Locales.DiscreteLocale.Definition` when carrying out this
construction.

\begin{code}

 _⊑_ : Downward-Closed-Subset → Downward-Closed-Subset → Ω 𝓤
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
   (holds-is-prop ∘ is-downward-closed)
   (≤-is-antisymmetric powerset-poset β γ)

 ⊑-is-partial-order : is-partial-order Downward-Closed-Subset _⊑_
 ⊑-is-partial-order = (⊑-is-reflexive , ⊑-is-transitive)
                    , ⊑-is-antisymmetric

 top↓ : Downward-Closed-Subset
 top↓ = full , †
  where
   † : is-downward-closed full holds
   † _ _ ⋆ _ = ⋆

 top↓-is-top : (U : Downward-Closed-Subset) → (U ⊑ top↓) holds
 top↓-is-top _ _ _ = ⋆

 _⊓↓_ : Downward-Closed-Subset → Downward-Closed-Subset → Downward-Closed-Subset
 (U , φ) ⊓↓ (V , ψ) = U ∩ V , †
  where
   † : is-downward-closed (U ∩ V) holds
   † x y (β , γ) p = φ x y β p , ψ x y γ p

 infixl 35 _⊓↓_

 open Meets _⊑_

 ⊓↓-gives-glb : (U V : Downward-Closed-Subset)
              → ((U ⊓↓ V) is-glb-of (U , V)) holds
 ⊓↓-gives-glb U V = (β , γ) , δ
  where
   β : (U ⊓↓ V ⊑ U) holds
   β = ∧[ powerset-frame ]-lower₁ (λ - → - ε U) (λ - → - ε V)

   γ : (U ⊓↓ V ⊑ V) holds
   γ = ∧[ powerset-frame ]-lower₂ (λ - → - ε U) (λ - → - ε V)

   δ : ((W , _) : lower-bound (U , V)) → (W ⊑ U ⊓↓ V) holds
   δ (W , p , q) = ∧[ powerset-frame ]-greatest _ _ _ p q

 ⨆_ : Fam 𝓤 Downward-Closed-Subset → Downward-Closed-Subset
 ⨆ S = ⋃ (λ i - → - ε (S [ i ])) , †
  where
   open unions-of-small-families pt 𝓤 𝓤 ∣ P ∣ₚ

   † : is-downward-closed (⋃ (λ i - → - ε (S [ i ]))) holds
   † a x β p = ∥∥-functor ‡ β
    where
     ‡ : (Σ i ꞉ index S , (a ε (S [ i ])) holds)
       → (Σ i ꞉ index S , (x ε (S [ i ])) holds)
     ‡ (i , β) = i , underlying-subset-is-downward-closed (S [ i ]) a x β p

 open Joins _⊑_

 ⨆-gives-lub : (S : Fam 𝓤 Downward-Closed-Subset) → ((⨆ S) is-lub-of S) holds
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

 downward-closed-subset-frame-data : frame-data 𝓤 𝓤 Downward-Closed-Subset
 downward-closed-subset-frame-data = _⊑_ , top↓ , _⊓↓_ , ⨆_

 distributivity↓
  : (U : Downward-Closed-Subset)
  → (S : Fam 𝓤 Downward-Closed-Subset)
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
  : frame-structure 𝓤 𝓤 Downward-Closed-Subset
 downward-closed-subset-frame-structure = downward-closed-subset-frame-data
                                        , ⊑-is-partial-order
                                        , top↓-is-top
                                        , (λ (U , V) → ⊓↓-gives-glb U V)
                                        , ⨆-gives-lub
                                        , λ (U , S) → distributivity↓ U S

 downward-closed-subset-frame : Frame (𝓤 ⁺) 𝓤 𝓤
 downward-closed-subset-frame =
  Downward-Closed-Subset , downward-closed-subset-frame-structure

\end{code}

The locale defined by this frame is called the _Alexandroff locale_.

\begin{code}

 alexandroff : Locale (𝓤 ⁺) 𝓤 𝓤
 alexandroff =
  record
  { ⟨_⟩ₗ         = Downward-Closed-Subset
  ; frame-str-of = downward-closed-subset-frame-structure
  }

\end{code}
