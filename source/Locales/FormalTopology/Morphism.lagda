---
title: Morphism of formal topologies
author: Ayberk Tosun
date-started: 2026-08-25
date-completed: 2026-08-27
---

This module defines morphisms between formal topologies as well as quasi formal
topologies, following [1] as reference.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.FormalTopology.Morphism
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.FormalTopology.Definition pt fe
open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Notation.UnderlyingType
open import UF.Logic
open import UF.Powerset
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\section{Preliminaries}

Given a subset `U : 𝓟 A` and a function `f : A → 𝓟 B`, the type
`relational-image f U` denotes the union `⋃_{u ∈ U} f u`.

\begin{code}

relational-image : {A B : 𝓤 ̇} → (A → 𝓟 B) → 𝓟 A → 𝓟 B
relational-image {𝓤} {A} {B} f U = ⋃ {𝕋 U} λ { (a , _) → f a }
 where
  open unions-of-small-families pt 𝓤 𝓤 B

\end{code}

We define the syntax `f ⦅ U ⦆` for the image of a relation over a subset `U`.

\begin{code}

relational-image-syntax : {A B : 𝓤 ̇} → (A → 𝓟 B) → 𝓟 A → 𝓟 B
relational-image-syntax f U = relational-image f U

infix 8 relational-image-syntax
syntax relational-image-syntax f U = f ⦅ U ⦆

\end{code}

\section{Morphisms of quasi formal topologies}

\begin{code}

module Quasi-Formal-Topology-Morphism
        {𝓤 : Universe}
        (𝒜 : Quasi-Formal-Topology 𝓤)
        (ℬ : Quasi-Formal-Topology 𝓤)
       where

 private
  A = ⟨ 𝒜 ⟩
  B = ⟨ ℬ ⟩

\end{code}

Negri [1] defines a quasi formal topology morphism as a relation (1) preserving
the top subset, and (2) preserving the covering relation.

\begin{code}

 preserves-top : (A → 𝓟 B) → Ω 𝓤
 preserves-top f = full ◁Q⁺[ ℬ ] f ⦅ full ⦆

 preserves-covering : (A → 𝓟 B) → Ω (𝓤 ⁺)
 preserves-covering f =
  Ɐ a ꞉ A , Ɐ U ꞉ 𝓟 A , a ◁Q[ 𝒜 ] U ⇒ f a ◁Q⁺[ ℬ ] f ⦅ U ⦆

 is-quasi-formal-topology-morphism : (A → 𝓟 B) → Ω (𝓤 ⁺)
 is-quasi-formal-topology-morphism f = preserves-top f ∧ preserves-covering f

\end{code}

Using this, we write down the type of quasi formal topology morphisms between
quasi formal topologies `𝒜` and `ℬ`.

\begin{code}

 _─qft→_ : 𝓤 ⁺  ̇
 _─qft→_ = Σ f ꞉ (A → 𝓟 B) , is-quasi-formal-topology-morphism f holds

 infix 0 _─qft→_

\end{code}

We denote by `fun 𝒻` the underlying function of a quasi formal topology
morphism `𝒻`.

\begin{code}

 fun : _─qft→_ → A → 𝓟 B
 fun (f , _) = f

 instance
  canonical-map-quasi-formal-topology-morphism-function
   : Canonical-Map _─qft→_ (A → 𝓟 B)
  ι {{canonical-map-quasi-formal-topology-morphism-function}} = fun

\end{code}

We now define named projections for the `_─qft→_` type.

\begin{code}

 fun-is-quasi-formal-topology-morphism
  : (𝒻 : _─qft→_)
  → is-quasi-formal-topology-morphism [ 𝒻 ] holds
 fun-is-quasi-formal-topology-morphism (_ , φ) = φ

 fun-preserves-top : (𝒻 : _─qft→_) → preserves-top [ 𝒻 ] holds
 fun-preserves-top (_ , φ , _) = φ

 fun-respects-cover : (𝒻 : _─qft→_) → preserves-covering [ 𝒻 ] holds
 fun-respects-cover (_ , _ , ψ) = ψ

 fun-respects-cover-plus
  : (𝒻 : _─qft→_)
  → (Ɐ U V ꞉ 𝓟 ⟨ 𝒜 ⟩ , U ◁Q⁺[ 𝒜 ] V ⇒ [ 𝒻 ] ⦅ U ⦆ ◁Q⁺[ ℬ ] [ 𝒻 ] ⦅ V ⦆) holds
 fun-respects-cover-plus 𝒻 U V p b h =
  ∥∥-rec (holds-is-prop (b ∈ₚ (λ - → - ◁Q[ ℬ ] ([ 𝒻 ] ⦅ V ⦆)))) † h
   where
    f = [ 𝒻 ]

    † : Σ (a , _) ꞉ 𝕋 U , b ∈ f a → b ∈ (λ - → - ◁Q[ ℬ ] f ⦅ V ⦆)
    † ((a , μ) , q) = b         ◁⟨  Ⅰ ⟩
                      f a       ◁⁺⟨ Ⅱ ⟩
                      f ⦅ V ⦆   ■
     where
      open Quasi-Cover-Reasoning ℬ

      Ⅱ : (f a ◁Q⁺[ ℬ ] f ⦅ V ⦆) holds
      Ⅱ = fun-respects-cover 𝒻 a V (p a μ)

      Ⅰ : (b ◁Q[ ℬ ] f a) holds
      Ⅰ = reflexivity-of-quasi-cover ℬ b (f a) q

\end{code}

The lemma below states that the extensional equality of the underlying function
is sufficient to establish the equality of two quasi formal topology morphisms.

\begin{code}

 to-quasi-formal-topology-morphism-＝
  : (𝒻 ℊ : _─qft→_)
  → [ 𝒻 ] ∼ [ ℊ ]
  → 𝒻 ＝ ℊ
 to-quasi-formal-topology-morphism-＝ 𝒻 ℊ = to-subtype-＝ † ∘ dfunext fe
  where
   † : (f : A → 𝓟 B)
     → is-prop (is-quasi-formal-topology-morphism f holds)
   † f = holds-is-prop (is-quasi-formal-topology-morphism f)

\end{code}

\section{Morphisms of formal topologies}

We now define the notion of formal topology morphism, following Definition 2.4
of [1]. A formal topology morphism is a quasi formal topology morphism that
additionally preserves binary meets in the sense of Condition 2 from [1].

\begin{code}

module Formal-Topology-Morphism
        (𝒜 : Formal-Topology 𝓤)
        (ℬ : Formal-Topology 𝓤)
       where

 private
  A = ⟨ 𝒜 ⟩
  B = ⟨ ℬ ⟩

  𝒜₀ : Quasi-Formal-Topology 𝓤
  𝒜₀ = underlying-quasi-formal-topology 𝒜

  ℬ₀ : Quasi-Formal-Topology 𝓤
  ℬ₀ = underlying-quasi-formal-topology ℬ

 open Downward-Closure-Intersection-Syntax (λ a b → a ⊑[ ℬ ] b)
  renaming (_⊓_ to _⊓ℬ_)
 open Quasi-Formal-Topology-Morphism 𝒜₀ ℬ₀

\end{code}

We denote by `lower-bounds a b` the set of lower bounds for `a` and `b`.

\begin{code}

 lower-bounds : ⟨ 𝒜 ⟩ → ⟨ 𝒜 ⟩ → 𝓟 ⟨ 𝒜 ⟩
 lower-bounds a b = λ c → (c ⊑[ 𝒜 ] a) ∧ (c ⊑[ 𝒜 ] b)

\end{code}

A function `f : ⟨ 𝒜 ⟩ → 𝓟 ⟨ ℬ ⟩` is said to _preserve binary meets_
if `f ⦅ lower-bounds a₁ a₂ ⦆` covers `f a₁ ⊓ f a₂` for every pair of elements
`a₁ a₂ : ⟨ 𝒜 ⟩`.

\begin{code}

 preserves-binary-meets : (⟨ 𝒜 ⟩ → 𝓟 ⟨ ℬ ⟩) → Ω 𝓤
 preserves-binary-meets f =
  Ɐ a₁ a₂ ꞉ ⟨ 𝒜 ⟩ , (f a₁ ⊓ℬ f a₂) ◁⁺[ ℬ ] f ⦅ lower-bounds a₁ a₂ ⦆

\end{code}

A formal topology morphism is a function `f : ⟨ 𝒜 ⟩ → 𝓟 ⟨ ℬ ⟩` that

  1. preserves the top subset,
  2. preserves binary meets, and
  3. preserves the covering relation.

\begin{code}

 is-formal-topology-morphism : (A → 𝓟 B) → Ω (𝓤 ⁺)
 is-formal-topology-morphism f =
  preserves-top f ∧ preserves-binary-meets f ∧ preserves-covering f

\end{code}

Using this, we write down the type of formal topology morphisms between the
formal topologies `𝒜` and `ℬ` and then define the named projections.

\begin{code}

 _─ft→_ : 𝓤 ⁺  ̇
 _─ft→_ = Σ f ꞉ (A → 𝓟 B) , is-formal-topology-morphism f holds

 infix 0 _─ft→_

 ft-fun : _─ft→_ → A → 𝓟 B
 ft-fun (f , _) = f

 instance
  canonical-map-formal-topology-morphism-function
   : Canonical-Map _─ft→_ (A → 𝓟 B)
  ι {{canonical-map-formal-topology-morphism-function}} = ft-fun

 fun-is-formal-topology-morphism
  : (𝒻 : _─ft→_)
  → is-formal-topology-morphism [ 𝒻 ] holds
 fun-is-formal-topology-morphism (_ , φ) = φ

 ft-fun-preserves-top : (𝒻 : _─ft→_) → preserves-top [ 𝒻 ] holds
 ft-fun-preserves-top (_ , φ , _) = φ

 fun-preserves-binary-meets : (𝒻 : _─ft→_) → preserves-binary-meets [ 𝒻 ] holds
 fun-preserves-binary-meets (_ , _ , ψ , _) = ψ

 ft-fun-respects-cover : (𝒻 : _─ft→_) → preserves-covering [ 𝒻 ] holds
 ft-fun-respects-cover (_ , _ , _ , χ) = χ

\end{code}

Every formal topology morphism is a quasi formal topology morphism when
Condition (2) is dropped.

\begin{code}

 to-qft-morphism : _─ft→_ → _─qft→_
 to-qft-morphism (f , φ , _ , χ) = f , φ , χ

 from-qft-morphism : (𝒻 : _─qft→_) → preserves-binary-meets [ 𝒻 ] holds → _─ft→_
 from-qft-morphism 𝒻@(f , β , δ) γ =  f , β , γ , δ

\end{code}

We now prove the analogue of `to-quasi-formal-topology-morphism-＝` for formal
topologies.

\begin{code}

 to-formal-topology-morphism-＝
  : (𝒻 ℊ : _─ft→_)
  → [ 𝒻 ] ∼ [ ℊ ]
  → 𝒻 ＝ ℊ
 to-formal-topology-morphism-＝ 𝒻 ℊ = to-subtype-＝ † ∘ dfunext fe
  where
   † : (f : A → 𝓟 B) → is-prop (is-formal-topology-morphism f holds)
   † f = holds-is-prop (is-formal-topology-morphism f)

\end{code}

\section{Identity morphisms}

In this section, we define the identity morphisms on formal and quasi formal
topologies.

\begin{code}

open Quasi-Formal-Topology-Morphism hiding (preserves-top; preserves-covering)

identity-morphism-qft : (𝒜 : Quasi-Formal-Topology 𝓤) → 𝒜 ─qft→ 𝒜
identity-morphism-qft 𝒜 = (λ a → ❴ a ❵) , β , γ
 where
  open singleton-subsets (carrier-of-quasi-formal-topology-is-set 𝒜)
  open Quasi-Formal-Topology-Morphism 𝒜 𝒜

  β : preserves-top (λ - → ❴ - ❵) holds
  β a ⋆ = reflexivity-of-quasi-cover 𝒜 a (❴_❵ ⦅ full ⦆) ∣ (a , ⋆) , refl ∣

  singleton-image-lemma : (U : 𝓟 ⟨ 𝒜 ⟩) → ((λ - → ❴ - ❵) ⦅ U ⦆) ＝ U
  singleton-image-lemma U = subset-extensionality pe fe Ⅰ Ⅱ
   where
    Ⅰ : (❴_❵ ⦅ U ⦆) ⊆ U
    Ⅰ a p = ∥∥-rec (holds-is-prop (a ∈ₚ U)) † p
     where
      † : _
      † ((b , h) , q) = transport (λ - → - ∈ U) q h

    Ⅱ : U ⊆ (❴_❵ ⦅ U ⦆)
    Ⅱ a p = ∣ (a , p) , refl ∣

  γ : preserves-covering (λ - → ❴ - ❵) holds
  γ a U p =
   transport (λ V → (❴ a ❵ ◁Q⁺[ 𝒜 ] V) holds) (singleton-image-lemma U ⁻¹) †
    where
     † : (❴ a ❵ ◁Q⁺[ 𝒜 ] U) holds
     † b q = transport (λ - → cover-of-quasi-formal-topology 𝒜 - U holds) q p

open Formal-Topology-Morphism

identity-morphism-ft : (𝒜 : Formal-Topology 𝓤) → 𝒜 ─ft→ 𝒜
identity-morphism-ft 𝒜 = from-qft-morphism 𝒜 𝒜 (identity-morphism-qft 𝒜₀) β
 where
  𝒜₀ = underlying-quasi-formal-topology 𝒜
  P  = underlying-poset-of-formal-topology 𝒜

  open singleton-subsets (carrier-of-quasi-formal-topology-is-set 𝒜₀)

  β : preserves-binary-meets 𝒜 𝒜 (fun 𝒜₀ 𝒜₀ (identity-morphism-qft 𝒜₀)) holds
  β a₁ a₂ a (p₁ , p₂) = ∥∥-rec₂ (holds-is-prop (a ◁Q[ 𝒜₀ ] _)) γ p₁ p₂
   where
    γ : Σ a₁′ ꞉ ⟨ 𝒜 ⟩ , (a₁ ＝ a₁′) × (a ≤[ P ] a₁′) holds
      → Σ a₂′ ꞉ ⟨ 𝒜 ⟩ , (a₂ ＝ a₂′) × (a ≤[ P ] a₂′) holds
      → (a ◁[ 𝒜 ] ❴_❵ ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆) holds
    γ (a₁′ , r₁ , q₁) (a₂′ , r₂ , q₂) =
     reflexivity-of-quasi-cover 𝒜₀ a _ ∣ (a , Ⅰ , Ⅱ) , refl ∣
      where
       open PosetReasoning P

       Ⅰ : (a ≤[ P ] a₁) holds
       Ⅰ = a ≤⟨ q₁ ⟩ a₁′ ＝⟨ r₁ ⁻¹ ⟩ₚ a₁ ■

       Ⅱ : (a ≤[ P ] a₂) holds
       Ⅱ = a ≤⟨ q₂ ⟩ a₂′ ＝⟨ r₂ ⁻¹ ⟩ₚ a₂ ■

\end{code}

\section{Bibliography}

[1]: Sara Negri. _Continuous domains as formal spaces_. Mathematical Structures
     in Computer Science, Volume 12, No. 1, pp. 19–52, 2002.
     DOI:10.1017/S0960129501003450
