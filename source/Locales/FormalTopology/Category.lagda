---
title: Category of formal topologies
author: Ayberk Tosun
date-started: 2026-08-27
date-completed: 2026-09-02
---

This module defines the category of formal topologies as well as that of quasi
formal topologies, following [1] as a reference.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.FormalTopology.Category
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Categories.Pre
open import Categories.Wild
open import Locales.FormalTopology.Definition pt fe
open import Locales.FormalTopology.Morphism pt fe pe
open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Notation.UnderlyingType
open import UF.Base
open import UF.Logic
open import UF.Powerset
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier

open Formal-Topology-Morphism
open Quasi-Formal-Topology-Morphism

\end{code}

\section{Preliminaries}

We first prove a lemma establishing that `relational-image` commutes with
composition.

\begin{code}

open PropositionalTruncation pt

relational-image-commutes-with-composition
 : {A B C : 𝓤  ̇}
 → (f : A → 𝓟 B)
 → (g : B → 𝓟 C)
 → (U : 𝓟 A)
 → g ⦅ f ⦅ U ⦆ ⦆ ＝ (λ - → g ⦅ f - ⦆) ⦅ U ⦆
relational-image-commutes-with-composition f g U =
 subset-extensionality pe fe † ‡
  where
   † : g ⦅ f ⦅ U ⦆ ⦆ ⊆ (λ - → g ⦅ f - ⦆) ⦅ U ⦆
   † c = ∥∥-rec (holds-is-prop (c ∈ₚ ((λ - → g ⦅ f - ⦆) ⦅ U ⦆))) Ⅰ
    where
     Ⅰ : Σ (b , _) ꞉ 𝕋 (f ⦅ U ⦆) , c ∈ g b → c ∈ ((λ - → g ⦅ f - ⦆) ⦅ U ⦆)
     Ⅰ ((b , h) , p) =
      ∥∥-rec (holds-is-prop (c ∈ₚ ((λ - → g ⦅ f - ⦆) ⦅ U ⦆))) Ⅱ h
       where
        Ⅱ : (Σ (a , _) ꞉ 𝕋 U , b ∈ f a) → c ∈ ((λ - → g ⦅ f - ⦆) ⦅ U ⦆)
        Ⅱ ((a , μ) , q) = ∣ (a , μ) , Ⅲ ∣
         where
          Ⅲ : c ∈ (g ⦅ f a ⦆)
          Ⅲ = ∣ (b , q) , p ∣

   ‡ : (λ - → g ⦅ f - ⦆) ⦅ U ⦆ ⊆ g ⦅ f ⦅ U ⦆ ⦆
   ‡ c = ∥∥-rec (holds-is-prop (c ∈ₚ (g ⦅ f ⦅ U ⦆ ⦆))) Ⅰ
    where
     Ⅰ : Σ (a , _) ꞉ 𝕋 U , c ∈ (g ⦅ f a ⦆) → c ∈ (g ⦅ f ⦅ U ⦆ ⦆)
     Ⅰ ((a , p) , h) = ∥∥-rec (holds-is-prop (c ∈ₚ (g ⦅ f ⦅ U ⦆ ⦆))) Ⅱ h
      where
       Ⅱ : Σ (b , _) ꞉ 𝕋 (f a) , c ∈ g b → c ∈ (g ⦅ f ⦅ U ⦆ ⦆)
       Ⅱ ((b , q) , h′) = ∣ (b , ∣ (a , p) , q ∣) , h′ ∣

\end{code}

\section{Category of quasi formal topologies}

We start by defining composition of quasi formal topology morphisms.

\begin{code}

qftop-composition
 : (𝒜 ℬ 𝒞 : Quasi-Formal-Topology 𝓤)
 → (ℬ ─qft→ 𝒞)
 → (𝒜 ─qft→ ℬ)
 → (𝒜 ─qft→ 𝒞)
qftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻 = h , h-preserves-top , h-preserves-covering
 where
  f = fun 𝒜 ℬ 𝒻
  g = fun ℬ 𝒞 ℊ

  h : ⟨ 𝒜 ⟩ → 𝓟 ⟨ 𝒞 ⟩
  h = λ - → g ⦅ f - ⦆

  h-preserves-top : (full ◁Q⁺[ 𝒞 ] h ⦅ full ⦆) holds
  h-preserves-top = Ⅴ
   where
    Ⅰ : (full ◁Q⁺[ ℬ ] f ⦅ full ⦆) holds
    Ⅰ = fun-preserves-top 𝒜 ℬ 𝒻

    Ⅱ : (full ◁Q⁺[ 𝒞 ] g ⦅ full ⦆) holds
    Ⅱ = fun-preserves-top ℬ 𝒞 ℊ

    Ⅲ : (g ⦅ full ⦆ ◁Q⁺[ 𝒞 ] g ⦅ f ⦅ full ⦆ ⦆) holds
    Ⅲ = fun-preserves-covering-plus ℬ 𝒞 ℊ full (f ⦅ full ⦆) Ⅰ

    Ⅳ : (full ◁Q⁺[ 𝒞 ] g ⦅ f ⦅ full ⦆ ⦆) holds
    Ⅳ = transitivity-of-quasi-cover-plus 𝒞 full _ _ Ⅱ Ⅲ

    Ⅴ : (full ◁Q⁺[ 𝒞 ] h ⦅ full ⦆) holds
    Ⅴ = transport
         (λ - → (full ◁Q⁺[ 𝒞 ] -) holds)
         (relational-image-commutes-with-composition f g full)
         Ⅳ

  h-preserves-covering
   : preserves-covering 𝒜 𝒞 h holds
  h-preserves-covering a U κ = Ⅲ
   where
    Ⅰ : (f a ◁Q⁺[ ℬ ] f ⦅ U ⦆) holds
    Ⅰ = fun-preserves-covering 𝒜 ℬ 𝒻 a U κ

    Ⅱ : (g ⦅ f a ⦆ ◁Q⁺[ 𝒞 ] g ⦅ f ⦅ U ⦆ ⦆) holds
    Ⅱ = fun-preserves-covering-plus ℬ 𝒞 ℊ (f a) (f ⦅ U ⦆) Ⅰ

    Ⅲ : (g ⦅ f a ⦆ ◁Q⁺[ 𝒞 ] h ⦅ U ⦆) holds
    Ⅲ = transport
         (λ - → (g ⦅ f a ⦆ ◁Q⁺[ 𝒞 ] -) holds)
         (relational-image-commutes-with-composition f g U)
         Ⅱ

\end{code}

The identity morphism is neutral for composition.

\begin{code}

id-qftop-is-left-neutral
 : (𝒜 ℬ : Quasi-Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─qft→ ℬ)
 → qftop-composition 𝒜 ℬ ℬ (identity-morphism-qft ℬ) 𝒻 ＝ 𝒻
id-qftop-is-left-neutral 𝒜 ℬ 𝒻 =
 to-quasi-formal-topology-morphism-＝
  𝒜
  ℬ
  (qftop-composition 𝒜 ℬ ℬ (identity-morphism-qft ℬ) 𝒻)
  𝒻
  †
  where
   open singleton-subsets (carrier-of-quasi-formal-topology-is-set ℬ)

   f = fun 𝒜 ℬ 𝒻

   † : (a : ⟨ 𝒜 ⟩) → (λ - → ❴ - ❵) ⦅ f a ⦆ ＝ f a
   † a = subset-extensionality pe fe Ⅰ Ⅱ
    where
     Ⅰ : ❴_❵ ⦅ f a ⦆ ⊆ f a
     Ⅰ b = ∥∥-rec (holds-is-prop (b ∈ₚ f a)) ‡
      where
       ‡ : (Σ (a′ , _) ꞉ 𝕋 (f a) , b ∈ ❴ a′ ❵) → b ∈ f a
       ‡ ((a′ , p) , h) = transport (λ - → - ∈ f a) h p

     Ⅱ : f a ⊆ ❴_❵ ⦅ f a ⦆
     Ⅱ b μ = ∣ (b , μ) , refl ∣

id-qftop-is-right-neutral
 : (𝒜 ℬ : Quasi-Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─qft→ ℬ)
 → qftop-composition 𝒜 𝒜 ℬ 𝒻 (identity-morphism-qft 𝒜) ＝ 𝒻
id-qftop-is-right-neutral 𝒜 ℬ 𝒻 =
 to-quasi-formal-topology-morphism-＝
  𝒜
  ℬ
  (qftop-composition 𝒜 𝒜 ℬ 𝒻 (identity-morphism-qft 𝒜))
  𝒻
  †
  where
   open singleton-subsets (carrier-of-quasi-formal-topology-is-set 𝒜)

   f = fun 𝒜 ℬ 𝒻

   † : (a : ⟨ 𝒜 ⟩) → f ⦅ ❴ a ❵ ⦆ ＝ f a
   † a = subset-extensionality pe fe Ⅰ Ⅱ ⁻¹
    where
     Ⅰ = λ b p → ∣ (a , refl) , p ∣

     Ⅱ : f ⦅ ❴ a ❵ ⦆ ⊆ f a
     Ⅱ b = ∥∥-rec (holds-is-prop (f a b)) γ
      where
       γ : Σ (a′ , _) ꞉ 𝕋 ❴ a ❵ , b ∈ f a′ → b ∈ f a
       γ ((a′ , h) , q) = transport (λ - → b ∈ f -) (h ⁻¹) q

\end{code}

Associativity of `qftop-composition` stated with extensional equality of
functions. This follows directly from `relational-image-commutes-with-composition`.

\begin{code}

qftop-composition-is-associative-extensional
 : (𝒜 ℬ 𝒞 𝒟 : Quasi-Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─qft→ ℬ)
 → (ℊ : ℬ ─qft→ 𝒞)
 → (𝒽 : 𝒞 ─qft→ 𝒟)
 → fun 𝒜 𝒟 (qftop-composition 𝒜 𝒞 𝒟 𝒽 (qftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻))
   ∼ fun 𝒜 𝒟 (qftop-composition 𝒜 ℬ 𝒟 (qftop-composition ℬ 𝒞 𝒟 𝒽 ℊ) 𝒻)
qftop-composition-is-associative-extensional 𝒜 ℬ 𝒞 𝒟 𝒻 ℊ 𝒽 =
 relational-image-commutes-with-composition g h ∘ f
  where
   f = fun 𝒜 ℬ 𝒻
   g = fun ℬ 𝒞 ℊ
   h = fun 𝒞 𝒟 𝒽

\end{code}

Now, the actual associativity of composition for quasi formal topology
morphisms.

\begin{code}

qftop-composition-is-associative
 : (𝒜 ℬ 𝒞 𝒟 : Quasi-Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─qft→ ℬ)
 → (ℊ : ℬ ─qft→ 𝒞)
 → (𝒽 : 𝒞 ─qft→ 𝒟)
 → qftop-composition 𝒜 𝒞 𝒟 𝒽 (qftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻)
   ＝ qftop-composition 𝒜 ℬ 𝒟 (qftop-composition ℬ 𝒞 𝒟 𝒽 ℊ) 𝒻
qftop-composition-is-associative 𝒜 ℬ 𝒞 𝒟 𝒻 ℊ 𝒽 =
 to-quasi-formal-topology-morphism-＝ 𝒜 𝒟 _ _ †
  where
   open Quasi-Formal-Topology-Morphism 𝒜 𝒟
    hiding (to-quasi-formal-topology-morphism-＝; fun)

   † : [ qftop-composition 𝒜 𝒞 𝒟 𝒽 (qftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻) ]
       ∼ [ qftop-composition 𝒜 ℬ 𝒟 (qftop-composition ℬ 𝒞 𝒟 𝒽 ℊ) 𝒻 ]
   † = qftop-composition-is-associative-extensional 𝒜 ℬ 𝒞 𝒟 𝒻 ℊ 𝒽

\end{code}

We now have everything we need to define the precategory of quasi formal
topologies.

\begin{code}

QFTopWildCategory : (𝓤 : Universe) → WildCategory (𝓤 ⁺) (𝓤 ⁺)
QFTopWildCategory 𝓤 =
 wildcategory (Quasi-Formal-Topology 𝓤)
              _─qft→_
              (λ {𝒜} → identity-morphism-qft 𝒜)
              (λ {𝒜} {ℬ} {𝒞} → qftop-composition 𝒜 ℬ 𝒞)
              (λ {𝒜} {ℬ} → id-qftop-is-left-neutral 𝒜 ℬ)
              (λ {𝒜} {ℬ} → id-qftop-is-right-neutral 𝒜 ℬ)
              (λ {𝒜} {ℬ} {𝒞} {𝒟} → qftop-composition-is-associative 𝒜 ℬ 𝒞 𝒟)

QFTopPrecategory : (𝓤 : Universe) → Precategory (𝓤 ⁺) (𝓤 ⁺)
QFTopPrecategory 𝓤 = QFTopWildCategory 𝓤 , _─qft→_-is-set

\end{code}

\section{Category of formal topologies}

We define the category of formal topologies in this section, building atop the
category of quasi formal topologies.

\begin{code}

ftop-composition
 : (𝒜 ℬ 𝒞 : Formal-Topology 𝓤)
 → (ℬ ─ft→ 𝒞) → (𝒜 ─ft→ ℬ) → (𝒜 ─ft→ 𝒞)
ftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻 =
 from-qft-morphism 𝒜 𝒞 (qftop-composition 𝒜₀ ℬ₀ 𝒞₀ ℊ₀ 𝒻₀) β
  where
   𝒜₀ = underlying-quasi-formal-topology 𝒜
   ℬ₀ = underlying-quasi-formal-topology ℬ
   𝒞₀ = underlying-quasi-formal-topology 𝒞
   R  = underlying-poset-of-formal-topology 𝒞

   𝒻₀ = to-qft-morphism 𝒜 ℬ 𝒻
   ℊ₀ = to-qft-morphism ℬ 𝒞 ℊ

   f = ft-fun 𝒜 ℬ 𝒻
   g = ft-fun ℬ 𝒞 ℊ

   open Downward-Closure-Intersection-Syntax (λ x y → x ⊑[ ℬ ] y)
    renaming (_⊓_ to _⊓₂_; ↓_ to ↓₂_)
   open Downward-Closure-Intersection-Syntax (λ x y → x ⊑[ 𝒞 ] y)
    renaming (_⊓_ to _⊓₃_; ↓_ to ↓₃_)

   β : preserves-binary-meets 𝒜 𝒞 (relational-image g ∘ f) holds
   β a₁ a₂ c (μ₁ , μ₂) = ∥∥-rec₂ (holds-is-prop (_ ◁[ 𝒞 ] _)) † μ₁ μ₂
    where
     † : Σ c₁ ꞉ ⟨ 𝒞 ⟩ , c₁ ∈ (relational-image g ∘ f) a₁ × (c ≤[ R ] c₁) holds
       → Σ c₂ ꞉ ⟨ 𝒞 ⟩ , c₂ ∈ (relational-image g ∘ f) a₂ × (c ≤[ R ] c₂) holds
       → (c ◁[ 𝒞 ] (relational-image g ∘ f) ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆) holds
     † (c₁ , ν₁ , p₁) (c₂ , ν₂ , p₂) = ∥∥-rec₂ (holds-is-prop (_ ◁[ 𝒞 ] _)) γ ν₁ ν₂
      where
       γ : (Σ (b₁ , _) ꞉ 𝕋 (f a₁) , c₁ ∈ g b₁)
         → (Σ (b₂ , _) ꞉ 𝕋 (f a₂) , c₂ ∈ g b₂)
         → (c ◁[ 𝒞 ] (relational-image g ∘ f) ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆) holds
       γ ((b₁ , θ₁) , q₁) ((b₂ , θ₂) , q₂) =
         c                                                   ◁⟨  Ⅰ ⟩
         g b₁ ⊓₃ g b₂                                        ◁⁺⟨ Ⅱ ⟩
         g ⦅ lower-bounds ℬ ℬ b₁ b₂ ⦆                        ◁⁺⟨ Ⅲ ⟩
         g ⦅ f ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆ ⦆                  ＝⟨ Ⅳ ⟩c
         (relational-image g ∘ f) ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆ ■
         where
          Ⅰ : (c ◁[ 𝒞 ] g b₁ ⊓₃ g b₂) holds
          Ⅰ = reflexivity-of-quasi-cover
               𝒞₀
               c
               (g b₁ ⊓₃ g b₂)
               (∣ c₁ , q₁ , p₁ ∣ , ∣ c₂ , q₂ , p₂ ∣)

          Ⅱ : (g b₁ ⊓₃ g b₂ ◁⁺[ 𝒞 ] g ⦅ lower-bounds ℬ ℬ b₁ b₂ ⦆) holds
          Ⅱ = ft-fun-preserves-binary-meets ℬ 𝒞 ℊ b₁ b₂

          ξ : (lower-bounds ℬ ℬ b₁ b₂ ◁⁺[ ℬ ] f ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆) holds
          ξ = lower-bounds ℬ ℬ b₁ b₂                  ◁⁺⟨ Ⅵ ⟩
              f a₁ ⊓₂ f a₂                            ◁⁺⟨ Ⅶ ⟩
              f ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆ ■
               where
                open Quasi-Cover-Reasoning ℬ₀

                Ⅵ : (lower-bounds ℬ ℬ b₁ b₂ ◁⁺[ ℬ ] f a₁ ⊓₂ f a₂) holds
                Ⅵ b (r₁ , r₂) = reflexivity-of-quasi-cover
                                 ℬ₀
                                 b
                                 (f a₁ ⊓₂ f a₂)
                                 (∣ b₁ , θ₁ , r₁ ∣ , ∣ b₂ , θ₂ , r₂ ∣)

                Ⅶ : (f a₁ ⊓₂ f a₂ ◁⁺[ ℬ ] f ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆) holds
                Ⅶ = ft-fun-preserves-binary-meets 𝒜 ℬ 𝒻 a₁ a₂

          Ⅲ : (g ⦅ lower-bounds ℬ ℬ b₁ b₂ ⦆ ◁⁺[ 𝒞 ] g ⦅ f ⦅ lower-bounds 𝒜 𝒜 a₁ a₂ ⦆ ⦆)
               holds
          Ⅲ = fun-preserves-covering-plus ℬ₀ 𝒞₀ ℊ₀ (lower-bounds ℬ ℬ b₁ b₂) _ ξ

          Ⅳ = relational-image-commutes-with-composition f g (lower-bounds 𝒜 𝒜 a₁ a₂)

          open Quasi-Cover-Reasoning 𝒞₀

\end{code}

The identity morphism is left neutral for composition.

\begin{code}

id-ftop-is-left-neutral : (𝒜 ℬ : Formal-Topology 𝓤)
                        → (𝒻 : 𝒜 ─ft→ ℬ)
                        → ftop-composition 𝒜 ℬ ℬ (identity-morphism-ft ℬ) 𝒻 ＝ 𝒻
id-ftop-is-left-neutral 𝒜 ℬ 𝒻 = to-formal-topology-morphism-＝ 𝒜 ℬ _ 𝒻 †
 where
  𝒜₀ = underlying-quasi-formal-topology 𝒜
  ℬ₀ = underlying-quasi-formal-topology ℬ

  𝒻₀ = to-qft-morphism 𝒜 ℬ 𝒻

  † : ft-fun 𝒜 ℬ (ftop-composition 𝒜 ℬ ℬ (identity-morphism-ft ℬ) 𝒻) ∼ ft-fun 𝒜 ℬ 𝒻
  † = happly (ap (fun 𝒜₀ ℬ₀) (id-qftop-is-left-neutral 𝒜₀ ℬ₀ 𝒻₀))

\end{code}

The identity morphism is right neutral for composition.

\begin{code}

id-ftop-is-right-neutral
 : (𝒜 ℬ : Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─ft→ ℬ)
 → ftop-composition 𝒜 𝒜 ℬ 𝒻 (identity-morphism-ft 𝒜) ＝ 𝒻
id-ftop-is-right-neutral 𝒜 ℬ 𝒻 = to-formal-topology-morphism-＝ 𝒜 ℬ _ 𝒻 †
 where
  𝒜₀ = underlying-quasi-formal-topology 𝒜
  ℬ₀ = underlying-quasi-formal-topology ℬ

  𝒻₀ = to-qft-morphism 𝒜 ℬ 𝒻

  † : ft-fun 𝒜 ℬ (ftop-composition 𝒜 𝒜 ℬ 𝒻 (identity-morphism-ft 𝒜)) ∼ ft-fun 𝒜 ℬ 𝒻
  † = happly (ap (fun 𝒜₀ ℬ₀) (id-qftop-is-right-neutral 𝒜₀ ℬ₀ 𝒻₀))

\end{code}

Composition of formal topology morphisms is associative.

\begin{code}

ftop-composition-is-associative
 : (𝒜 ℬ 𝒞 𝒟 : Formal-Topology 𝓤)
 → (𝒻 : 𝒜 ─ft→ ℬ)
 → (ℊ : ℬ ─ft→ 𝒞)
 → (𝒽 : 𝒞 ─ft→ 𝒟)
 → ftop-composition 𝒜 𝒞 𝒟 𝒽 (ftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻)
   ＝ ftop-composition 𝒜 ℬ 𝒟 (ftop-composition ℬ 𝒞 𝒟 𝒽 ℊ) 𝒻
ftop-composition-is-associative 𝒜 ℬ 𝒞 𝒟 𝒻 ℊ 𝒽 =
 to-formal-topology-morphism-＝ 𝒜 𝒟 _ _ †
 where
  open Formal-Topology-Morphism 𝒜 𝒟
   hiding (to-formal-topology-morphism-＝; to-qft-morphism)

  𝒜₀ = underlying-quasi-formal-topology 𝒜
  ℬ₀ = underlying-quasi-formal-topology ℬ
  𝒞₀ = underlying-quasi-formal-topology 𝒞
  𝒟₀ = underlying-quasi-formal-topology 𝒟

  𝒻₀ = to-qft-morphism 𝒜 ℬ 𝒻
  ℊ₀ = to-qft-morphism ℬ 𝒞 ℊ
  𝒽₀ = to-qft-morphism 𝒞 𝒟 𝒽

  † : [ (ftop-composition 𝒜 𝒞 𝒟 𝒽 (ftop-composition 𝒜 ℬ 𝒞 ℊ 𝒻)) ]
      ∼
      [ (ftop-composition 𝒜 ℬ 𝒟 (ftop-composition ℬ 𝒞 𝒟 𝒽 ℊ) 𝒻) ]
  † = qftop-composition-is-associative-extensional 𝒜₀ ℬ₀ 𝒞₀ 𝒟₀ 𝒻₀ ℊ₀ 𝒽₀

\end{code}

Finally, we write down the precategory of formal topologies.

\begin{code}

FTopWildCategory : (𝓤 : Universe) → WildCategory (𝓤 ⁺) (𝓤 ⁺)
FTopWildCategory 𝓤 =
 wildcategory (Formal-Topology 𝓤)
              _─ft→_
              (λ {𝒜} → identity-morphism-ft 𝒜)
              (λ {𝒜} {ℬ} {𝒞} → ftop-composition 𝒜 ℬ 𝒞)
              (λ {𝒜} {ℬ} → id-ftop-is-left-neutral 𝒜 ℬ)
              (λ {𝒜} {ℬ} → id-ftop-is-right-neutral 𝒜 ℬ)
              (λ {𝒜} {ℬ} {𝒞} {𝒟} → ftop-composition-is-associative 𝒜 ℬ 𝒞 𝒟)

FTopPrecategory : (𝓤 : Universe) → Precategory (𝓤 ⁺) (𝓤 ⁺)
FTopPrecategory 𝓤 = FTopWildCategory 𝓤 , †
 where
  † : is-precategory (FTopWildCategory 𝓤)
  † 𝒜 ℬ = _─ft→_-is-set 𝒜 ℬ

\end{code}

[1]: Sara Negri. _Continuous domains as formal spaces_. Mathematical Structures
     in Computer Science, Volume 12, No. 1, pp. 19–52, 2002.
     DOI:10.1017/S0960129501003450
