---
title:        Properties of posetal adjunctions on distributive lattices
author:       Ayberk Tosun
date-started: 2024-05-20
---

Many properties of posetal adjunctions have previously been written down, mostly
in the context of frames. In this module, we collect some of these properties in
the more general case where the lattices in consideration are not necessarily
frames.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc

module Locales.Adjunctions.Properties-DistributiveLattice
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Adjunctions.Properties pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import Locales.GaloisConnection pt fe
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We work in a module parameterized by two distributive lattices `K` and `L`.

\begin{code}

module Properties-Of-Posetal-Adjunctions-on-Distributive-Lattices
        (K : DistributiveLattice 𝓤)
        (L : DistributiveLattice 𝓥)
       where

 open GaloisConnectionBetween (poset-ofᵈ K) (poset-ofᵈ L)
 open Some-Properties-Of-Posetal-Adjunctions

\end{code}

We denote by `P` and `Q` the underlying posets of distributive lattices `K` and
`L`.

\begin{code}

 P : Poset 𝓤 𝓤
 P = poset-ofᵈ K

 Q : Poset 𝓥 𝓥
 Q = poset-ofᵈ L

 open DistributiveLattice K
  using ()
  renaming (𝟎 to 𝟎K; 𝟏 to 𝟏K; _∧_ to _∧ₖ_; _∨_ to _∨ₖ_)
 open DistributiveLattice L
  using ()
  renaming (𝟎 to 𝟎L; 𝟏 to 𝟏L; _∧_ to _∧ₗ_; _∨_ to _∨ₗ_)

\end{code}

Right adjoints preserve the top element `𝟏`.

\begin{code}

 right-adjoint-preserves-𝟏 : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                           → (𝒻 ⊣ ℊ) holds
                           → g 𝟏L ＝ 𝟏K
 right-adjoint-preserves-𝟏 𝒻@(f , _) ℊ@(g , _) 𝒶𝒹𝒿 = ≤-is-antisymmetric P † ‡
  where
   † : (g 𝟏L ≤[ poset-ofᵈ K ] 𝟏K) holds
   † = 𝟏ᵈ-is-top K (g 𝟏L)

   ‡ : (𝟏K ≤[ poset-ofᵈ K ] g 𝟏L) holds
   ‡ = adjunction-law₁ (poset-ofᵈ K) (poset-ofᵈ L) 𝒻 ℊ 𝒶𝒹𝒿 (𝟏ᵈ-is-top L (f 𝟏K))

\end{code}

Left adjoints preserve the bottom element `𝟎`.

\begin{code}

 left-adjoint-preserves-𝟎 : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                          → (𝒻 ⊣ ℊ) holds
                          → f 𝟎K ＝ 𝟎L
 left-adjoint-preserves-𝟎 𝒻@(f , _) ℊ@(g , _) 𝒶𝒹𝒿 = ≤-is-antisymmetric Q † ‡
  where
   † : (f 𝟎K ≤[ poset-ofᵈ L ] 𝟎L) holds
   † = adjunction-law₂ P Q 𝒻 ℊ 𝒶𝒹𝒿 (𝟎ᵈ-is-bottom K (g 𝟎L))

   ‡ : (𝟎L ≤[ poset-ofᵈ L ] f 𝟎K) holds
   ‡ = 𝟎ᵈ-is-bottom L (f 𝟎K)

\end{code}

Right adjoints preserve binary meets.

\begin{code}

 right-adjoint-preserves-∧ : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                           → (𝒻 ⊣ ℊ) holds
                           → (x y : ∣ Q ∣ₚ) → g (x ∧ₗ y) ＝ g x ∧ₖ g y
 right-adjoint-preserves-∧ 𝒻@(f , μ₁) ℊ@(g , μ₂) 𝒶𝒹𝒿 x y =
  ≤-is-antisymmetric P † ‡
   where
    † : (g (x ∧ₗ y) ≤[ P ] g x ∧ₖ g y) holds
    † = ∧-is-greatest K (g x) (g y) (g (x ∧ₗ y)) (†₁ , †₂)
     where
      †₁ : (g (x ∧ₗ y) ≤[ P ] g x) holds
      †₁ = μ₂ (x ∧ₗ y , x) (∧-is-a-lower-bound₁ L x y)

      †₂ : (g (x ∧ₗ y) ≤[ P ] g y) holds
      †₂ = μ₂ (x ∧ₗ y , y) (∧-is-a-lower-bound₂ L x y)

    ‡ : (g x ∧ₖ g y ≤[ P ] g (x ∧ₗ y)) holds
    ‡ =
     adjunction-law₁ P Q 𝒻 ℊ 𝒶𝒹𝒿 (∧-is-greatest L x y (f (g x ∧ₖ g y)) (‡₁ , ‡₂))
      where
       ‡₁ : (f (g x ∧ₖ g y) ≤[ Q ] x) holds
       ‡₁ = adjunction-law₂ P Q 𝒻 ℊ 𝒶𝒹𝒿 (∧-is-a-lower-bound₁ K (g x) (g y))

       ‡₂ : (f (g x ∧ₖ g y) ≤[ Q ] y) holds
       ‡₂ = adjunction-law₂ P Q 𝒻 ℊ 𝒶𝒹𝒿 (∧-is-a-lower-bound₂ K (g x) (g y))

\end{code}

Left adjoints preserve binary joins.

\begin{code}

 left-adjoint-preserves-∨ : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                          → (𝒻 ⊣ ℊ) holds
                          → (x y : ∣ P ∣ₚ) → f (x ∨ₖ y) ＝ f x ∨ₗ f y
 left-adjoint-preserves-∨ 𝒻@(f , μ₁) ℊ@(g , μ₂) 𝒶𝒹𝒿 x y =
  ≤-is-antisymmetric Q † ‡
   where
    † : (f (x ∨ₖ y) ≤[ Q ] f x ∨ₗ f y) holds
    † =
     adjunction-law₂
      P
      Q
      𝒻
      ℊ
      𝒶𝒹𝒿
      (∨-is-least K x y (g (f x ∨ₗ f y)) (†₁ , †₂))
       where
        †₁ : (x ≤[ P ] g (f x ∨ₗ f y)) holds
        †₁ = adjunction-law₁ P Q 𝒻 ℊ 𝒶𝒹𝒿 (∨-is-an-upper-bound₁ L (f x) (f y))

        †₂ : (y ≤[ P ] g (f x ∨ₗ f y)) holds
        †₂ = adjunction-law₁ P Q 𝒻 ℊ 𝒶𝒹𝒿 (∨-is-an-upper-bound₂ L (f x) (f y))

    ‡ : (f x ∨ₗ f y ≤[ Q ] f (x ∨ₖ y)) holds
    ‡ = ∨-is-least L (f x) (f y) (f (x ∨ₖ y)) (‡₁ , ‡₂)
     where
      ‡₁ : (f x ≤ᵈ[ L ] f (x ∨ₖ y)) holds
      ‡₁ = μ₁ (x , x ∨ₖ y) (∨-is-an-upper-bound₁ K x y)

      ‡₂ : (f y ≤ᵈ[ L ] f (x ∨ₖ y)) holds
      ‡₂ = μ₁ (y , x ∨ₖ y) (∨-is-an-upper-bound₂ K x y)

\end{code}
