--------------------------------------------------------------------------------
title:        Properties of posetal adjunctions on distributive lattices
author:       Ayberk Tosun
date-started: 2024-05-20
--------------------------------------------------------------------------------

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

We work in a module parameterized by two posets `P` and `Q`.

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

\end{code}

\begin{code}

 open DistributiveLattice K using () renaming (𝟎 to 𝟎K; 𝟏 to 𝟏K)
 open DistributiveLattice L using () renaming (𝟎 to 𝟎L; 𝟏 to 𝟏L)

 right-adjoint-preserves-𝟏 : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                           → (𝒻 ⊣ ℊ) holds
                           → g 𝟏L ＝ 𝟏K
 right-adjoint-preserves-𝟏 𝒻@(f , _) ℊ@(g , _) 𝒶𝒹𝒿 = ≤-is-antisymmetric P † ‡
  where
   † : (g 𝟏L ≤[ poset-ofᵈ K ] 𝟏K) holds
   † = 𝟏ᵈ-is-top K (g 𝟏L)

   ‡ : (𝟏K ≤[ poset-ofᵈ K ] g 𝟏L) holds
   ‡ = adjunction-law₁ (poset-ofᵈ K) (poset-ofᵈ L) 𝒻 ℊ 𝒶𝒹𝒿 (𝟏ᵈ-is-top L (f 𝟏K))

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

\begin{code}

 right-adjoint-preserves-∧ : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                           → (𝒻 ⊣ ℊ) holds
                           → let
                              open DistributiveLattice L renaming (_∧_ to _∧∙_)
                             in
                              (y₁ y₂ : ∣ Q ∣ₚ) → g (y₁ ∧∙ y₂) ＝ {!!}
 right-adjoint-preserves-∧ = {!!}

\end{code}
