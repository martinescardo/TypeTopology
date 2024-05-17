--------------------------------------------------------------------------------
title:          SIP for distributive lattices
author:         Ayberk Tosun
date-started:   2024-05-16
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.SIP.DistributiveLatticeSIP
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Definition-SigmaBased fe pt

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open sip hiding (⟨_⟩)

\end{code}

We work in a module parameterized by two distributive lattice structures that
we call `str₁` and `str₂`.

\begin{code}

module SIP-For-Distributive-Lattices
        {A : 𝓤  ̇}
        (str₁ str₂ : Distributive-Lattice-Structure A)
       where

\end{code}

We denote by `K` and `L` the distributive lattices `(A , str₁)` and `(B , str₂)`.

\begin{code}

 K : Distributive-Lattice₀ 𝓤
 K = A , str₁

 L : Distributive-Lattice₀ 𝓤
 L = A , str₂

\end{code}

To avoid using projections, we also define the record-based versions of these
two distributive lattices.

\begin{code}

 Kᵣ : DistributiveLattice 𝓤
 Kᵣ = to-distributive-lattice 𝓤 K

 Lᵣ : DistributiveLattice 𝓤
 Lᵣ = to-distributive-lattice 𝓤 L

\end{code}

We define a bunch of other abbreviations that we will use throughout this
module.

\begin{code}

 lattice-data-of-K : Distributive-Lattice-Data A
 lattice-data-of-K = pr₁ str₁

 lattice-data-of-L : Distributive-Lattice-Data A
 lattice-data-of-L = pr₁ str₂

 _≤₁_ : A → A → Ω 𝓤
 _≤₁_ = λ x y → x ≤[ poset-ofᵈ Kᵣ ] y

 _≤₂_ : A → A → Ω 𝓤
 _≤₂_ = λ x y → x ≤[ poset-ofᵈ Lᵣ  ] y

 𝟏₁ : A
 𝟏₁ = DistributiveLattice.𝟏 Kᵣ

 𝟏₂ : A
 𝟏₂ = DistributiveLattice.𝟏 Lᵣ

 𝟎₁ : A
 𝟎₁ = DistributiveLattice.𝟏 Kᵣ

 𝟎₂ : A
 𝟎₂ = DistributiveLattice.𝟏 Lᵣ

 _∧₁_ : A → A → A
 _∧₁_ = λ x y → x ∧∙ y
  where
   open DistributiveLattice Kᵣ renaming (_∧_ to _∧∙_)

 _∧₂_ : A → A → A
 _∧₂_ = λ x y → x ∧∙ y
  where
   open DistributiveLattice Lᵣ renaming (_∧_ to _∧∙_)

 _∨₁_ : A → A → A
 _∨₁_ = λ x y → x ∨∙ y
  where
   open DistributiveLattice Kᵣ renaming (_∨_ to _∨∙_)

 _∨₂_ : A → A → A
 _∨₂_ = λ x y → x ∨∙ y
  where
   open DistributiveLattice Lᵣ renaming (_∨_ to _∨∙_)

\end{code}

\begin{code}

\end{code}
