---
title:         Properties of distributive lattice isomorphisms
author:        Ayberk Tosun
date-started:  2024-06-01
dates-updated: [2024-06-09]
---

In this module, we collect properties of distributive lattice isomorphisms.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.DistributiveLattice.Isomorphism-Properties
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Adjunctions.Properties pt fe
open import Locales.Adjunctions.Properties-DistributiveLattice pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.Frame pt fe
open import Locales.GaloisConnection pt fe
open import Locales.SIP.DistributiveLatticeSIP ua pt sr
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

We work in a module parameterized by 𝓤-distributive-lattices `K` and `L`.

\begin{code}

module DistributiveLatticeIsomorphismProperties
        (K : DistributiveLattice 𝓤)
        (L : DistributiveLattice 𝓤)
       where

 open DistributiveLatticeIsomorphisms K L

\end{code}

Transport lemma for distributive lattices.

\begin{code}

 ≅d≅-transport : (K L : DistributiveLattice 𝓤)
               → (B : DistributiveLattice 𝓤 → 𝓣  ̇)
               → K ≅d≅ L
               → B K
               → B L
 ≅d≅-transport K L B iso = transport B †
  where
   † : K ＝ L
   † = isomorphic-distributive-lattices-are-equal K L iso

\end{code}

Added on 2024-06-09.

Distributive lattice isomorphisms are symmetric.

\begin{code}

≅d-sym : (K : DistributiveLattice 𝓤)
       → (L : DistributiveLattice 𝓥)
       → K ≅d≅ L → L ≅d≅ K
≅d-sym K L 𝒾 =
 record
  { 𝓈           = 𝓇 𝒾
  ; 𝓇           = 𝓈 𝒾
  ; r-cancels-s = s-cancels-r 𝒾
  ; s-cancels-r = r-cancels-s 𝒾
  }
   where
    open DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ

\end{code}

End of addition.
