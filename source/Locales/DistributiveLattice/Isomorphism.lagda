--------------------------------------------------------------------------------
title:        Isomorphisms of distributive lattices
author:       Ayberk Tosun
date-started: 2024-04-24
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Isomorphism
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

We work in a module parameterized by a 𝓤-distributive-lattice `L₁` and a
𝓥-distributive-lattice `L₂`.

\begin{code}

module DistributiveLatticeIsomorphisms (L₁ : DistributiveLattice 𝓤)
                                       (L₂ : DistributiveLattice 𝓥) where

\end{code}

The type `Isomorphismᵈᵣ L₁ L₂`, defined below, is the type of isomorphisms
between distributive lattices `L₁` and `L₂`.

\begin{code}

 record Isomorphismᵈᵣ : (𝓤 ⊔ 𝓥) ⁺  ̇ where
  field
   𝓈 : L₁ ─d→ L₂
   𝓇 : L₂ ─d→ L₁

  s : ∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ
  s = Homomorphismᵈᵣ.h 𝓈

  r : ∣ L₂ ∣ᵈ → ∣ L₁ ∣ᵈ
  r = Homomorphismᵈᵣ.h 𝓇

  s-is-homomorphism : is-homomorphismᵈ L₁ L₂ s holds
  s-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓈

  r-is-homomorphism : is-homomorphismᵈ L₂ L₁ r holds
  r-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓇

  field
   r-cancels-s : r ∘ s ∼ id
   s-cancels-r : s ∘ r ∼ id

\end{code}

Pretty syntax for `Isomorphismᵈᵣ`.

\begin{code}

Isomorphismᵈᵣ-Syntax : DistributiveLattice 𝓤
                     → DistributiveLattice 𝓥
                     → (𝓤 ⊔ 𝓥) ⁺  ̇
Isomorphismᵈᵣ-Syntax K L = DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ K L

infix 0 Isomorphismᵈᵣ-Syntax
syntax Isomorphismᵈᵣ-Syntax K L = K ≅d≅ L

\end{code}

Added on 2025-05-17.

Homomorphic equivalences.

\begin{code}

module HomomorphicEquivalences (K : DistributiveLattice 𝓤)
                               (L : DistributiveLattice 𝓤) where

 is-homomorphic : (∣ K ∣ᵈ ≃ ∣ L ∣ᵈ) → Ω 𝓤
 is-homomorphic e =  is-monotonic (poset-ofᵈ K) (poset-ofᵈ L) ⌜ e   ⌝
                  ∧ₚ is-monotonic (poset-ofᵈ L) (poset-ofᵈ K) ⌜ e⁻¹ ⌝
  where
   e⁻¹ : ∣ L ∣ᵈ ≃ ∣ K ∣ᵈ
   e⁻¹ = ≃-sym e

\end{code}

We now give an alternative definition of the notion of distributive lattice
isomorphism, which asserts the existence of a homomorphic equivalence.

\begin{code}

 Isomorphism₀ : 𝓤  ̇
 Isomorphism₀ = Σ e ꞉ ∣ K ∣ᵈ ≃ ∣ L ∣ᵈ , is-homomorphic e holds

\end{code}

These two notions of distributive lattice isomorphism are equivalent.

First, the part of the equivalence going from `Isomorphismᵈᵣ K L` to
`Isomorphism₀`.

\begin{code}

 open DistributiveLatticeIsomorphisms

 to-isomorphism₀ : Isomorphismᵈᵣ K L → Isomorphism₀
 to-isomorphism₀ 𝒾 = e , 𝒽
  where
   open Isomorphismᵈᵣ 𝒾
    using (s; 𝓈; 𝓇; r; s-cancels-r; r-cancels-s; s-is-homomorphism)
   open Homomorphismᵈᵣ 𝓈
    using ()
    renaming (h-preserves-∧ to 𝓈-preserves-∧; h-is-monotone to 𝓈-is-monotone)
   open Homomorphismᵈᵣ 𝓇
    using ()
    renaming (h-is-monotone to 𝓇-is-monotone)
   open DistributiveLattice K
    using ()
    renaming (_∧_ to _∧₁_)
   open DistributiveLattice L
    using ()
    renaming (_∧_ to _∧₂_)

   e : ∣ K ∣ᵈ ≃ ∣ L ∣ᵈ
   e = s , qinvs-are-equivs s (r , r-cancels-s , s-cancels-r)

   𝒽 : is-homomorphic e holds
   𝒽 = 𝓈-is-monotone , 𝓇-is-monotone

 to-isomorphismᵈᵣ : Isomorphism₀ → Isomorphismᵈᵣ K L
 to-isomorphismᵈᵣ (e , 𝒽) =
  record
   { 𝓈           = 𝓈
   ; 𝓇           = {!!}
   ; r-cancels-s = {!!}
   ; s-cancels-r = {!!}
   }
    where
     s = ⌜ e ⌝

     μ : preserves-𝟏 K L s holds
     μ = {!!}

     𝓈 : Homomorphismᵈᵣ K L
     𝓈 = record
          { h = s
          ; h-is-homomorphism = μ , {!!} }

\end{code}
