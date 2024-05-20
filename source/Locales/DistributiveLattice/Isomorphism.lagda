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

open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Adjunctions.Properties pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import Locales.GaloisConnection pt fe
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
 open Some-Properties-Of-Posetal-Adjunctions

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

 open AdjointFunctorTheorem
 open GaloisConnectionBetween (poset-ofᵈ L) (poset-ofᵈ K)

 to-isomorphismᵈᵣ : Isomorphism₀ → Isomorphismᵈᵣ K L
 to-isomorphismᵈᵣ (e , (μ₁ , μ₂)) =
  record
   { 𝓈           = 𝓈
   ; 𝓇           = 𝓇
   ; r-cancels-s = †
   ; s-cancels-r = {!‡!}
   }
    where
     open DistributiveLattice L using () renaming (𝟏 to 𝟏L; 𝟎 to 𝟎L)
     open DistributiveLattice K using () renaming (𝟏 to 𝟏K; 𝟎 to 𝟎K)

     s = ⌜ e ⌝
     r = ⌜ ≃-sym e ⌝

     sₘ : poset-ofᵈ K ─m→ poset-ofᵈ L
     sₘ = s , μ₁

     rₘ : poset-ofᵈ L ─m→ poset-ofᵈ K
     rₘ = r , μ₂

     -- 𝒶𝒹𝒿 : (sₘ ⊣ rₘ) holds
     -- 𝒶𝒹𝒿 = monotone-equivalences-are-adjoint
     --        (s , μ₁)
     --        (r , μ₂)
     --        (inverses-are-sections' e)
     --        (inverses-are-retractions' e)

     𝒶𝒹𝒿 : (rₘ ⊣ sₘ) holds
     𝒶𝒹𝒿 = {!!}

     𝒶𝒹𝒿' : (poset-ofᵈ K GaloisConnectionBetween.⊣ poset-ofᵈ L) sₘ rₘ holds
     𝒶𝒹𝒿' = {!!}

     α₁ : preserves-𝟏 K L s holds
     α₁ = ≤-is-antisymmetric (poset-ofᵈ L) (𝟏ᵈ-is-top L (s 𝟏K)) †
      where
       † : (𝟏L ≤[ poset-ofᵈ L ] s 𝟏K) holds
       † = adjunction-law₁
            (poset-ofᵈ L)
            (poset-ofᵈ K)
            rₘ
            sₘ
            𝒶𝒹𝒿
            (𝟏ᵈ-is-top K (r 𝟏L))

     β₁ : preserves-∧ K L s holds
     β₁ = {!!}

     γ₁ : preserves-𝟎 K L s holds
     γ₁ = ≤-is-antisymmetric
           (poset-ofᵈ L)
           (adjunction-law₂ (poset-ofᵈ K) (poset-ofᵈ L) sₘ rₘ 𝒶𝒹𝒿' (𝟎ᵈ-is-bottom K (r 𝟎L)) )
           (𝟎ᵈ-is-bottom L (s 𝟎K))

     δ₁ : preserves-∨ K L s holds
     δ₁ = {!!}

     γ : preserves-𝟎 L K r holds
     γ = {!!}

     δ₂ : preserves-∨ L K r holds
     δ₂ = {!!}

     𝓈 : Homomorphismᵈᵣ K L
     𝓈 = record
          { h                 = s
          ; h-is-homomorphism = α₁ , β₁ , γ₁ , δ₁ }

     𝓇 : Homomorphismᵈᵣ L K
     𝓇 = record
          { h                 = r
          ; h-is-homomorphism = {!!} , {!!} , {!!} , δ₂
          }

     † : r ∘ s ∼ id
     † = {!!}

     ‡ : s ∘ r ∼ id
     ‡ = {!!}

\end{code}
