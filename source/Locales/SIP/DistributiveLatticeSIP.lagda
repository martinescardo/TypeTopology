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

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Definition-SigmaBased fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
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
 𝟎₁ = DistributiveLattice.𝟎 Kᵣ

 𝟎₂ : A
 𝟎₂ = DistributiveLattice.𝟎 Lᵣ

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

 open HomomorphicEquivalences Kᵣ Lᵣ

 homomorphic-identity-equivalence-gives-order-agreement
  : is-homomorphic (≃-refl ∣ Lᵣ ∣ᵈ) holds
  → _≤₁_ ＝ _≤₂_
 homomorphic-identity-equivalence-gives-order-agreement (𝓂₁ , 𝓂₂) =
  dfunext fe λ x → dfunext fe λ y → † x y
   where
    † : (x y : ∣ Kᵣ ∣ᵈ) → x ≤₁ y ＝ x ≤₂ y
    † x y = ⇔-gives-＝ pe (x ≤₁ y) (x ≤₂ y) ‡
     where
      ‡ : (x ≤₁ y) ⇔ (x ≤₂ y) ＝ ⊤
      ‡ = holds-gives-equal-⊤ pe fe ((x ≤₁ y) ⇔ (x ≤₂ y)) (β , γ)
       where
        β : (x ≤₁ y ⇒ x ≤₂ y) holds
        β = 𝓂₁ (x , y)

        γ : (x ≤₂ y ⇒ x ≤₁ y) holds
        γ = 𝓂₂ (x , y)

\end{code}

Homomorphic identity equivalence gives top agreement.

\begin{code}

 open DistributiveLatticeIsomorphisms Kᵣ Lᵣ

 homomorphic-identity-equivalence-gives-top-agreement
  : is-homomorphic (≃-refl ∣ Lᵣ ∣ᵈ) holds
  → 𝟏₁ ＝ 𝟏₂
 homomorphic-identity-equivalence-gives-top-agreement 𝒽 = †
  where
   iso : DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ Kᵣ Lᵣ
   iso = to-isomorphismᵈᵣ (≃-refl A , 𝒽)

   † : preserves-𝟏 Kᵣ Lᵣ id holds
   † = Homomorphismᵈᵣ.h-preserves-𝟏 (Isomorphismᵈᵣ.𝓈 iso)

\end{code}

The identity function being homomorphic gives the equality of bottom elements.

\begin{code}

 homomorphic-identity-equivalence-gives-bottom-agreement
  : is-homomorphic (≃-refl ∣ Lᵣ ∣ᵈ) holds
  → 𝟎₁ ＝ 𝟎₂
 homomorphic-identity-equivalence-gives-bottom-agreement 𝒽 = †
  where
   iso : DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ Kᵣ Lᵣ
   iso = to-isomorphismᵈᵣ (≃-refl A , 𝒽)

   † : preserves-𝟎 Kᵣ Lᵣ id holds
   † = Homomorphismᵈᵣ.h-preserves-𝟎 (Isomorphismᵈᵣ.𝓈 iso)

\end{code}

The identity function being homomorphic gives the equality of meets.

\begin{code}

\end{code}

\begin{code}

 homomorphic-equivalence-gives-distributive-lattice-data-agreement
  : is-homomorphic (≃-refl A) holds
  → distributive-lattice-data-of A str₁ ＝ distributive-lattice-data-of A str₂
 homomorphic-equivalence-gives-distributive-lattice-data-agreement 𝒽 =
  goal
   where
    γ : 𝟏₁ , _∧₁_ , _∨₁_ ＝ 𝟏₂ , _∧₂_ , _∨₂_
    γ = {!!}

    β : 𝟎₁ , 𝟏₁ , _∧₁_ , _∨₁_ ＝ 𝟎₂ , 𝟏₂ , _∧₂_ , _∨₂_
    β = transport
         (λ - → 𝟎₁ , 𝟏₁ , _∧₁_ , _∨₁_ ＝ - , 𝟏₂ , _∧₂_ , _∨₂_)
         (homomorphic-identity-equivalence-gives-bottom-agreement 𝒽)
         (to-Σ-＝' γ)

    goal : 𝟎₁ , 𝟏₁ , _∧₁_ , _∨₁_  ＝ 𝟎₂ , 𝟏₂ , _∧₂_ , _∨₂_
    goal = {!!}

\end{code}

\begin{code}

 homomorphic-equivalence-gives-structural-equality
  : is-homomorphic (≃-refl A) holds
  → str₁ ＝ str₂
 homomorphic-equivalence-gives-structural-equality = {!!}

\end{code}
