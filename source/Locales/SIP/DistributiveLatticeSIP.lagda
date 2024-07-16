---
title:          SIP for distributive lattices
author:         Ayberk Tosun
date-started:   2024-05-16
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

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

 private
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

The identity equivalence being homomorphic gives the equality of top elements.

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

 homomorphic-identity-equivalence-gives-meet-agreement
  : is-homomorphic (≃-refl ∣ Lᵣ ∣ᵈ) holds
  → _∧₁_ ＝ _∧₂_
 homomorphic-identity-equivalence-gives-meet-agreement 𝒽 =
  dfunext fe λ x → dfunext fe λ y → φ x y
   where
    iso : Isomorphismᵈᵣ
    iso = to-isomorphismᵈᵣ (≃-refl A , 𝒽)

    φ : preserves-∧ Kᵣ Lᵣ id holds
    φ = Homomorphismᵈᵣ.h-preserves-∧ (Isomorphismᵈᵣ.𝓈 iso)

\end{code}

The identity function being homomorphic gives join agreement.

\begin{code}

 homomorphic-identity-equivalence-gives-join-agreement
  : is-homomorphic (≃-refl ∣ Lᵣ ∣ᵈ) holds
  → _∨₁_ ＝ _∨₂_
 homomorphic-identity-equivalence-gives-join-agreement 𝒽 =
  dfunext fe λ x → dfunext fe λ y → φ x y
   where
    iso : Isomorphismᵈᵣ
    iso = to-isomorphismᵈᵣ (≃-refl A , 𝒽)

    φ : preserves-∨ Kᵣ Lᵣ id holds
    φ = Homomorphismᵈᵣ.h-preserves-∨ (Isomorphismᵈᵣ.𝓈 iso)


\end{code}

If the identity equivalence is homomorphic, then the two distributive lattice
structures must be equal.

\begin{code}

 abstract
  homomorphic-equivalence-gives-distributive-lattice-data-agreement
   : is-homomorphic (≃-refl A) holds
   → distributive-lattice-data-of A str₁ ＝ distributive-lattice-data-of A str₂
  homomorphic-equivalence-gives-distributive-lattice-data-agreement 𝒽 = β
   where
    ϵ : _∨₁_ ＝ _∨₂_
    ϵ = homomorphic-identity-equivalence-gives-join-agreement 𝒽

    δ : _∧₁_ , _∨₁_ ＝ _∧₂_ , _∨₂_
    δ = transport
         (λ - → _∧₁_ , _∨₁_ ＝ - , _∨₂_)
         (homomorphic-identity-equivalence-gives-meet-agreement 𝒽)
         (to-Σ-＝' ϵ)

    γ : 𝟏₁ , _∧₁_ , _∨₁_ ＝ 𝟏₂ , _∧₂_ , _∨₂_
    γ = transport
         (λ - → 𝟏₁ , _∧₁_ , _∨₁_ ＝ - , _∧₂_ , _∨₂_)
         (homomorphic-identity-equivalence-gives-top-agreement 𝒽)
         (to-Σ-＝' δ)

    β : 𝟎₁ , 𝟏₁ , _∧₁_ , _∨₁_ ＝ 𝟎₂ , 𝟏₂ , _∧₂_ , _∨₂_
    β = transport
         (λ - → 𝟎₁ , 𝟏₁ , _∧₁_ , _∨₁_ ＝ - , 𝟏₂ , _∧₂_ , _∨₂_)
         (homomorphic-identity-equivalence-gives-bottom-agreement 𝒽)
         (to-Σ-＝' γ)

 abstract
  homomorphic-equivalence-gives-structural-equality
   : is-homomorphic (≃-refl A) holds
   → str₁ ＝ str₂
  homomorphic-equivalence-gives-structural-equality 𝒽 =
   to-subtype-＝
    satisfying-distributive-lattice-laws-is-prop
    (homomorphic-equivalence-gives-distributive-lattice-data-agreement 𝒽)

\end{code}

The distributive lattice structure is a standard notion of structure.

\begin{code}

distributive-lattice-sns-data : SNS Distributive-Lattice-Structure 𝓤
distributive-lattice-sns-data {𝓤} = ι , ρ , θ
 where
  ι : (K′ L′ : Distributive-Lattice₀ 𝓤) → sip.⟨ K′ ⟩ ≃ sip.⟨ L′ ⟩ → 𝓤  ̇
  ι K′ L′ e = is-homomorphic e holds
   where
    K′ᵣ = to-distributive-lattice 𝓤 K′
    L′ᵣ = to-distributive-lattice 𝓤 L′

    open HomomorphicEquivalences K′ᵣ L′ᵣ

  ρ : (L : Distributive-Lattice₀ 𝓤) → ι L L (≃-refl sip.⟨ L ⟩)
  ρ L = (λ _ → id) , (λ _ → id)

  θ : {X : 𝓤  ̇}
    → (str₁ str₂ : Distributive-Lattice-Structure X)
    → is-equiv (canonical-map ι ρ str₁ str₂)
  θ {X} str₁ str₂ = (homomorphic-equivalence-gives-structural-equality , †)
                  , (homomorphic-equivalence-gives-structural-equality , ‡)
   where
    open SIP-For-Distributive-Lattices str₁ str₂
    open HomomorphicEquivalences

    Kᵣ = to-distributive-lattice 𝓤 (X , str₁)
    Lᵣ = to-distributive-lattice 𝓤 (X , str₂)

    † : (h : is-homomorphic Kᵣ Lᵣ (≃-refl X) holds)
      → let
         p = homomorphic-equivalence-gives-structural-equality h
        in
         canonical-map ι ρ str₁ str₂ p ＝ h
    † h = holds-is-prop
           (is-homomorphic Kᵣ Lᵣ (≃-refl X))
           (canonical-map ι ρ str₁ str₂ (homomorphic-equivalence-gives-structural-equality h))
           h

    ‡ : (p : str₁ ＝ str₂)
      → homomorphic-equivalence-gives-structural-equality (canonical-map ι ρ str₁ str₂ p) ＝ p
    ‡ p = distributive-lattice-structure-is-set
           X
           pe
           (homomorphic-equivalence-gives-structural-equality (canonical-map ι ρ str₁ str₂ p))
           p

\end{code}

We abbreviate this proof by `snsᵈ`.

\begin{code}

private
 snsᵈ = distributive-lattice-sns-data

\end{code}

The notion of isomorphism given by `snsᵈ` is trivially equivalent to the type
`Isomorphismᵈ₀`.

\begin{code}

 open HomomorphicEquivalences

 isomorphism₀-equivalent-to-sns-isomorphism
  : (K L : Distributive-Lattice₀ 𝓤)
  → let
     Kᵣ = to-distributive-lattice 𝓤 K
     Lᵣ = to-distributive-lattice 𝓤 L
    in
     (K ≃[ snsᵈ ] L) ≃ (Isomorphism₀ Kᵣ Lᵣ)
 isomorphism₀-equivalent-to-sns-isomorphism {𝓤} K L = 𝔰 , qinvs-are-equivs 𝔰 †
  where
   Kᵣ = to-distributive-lattice 𝓤 K
   Lᵣ = to-distributive-lattice 𝓤 L

   𝔰 : K ≃[ snsᵈ ] L → Isomorphism₀ Kᵣ Lᵣ
   𝔰 (f , (e , φ)) = (f , e) , φ

   𝔯 : Isomorphism₀ Kᵣ Lᵣ → K ≃[ snsᵈ ] L
   𝔯 ((f , e) , φ) = f , (e , φ)

   † : qinv 𝔰
   † = 𝔯 , (λ _ → refl) , (λ _ → refl)

\end{code}

From this, we get the characterization of equality for distributive lattices.

\begin{code}

characterization-of-distributive-lattice₀-＝ : (K L : Distributive-Lattice₀ 𝓤)
                                             → (K ＝ L) ≃ (K ≃[ snsᵈ ] L)
characterization-of-distributive-lattice₀-＝ {𝓤} K L =
 characterization-of-＝ (ua 𝓤) snsᵈ K L

characterization-of-distributive-lattice-＝ : (K L : DistributiveLattice 𝓤)
                                            → (K ＝ L) ≃ (K ≅d≅ L)
characterization-of-distributive-lattice-＝ {𝓤} K L =
 let
  K₀ = to-distributive-lattice₀ 𝓤 K
  L₀ = to-distributive-lattice₀ 𝓤 L

  Ⅱ = characterization-of-distributive-lattice₀-＝ K₀ L₀
  Ⅲ = isomorphism₀-equivalent-to-sns-isomorphism K₀ L₀
  Ⅳ = isomorphismᵈᵣ-is-equivalent-to-isomorphism₀ K L

  𝔰 : K ＝ L → K₀ ＝ L₀
  𝔰 = λ { refl → refl }

  𝔯 : K₀ ＝ L₀ → K ＝ L
  𝔯 = λ { refl → refl }

  † : (𝔯 ∘ 𝔰) ∼ id
  † = (λ { refl → refl })

  ‡ : (𝔰 ∘ 𝔯) ∼ id
  ‡ = (λ { refl → refl })

  goal : (K ＝ L) ≃ (K₀ ＝ L₀)
  goal = 𝔰 , qinvs-are-equivs 𝔰 (𝔯 , † , ‡)
 in
  (K ＝ L)           ≃⟨ goal ⟩
  (K₀ ＝ L₀)         ≃⟨ Ⅱ ⟩
  (K₀ ≃[ snsᵈ ] L₀)  ≃⟨ Ⅲ ⟩
  (Isomorphism₀ K L) ≃⟨ Ⅳ ⟩
  (K ≅d≅ L)          ■

\end{code}

Finally, we record the fact that isomorphic distributive lattices are _equal_.

\begin{code}

isomorphic-distributive-lattices-are-equal
 : (K L : DistributiveLattice 𝓤)
 → K ≅d≅ L
 → K ＝ L
isomorphic-distributive-lattices-are-equal K L =
 ⌜ ≃-sym (characterization-of-distributive-lattice-＝ K L) ⌝

\end{code}
