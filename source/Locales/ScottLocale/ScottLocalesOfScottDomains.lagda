---
title:          The spectral Scott locale of a Scott domain
author:         Ayberk Tosun
date-started:   2023-10-25
date-completed: 2023-11-26
dates-updated:  [2024-03-16]
---

In this module, we prove that the Scott locale of any Scott domain is a spectral
locale (provided that the domain in consideration is large and locally small and
satisfies a certain decidability condition).

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Univalence

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity       pt fe 𝓤
open import DomainTheory.BasesAndContinuity.ScottDomain      pt fe 𝓤
open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙) hiding   (is-directed)
open import DomainTheory.Basics.WayBelow                     pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Compactness.Definition                              pt fe
 hiding (is-compact)
open import Locales.Frame                                    pt fe
 hiding (∅)
open import Locales.ScottLocale.Definition                   pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale               pt fe

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

The module:

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤

\end{code}

contains a proof that the Scott locale of any algebraic dcpo is a locale.

In this module, we extend this proof by showing that the Scott locale is
spectral.

\section{Preliminaries}

The following function expresses a list being contained in a given subset.

\begin{code}

_⊆⊆_ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } → List X → 𝓟 {𝓥} {𝓤} X → 𝓤 ⊔ 𝓥 ̇
_⊆⊆_ {_} {_} {X} xs U = (x : X) → member x xs → x ∈ U

\end{code}

For the proof of spectrality, we will also need the following decidability
assumption for upper boundedness of compact elements.

\begin{code}

decidability-condition : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → 𝓤 ⁺ ̇
decidability-condition 𝓓 = (c d : ⟨ 𝓓 ⟩∙) →
                            is-compact 𝓓 c → is-compact 𝓓 d →
                             is-decidable (bounded-above 𝓓 c d holds)

\end{code}

This condition is trivially satisfied if the dcpo in consideration is complete
(or equivalently, it has all binary joins) because the upper bound mentioned
here will always exist. In many cases, the dcpos we are interested in turn out
to be such complete lattices.

\section{The proof}

As mentioned previously, we assume a couple of things.

  1. The dcpo `𝓓` in consideration is large and locally small.
  2. It is pointed.
  3. It has a specified small compact basis.
  4. It satisfies the aforementioned decidability condition.
  5. It is bounded complete (which means it is a Scott domain when combined
     with the algebraicity condition).

\begin{code}

open DefinitionOfBoundedCompleteness

module SpectralScottLocaleConstruction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hl   : has-least (underlying-order 𝓓))
        (hscb : has-specified-small-compact-basis 𝓓)
        (dc   : decidability-condition 𝓓)
        (bc   : bounded-complete 𝓓 holds)
        (pe   : propext 𝓤) where

 open ScottLocaleConstruction 𝓓 hscb pe

\end{code}

We denote by `Σ𝓓` the large and locally small Scott locale of the dcpo `𝓓`.

\begin{code}

 open ScottLocaleProperties 𝓓 hl hscb pe

 Σ[𝓓] : Locale (𝓤 ⁺) 𝓤 𝓤
 Σ[𝓓] = Σ⦅𝓓⦆

\end{code}

We denote by `(B, β)` the algebraic basis of the pointed dcpo 𝓓 in consideration.

\begin{code}

 B : 𝓤 ̇
 B = index-of-compact-basis 𝓓 hscb

 β : B → ⟨ 𝓓 ⟩∙
 β i = family-of-compact-elements 𝓓 hscb i

 open structurally-algebraic

 scb : is-small-compact-basis 𝓓 (family-of-compact-elements 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb

 ϟ : (b : B) → is-compact 𝓓 (β b)
 ϟ = basis-is-compact

\end{code}

We define some nice notation for the prop-valued equality of the dcpo `𝓓`.

\begin{code}

 open DefnOfScottTopology 𝓓 𝓤
 open BottomLemma 𝓓 𝕒 hl
 open Properties 𝓓
 open binary-unions-of-subsets pt

\end{code}

We also define some nice notation for the open given by a basis index.

\begin{code}

 ↑ᵏ[_] : B →  ⟨ 𝒪 Σ[𝓓] ⟩
 ↑ᵏ[ i ] = ↑ˢ[ β i , ϟ i ]

\end{code}

We now proceed to construct the intensional basis for the Scott locale.

The basis is the family `(List B , 𝜸₀)`, where `𝜸₀` is the following function:

\begin{code}

 𝜸₀ : List B → 𝓟 {𝓤} ⟨ 𝓓 ⟩∙
 𝜸₀ = foldr _∪_ ∅ ∘ map (principal-filter 𝓓 ∘ β)

\end{code}

For the reader who might be unfamiliar with it, `foldr` is a function on lists
that takes a binary function `f : X → Y → Y` and an element `u : Y`, and "folds"
a given a list `x[0], …, x[n-1]` into

```
f(x[0], f(x[1], … f(x[n-1], u)))
```

\begin{code}

 𝜸₀-is-upwards-closed : (ks : List B)
                      → is-upwards-closed (𝜸₀ ks) holds
 𝜸₀-is-upwards-closed []       x y () q
 𝜸₀-is-upwards-closed (b ∷ bs) x y p  q =
  ∥∥-rec (holds-is-prop (y ∈ₚ 𝜸₀ (b ∷ bs))) † p
   where
    † : (β b ⊑⟨ 𝓓 ⟩ x) + x ∈ 𝜸₀ bs → 𝜸₀ (b ∷ bs) y holds
    † (inl r) = ∣ inl (principal-filter-is-upwards-closed (β b) x y r q) ∣
    † (inr r) = ∣ inr (𝜸₀-is-upwards-closed bs x y r q) ∣

 𝜸₀-is-inaccessible-by-directed-joins :(ks : List B)
                                      → is-inaccessible-by-directed-joins (𝜸₀ ks)
                                         holds
 𝜸₀-is-inaccessible-by-directed-joins []       (S , δ) ()
 𝜸₀-is-inaccessible-by-directed-joins (k ∷ ks) (S , δ) p =
  ∥∥-rec ∃-is-prop † p
   where
    σ : is-scott-open (↑[ 𝓓 ] β k) holds
    σ = compact-implies-principal-filter-is-scott-open (β k) (basis-is-compact k)

    υ : is-upwards-closed (↑[ 𝓓 ] (β k)) holds
    υ = 𝒪ₛᴿ.pred-is-upwards-closed (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    ι : is-inaccessible-by-directed-joins (↑[ 𝓓 ] β k) holds
    ι = 𝒪ₛᴿ.pred-is-inaccessible-by-dir-joins (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    † : (β k ⊑⟨ 𝓓 ⟩ (⋁ (S , δ))) + (⋁ (S , δ)) ∈ 𝜸₀ ks
      → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
    † (inl q) = let
                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ ↑[ 𝓓 ] β k
                   → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
                 ‡ = λ { (i , p) → ∣ i , ∣ inl p ∣ ∣}
                in
                 ∥∥-rec ∃-is-prop ‡ (ι (S , δ) q)
    † (inr q) = let
                 IH : ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ ks
                 IH = 𝜸₀-is-inaccessible-by-directed-joins ks (S , δ) q

                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ ks
                   → ∃ i ꞉ index S , (S [ i ]) ∈ 𝜸₀ (k ∷ ks)
                 ‡ = λ { (i , r) → ∣ i , ∣ inr r ∣ ∣}
                in
                 ∥∥-rec ∃-is-prop ‡ IH

 𝜸₀-gives-scott-opens : (ks : List B) → is-scott-open (𝜸₀ ks) holds
 𝜸₀-gives-scott-opens ks = ⦅𝟏⦆ , ⦅𝟐⦆
  where
   ⦅𝟏⦆ = 𝜸₀-is-upwards-closed ks
   ⦅𝟐⦆ = 𝜸₀-is-inaccessible-by-directed-joins ks

 𝜸₀-lemma : (x : ⟨ 𝓓 ⟩∙) (ks : List B)
          → x ∈ 𝜸₀ ks → ∃ k ꞉ B , member k ks × β k ⊑⟨ 𝓓 ⟩ x
 𝜸₀-lemma x []       = λ ()
 𝜸₀-lemma x (k ∷ ks) p = ∥∥-rec ∃-is-prop † p
  where
   † : principal-filter 𝓓 (β k) x holds + x ∈ 𝜸₀ ks
     → ∃ k₀ ꞉ B , member k₀ (k ∷ ks) × underlying-order 𝓓 (β k₀) x
   † (inl q) = ∣ k , (in-head , q) ∣
   † (inr q) = ∥∥-rec
                ∃-is-prop
                (λ { (k₀ , r , s) → ∣ k₀ , in-tail r , s ∣})
                (𝜸₀-lemma x ks q)

 𝜸 : List B → ⟨ 𝒪 Σ[𝓓] ⟩
 𝜸 ks = 𝜸₀ ks , 𝜸₀-gives-scott-opens ks

 𝜸₁ : List B → ⟨ 𝒪 Σ[𝓓] ⟩
 𝜸₁ []       = 𝟎[ 𝒪 Σ[𝓓] ]
 𝜸₁ (k ∷ ks) = ↑ᵏ[ k ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks

\end{code}

The function `𝜸₁` is equal to `𝜸`.

\begin{code}

 𝜸-below-𝜸₁ : (bs : List B) → (𝜸 bs ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ bs) holds
 𝜸-below-𝜸₁ []       _ ()
 𝜸-below-𝜸₁ (i ∷ is) j p =
  ∥∥-rec (holds-is-prop (𝜸₁ (i ∷ is) .pr₁ (β j))) † p
   where
    IH : (𝜸 is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ is) holds
    IH = 𝜸-below-𝜸₁ is

    † : (β i ⊑⟨ 𝓓 ⟩ β j) + (β j ∈ₛ 𝜸 is) holds
      → ((β j) ∈ₛ 𝜸₁ (i ∷ is)) holds
    † (inl q) = ∣ inl ⋆ , q      ∣
    † (inr q) = ∣ inr ⋆ , IH j q ∣

 𝜸₁-below-𝜸 : (bs : List B) → (𝜸₁ bs ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸 bs) holds
 𝜸₁-below-𝜸 []       j p = 𝟎-is-bottom (𝒪 Σ[𝓓]) (𝜸 []) j p
 𝜸₁-below-𝜸 (i ∷ is) j p = ∥∥-rec (holds-is-prop (β j ∈ₛ 𝜸 (i ∷ is))) † p
  where
   IH : (𝜸₁ is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸 is) holds
   IH = 𝜸₁-below-𝜸 is

   † : (Σ k ꞉ 𝟚 𝓤 ,
         (β j ∈ₛ (⁅ ↑ᵏ[ i ] , 𝜸₁ is ⁆ [ k ])) holds)
     → (β j ∈ₛ 𝜸 (i ∷ is)) holds
   † (inl ⋆ , r) = ∣ inl r        ∣
   † (inr ⋆ , r) = ∣ inr (IH j r) ∣

 𝜸-equal-to-𝜸₁ : (bs : List B) → 𝜸 bs ＝ 𝜸₁ bs
 𝜸-equal-to-𝜸₁ bs =
  ≤-is-antisymmetric (poset-of (𝒪 Σ[𝓓])) (𝜸-below-𝜸₁ bs) (𝜸₁-below-𝜸 bs)

\end{code}

TODO: get rid of `𝜸` altogether and use `𝜸₁` as the basis function

\begin{code}

 𝜸-lemma₁ : (is js : List B) → (𝜸 is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸 (is ++ js)) holds
 𝜸-lemma₁ []       js       = λ _ ()
 𝜸-lemma₁ (i ∷ is) []       = let
                               open PosetNotation (poset-of (𝒪 Σ[𝓓]))

                               † : (i ∷ is) ＝ (i ∷ is) ++ []
                               † = []-right-neutral (i ∷ is)

                               ‡ : (𝜸 (i ∷ is) ≤ 𝜸 (i ∷ is)) holds
                               ‡ = ≤-is-reflexive (poset-of (𝒪 Σ[𝓓])) (𝜸 (i ∷ is))
                              in
                               transport (λ - → (𝜸 (i ∷ is) ≤ 𝜸 -) holds) † ‡
 𝜸-lemma₁ (i ∷ is) (j ∷ js) x p = Ⅲ x (Ⅱ x (Ⅰ x p))
   where
    † : (𝜸₁ is ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸₁ (is ++ (j ∷ js))) holds
    † y q =
     𝜸-below-𝜸₁ (is ++ (j ∷ js)) y (𝜸-lemma₁ is (j ∷ js) y (𝜸₁-below-𝜸 is y q))

    Ⅰ = 𝜸-below-𝜸₁ (i ∷ is)
    Ⅱ = ∨[ 𝒪 Σ[𝓓] ]-right-monotone †
    Ⅲ = 𝜸₁-below-𝜸 (i ∷ (is ++ (j ∷ js)))

 𝜸-lemma₂ : (is js : List B) → (𝜸 js ≤[ poset-of (𝒪 Σ[𝓓]) ] 𝜸 (is ++ js)) holds
 𝜸-lemma₂    []        js = ≤-is-reflexive (poset-of (𝒪 Σ[𝓓])) (𝜸 js)
 𝜸-lemma₂ is@(i ∷ is′) js = λ x p → ∣_∣ (inr (𝜸-lemma₂ is′ js x p))

 𝜸-maps-∨-to-++ : (is js : List B) → 𝜸₁ (is ++ js) ＝ 𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js
 𝜸-maps-∨-to-++ []       js = 𝟎-right-unit-of-∨ (𝒪 Σ[𝓓]) (𝜸₁ js) ⁻¹
 𝜸-maps-∨-to-++ (i ∷ is) js =
  𝜸₁ ((i ∷ is) ++ js)                               ＝⟨refl⟩
  ↑ᵏ[ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ (is ++ js)                 ＝⟨ Ⅰ    ⟩
  ↑ᵏ[ i ] ∨[ 𝒪 Σ[𝓓] ] (𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)     ＝⟨ Ⅱ    ⟩
  (↑ᵏ[ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ is) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js     ＝⟨refl⟩
  𝜸₁ (i ∷ is) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js                     ∎
   where
    Ⅰ = ap (λ - → ↑ᵏ[ i ] ∨[ 𝒪 Σ[𝓓] ] -) (𝜸-maps-∨-to-++ is js)
    Ⅱ = ∨[ 𝒪 Σ[𝓓] ]-assoc ↑ᵏ[ i ] (𝜸₁ is) (𝜸₁ js) ⁻¹

\end{code}

The principal filter `↑(x)` on any `x : 𝓓` is a compact Scott open.

\begin{code}

 principal-filter-is-compact : (b : B)
                             → is-compact-open Σ[𝓓] ↑ᵏ[ b ] holds
 principal-filter-is-compact b = principal-filter-is-compact₀ (β b) (ϟ b)

\end{code}

For any `bs : List B`, the Scott open `𝜸₁(bs)` is compact.

\begin{code}

 𝜸₁-gives-compact-opens : (bs : List B) → is-compact-open Σ[𝓓] (𝜸₁ bs) holds
 𝜸₁-gives-compact-opens []       = 𝟎-is-compact Σ[𝓓]
 𝜸₁-gives-compact-opens (b ∷ bs) = †
  where
   𝔘ᶜ : ⟨ 𝒪 Σ[𝓓] ⟩
   𝔘ᶜ = ↑[ 𝓓 ] (β b)
      , compact-implies-principal-filter-is-scott-open (β b) (basis-is-compact b)

   𝔘ᶜᵣ : 𝒪ₛᴿ
   𝔘ᶜᵣ = to-𝒪ₛᴿ 𝔘ᶜ

   IH : is-compact-open Σ[𝓓] (𝜸₁ bs) holds
   IH = 𝜸₁-gives-compact-opens bs

   † : is-compact-open Σ[𝓓] (𝜸₁ (b ∷ bs)) holds
   † = compact-opens-are-closed-under-∨
        Σ[𝓓]
        𝔘ᶜ
        (𝜸₁ bs)
        (principal-filter-is-compact b)
        IH

 𝜸-gives-compact-opens : (bs : List B) → is-compact-open Σ[𝓓] (𝜸 bs) holds
 𝜸-gives-compact-opens bs =
  transport (λ - → is-compact-open Σ[𝓓] - holds) (𝜸-equal-to-𝜸₁ bs ⁻¹) †
   where
    † : is-compact-open Σ[𝓓] (𝜸₁ bs) holds
    † = 𝜸₁-gives-compact-opens bs

\end{code}

Given compact elements `c` and `d` of `𝓓`, if an element `s` is their sup,
then it is compact.

\begin{code}

 sup-is-compact : (c d s : ⟨ 𝓓 ⟩∙)
                → (κᶜ : is-compact 𝓓 c)
                → (κᵈ : is-compact 𝓓 d)
                → is-sup (underlying-order 𝓓) s (binary-family 𝓤 c d [_])
                → is-compact 𝓓 s
 sup-is-compact c d s κᶜ κᵈ (p , q) =
  binary-join-is-compact 𝓓 (p (inl ⋆)) (p (inr ⋆)) η κᶜ κᵈ
   where
    η : (d₁ : ⟨ 𝓓 ⟩∙) → c ⊑⟨ 𝓓 ⟩ d₁ → d ⊑⟨ 𝓓 ⟩ d₁ → s ⊑⟨ 𝓓 ⟩ d₁
    η d₁ r₁ r₂ = q d₁ λ { (inl ⋆) → r₁ ; (inr ⋆) → r₂}

 open DefnOfScottLocale 𝓓 𝓤 pe using (_⊆ₛ_)

\end{code}

\begin{code}

 principal-filter-is-antitone : (b c : ⟨ 𝓓 ⟩∙)
                              → b ⊑⟨ 𝓓 ⟩ c
                              → (κᵇ : is-compact 𝓓 b)
                              → (κᶜ : is-compact 𝓓 c)
                              → (↑ˢ[ c , κᶜ ] ≤[ poset-of (𝒪 Σ[𝓓]) ] ↑ˢ[ b , κᵇ ]) holds
 principal-filter-is-antitone b c p κᵇ κᶜ x =
  upward-closure ↑ˢ[ b , κᵇ ] c (β x) p

 principal-filter-reflects-joins
  : (c d s : ⟨ 𝓓 ⟩∙)
  → (κᶜ : is-compact 𝓓 c)
  → (κᵈ : is-compact 𝓓 d)
  → (σ : is-sup (underlying-order 𝓓) s (⁅ c , d ⁆ [_]))
  → let
     κˢ = sup-is-compact c d s κᶜ κᵈ σ
    in
     ↑ˢ[ s , κˢ ] ＝ ↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]
 principal-filter-reflects-joins c d s κᶜ κᵈ σ =
  ≤-is-antisymmetric (poset-of (𝒪 Σ[𝓓])) Ⅰ Ⅱ
   where
    open PosetReasoning (poset-of (𝒪 Σ[𝓓]))

    κₛ : is-compact 𝓓 s
    κₛ = sup-is-compact c d s κᶜ κᵈ σ

    † : (↑ˢ[ s , κₛ ] ⊆ₛ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ])) holds
    † x p = (c ⊑⟨ 𝓓 ⟩[ pr₁ σ (inl ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)
          , (d ⊑⟨ 𝓓 ⟩[ pr₁ σ (inr ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)

    ‡ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ⊆ₛ ↑ˢ[ s , κₛ ]) holds
    ‡ x (p , q) = pr₂ σ x λ { (inl ⋆) → p ; (inr ⋆) → q}

    Ⅰ : (↑ˢ[ s , κₛ ] ⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ])) holds
    Ⅰ = ⊆ₛ-implies-⊆ₖ ↑ˢ[ s , κₛ ] (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) †

    Ⅱ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ⊆ₖ ↑ˢ[ s , κₛ ]) holds
    Ⅱ = ⊆ₛ-implies-⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ d , κᵈ ]) ↑ˢ[ s , κₛ ] ‡

\end{code}

The following is the main lemma used when showing that the image of `𝜸` is
closed under binary meets.

\begin{code}

 𝜸-closure-under-∧₁ : (i : B) (is : List B)
                    → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ is
 𝜸-closure-under-∧₁ i []       = let
                                  † = 𝟎-right-annihilator-for-∧ (𝒪 Σ[𝓓]) ↑ᵏ[ i ]
                                 in ∣ [] , († ⁻¹) ∣
 𝜸-closure-under-∧₁ i (j ∷ js) = cases †₁ †₂ (dc (β i) (β j) (ϟ i) (ϟ j))
  where
   IH : ∃ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   IH = 𝜸-closure-under-∧₁ i js

   †₁ : (β i ↑[ 𝓓 ] β j) holds
      → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
   †₁ υ = ∥∥-rec ∃-is-prop ‡₁ ξ
    where
     open Joins (λ x y → x ⊑⟨ 𝓓 ⟩ₚ y)

     s : ⟨ 𝓓 ⟩∙
     s = pr₁ (bc ⁅ β i , β j ⁆ υ)

     φ : (s is-an-upper-bound-of ⁅ β i , β j ⁆) holds
     φ = pr₁ (pr₂ (bc ⁅ β i , β j ⁆ υ))

     ψ : is-lowerbound-of-upperbounds (underlying-order 𝓓) s (⁅ β i , β j ⁆ [_])
     ψ = pr₂ (pr₂ (bc ⁅ β i , β j ⁆ υ))

     κˢ : is-compact 𝓓 s
     κˢ = sup-is-compact (β i) (β j) s (ϟ i) (ϟ j) (φ , ψ)

     ξ : ∃ k ꞉ B , β k ＝ s
     ξ = small-compact-basis-contains-all-compact-elements 𝓓 β scb s κˢ

     ‡₁ : Σ k ꞉ B , β k ＝ s
        → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
     ‡₁ (k , p) = ∥∥-rec ∃-is-prop ※₁ IH
      where
       ※₁ : Σ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
          → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
       ※₁ (ks′ , q) = ∣ (k ∷ ks′) , ♣ ∣
        where
         μ : ↑ᵏ[ k ] ＝ ↑ˢ[ s , κˢ ]
         μ =
          to-subtype-＝ (holds-is-prop ∘ is-scott-open) (ap (λ - → ↑[ 𝓓 ] -) p)

         ζ : ↑ˢ[ s , κˢ ] ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]
         ζ = principal-filter-reflects-joins (β i) (β j) s (ϟ i) (ϟ j) (φ , ψ)

         ρ : ↑ᵏ[ k ] ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]
         ρ = ↑ᵏ[ k ] ＝⟨ μ ⟩ ↑ˢ[ s , κˢ ] ＝⟨ ζ ⟩ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ] ∎

         Ⅰ = ap (λ - → - ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′) ρ
         Ⅱ = ap (λ - → (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] -) q
         Ⅲ = binary-distributivity (𝒪 Σ[𝓓]) ↑ᵏ[ i ] ↑ᵏ[ j ] (𝜸₁ js) ⁻¹

         ♣ : 𝜸₁ (k ∷ ks′) ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
         ♣ =
           𝜸₁ (k ∷ ks′)
             ＝⟨refl⟩
           ↑ᵏ[ k ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′
             ＝⟨ Ⅰ ⟩
           (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks′
             ＝⟨ Ⅱ ⟩
           (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
             ＝⟨ Ⅲ ⟩
           ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] (↑ᵏ[ j ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
             ＝⟨refl⟩
           ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
             ∎

   †₂ : (β i ↑[ 𝓓 ] β j ⇒ ⊥) holds
      → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
   †₂ ν = ∥∥-rec ∃-is-prop ‡₂ IH
    where
     ‡₂ : Σ ks′ ꞉ List B , 𝜸₁ ks′ ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
        → ∃ ks ꞉ List B , 𝜸₁ ks ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
     ‡₂ (ks′ , p) = ∣ ks′ , ρ ∣
      where
       ρ : 𝜸₁ ks′ ＝  ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] (𝜸₁ (j ∷ js))
       ρ =
        𝜸₁ ks′
          ＝⟨ p ⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
          ＝⟨ Ⅰ ⟩
        𝟎[ 𝒪 Σ[𝓓] ] ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
          ＝⟨ Ⅱ ⟩
        (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] ↑ᵏ[ j ]) ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
          ＝⟨ Ⅲ ⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] (↑ᵏ[ j ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
          ＝⟨refl⟩
        ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ (j ∷ js)
          ∎
         where
          Ⅰ = 𝟎-right-unit-of-∨ (𝒪 Σ[𝓓]) (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ⁻¹
          Ⅱ = ap
               (λ - → - ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js))
               (not-bounded-lemma (β i) (β j) (ϟ i) (ϟ j) ν ⁻¹ )
          Ⅲ = binary-distributivity (𝒪 Σ[𝓓]) ↑ᵏ[ i ] ↑ᵏ[ j ] (𝜸₁ js) ⁻¹

 𝜸-closure-under-∧ : (is js : List B)
                   → ∃ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
 𝜸-closure-under-∧ []       js = ∣ [] , † ∣
  where
   † = 𝟎-left-annihilator-for-∧ (𝒪 Σ[𝓓]) (𝜸₁ js) ⁻¹
 𝜸-closure-under-∧ (i ∷ is) js = ∥∥-rec₂ ∃-is-prop † η₀ ρ₀
  where
   η₀ : ∃ ks₀ ꞉ List B , 𝜸₁ ks₀ ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   η₀ = 𝜸-closure-under-∧ is js

   ρ₀ : ∃ ks₁ ꞉ List B , 𝜸₁ ks₁ ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   ρ₀ = 𝜸-closure-under-∧₁ i js

   † : Σ ks₀ ꞉ List B , 𝜸₁ ks₀ ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     → Σ ks₁ ꞉ List B , 𝜸₁ ks₁ ＝ ↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     → ∃ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
   † (ks₀ , p₀) (ks₁ , p₁) = ∣ (ks₀ ++ ks₁) , ‡ ∣
    where
     ‡ : 𝜸₁ (ks₀ ++ ks₁) ＝ 𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
     ‡ =
      𝜸₁ (ks₀ ++ ks₁)
       ＝⟨ Ⅰ ⟩
      𝜸₁ ks₀ ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁
       ＝⟨ Ⅱ    ⟩
      (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁
       ＝⟨ Ⅲ    ⟩
      (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] (↑ᵏ[ i ] ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
       ＝⟨ Ⅳ    ⟩
      (𝜸₁ is ∨[ 𝒪 Σ[𝓓] ] ↑ᵏ[ i ]) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
       ＝⟨ Ⅴ    ⟩
      (↑ᵏ[ i ] ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
       ＝⟨refl⟩
      𝜸₁ (i ∷ is) ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js
       ∎
        where
         Ⅰ = 𝜸-maps-∨-to-++ ks₀ ks₁
         Ⅱ = ap (λ - → - ∨[ 𝒪 Σ[𝓓] ] 𝜸₁ ks₁) p₀
         Ⅲ = ap (λ - → (𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js) ∨[ 𝒪 Σ[𝓓] ] -) p₁
         Ⅳ = binary-distributivity-right (𝒪 Σ[𝓓]) ⁻¹
         Ⅴ = ap
              (λ - → - ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
              (∨[ 𝒪 Σ[𝓓] ]-is-commutative (𝜸₁ is) ↑ᵏ[ i ])

\end{code}

We are now ready to package up the basis. We call it `basis-for-Σ[𝓓]`.

\begin{code}

 basis-for-Σ[𝓓] : Fam 𝓤 ⟨ 𝒪 Σ[𝓓] ⟩
 basis-for-Σ[𝓓] = List B , 𝜸

 open PropertiesAlgebraic 𝓓 𝕒

\end{code}

This forms a directed basis.

\begin{code}

 Σ[𝓓]-dir-basis-forᴰ : directed-basis-forᴰ (𝒪 Σ[𝓓]) basis-for-Σ[𝓓]
 Σ[𝓓]-dir-basis-forᴰ U@(_ , so) = (D , δ) , † , 𝒹
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 Σ[𝓓]) ] y)

    Uᴿ : 𝒪ₛᴿ
    Uᴿ = to-𝒪ₛᴿ U

    open 𝒪ₛᴿ Uᴿ renaming (pred to 𝔘)

    D : 𝓤 ̇
    D = (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘))

    δ : (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘)) → List B
    δ = pr₁

    †₁ : (U is-an-upper-bound-of ⁅ 𝜸 d ∣ d ε (D , δ) ⁆) holds
    †₁ (b⃗ , r) b p =
     ∥∥-rec (holds-is-prop (β b ∈ₚ 𝔘)) ‡₁ (𝜸₀-lemma (β b) b⃗ p)
      where
       ‡₁ : Σ k ꞉ B , member k b⃗ × β k ⊑⟨ 𝓓 ⟩ β b → β b ∈ 𝔘
       ‡₁ (k , q , φ) = pred-is-upwards-closed (β k) (β b) (r k q) φ

    †₂ : ((U′ , _) : upper-bound ⁅ 𝜸 d ∣ d ε (D , δ) ⁆)
       → (U ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds
    †₂ (U′ , ψ) k p = ‡₂ k (reflexivity 𝓓 (β k))
     where
      r : ↑ˢ[ β k , ϟ k ] ＝ 𝜸 (k ∷ [])
      r =
       ↑ˢ[ β k , ϟ k ]                            ＝⟨ Ⅰ ⟩
       ↑ˢ[ β k , ϟ k ] ∨[ 𝒪 Σ[𝓓] ] 𝟎[ 𝒪 Σ[𝓓] ]    ＝⟨ Ⅱ ⟩
       𝜸 (k ∷ [])                                 ∎
        where
         Ⅰ = 𝟎-left-unit-of-∨ (𝒪 Σ[𝓓]) ↑ˢ[ β k , ϟ k ] ⁻¹
         Ⅱ = 𝜸-equal-to-𝜸₁ (k ∷ []) ⁻¹

      ‡₂ : (↑ˢ[ β k , ϟ k ] ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds
      ‡₂ = transport
            (λ - → (- ≤[ poset-of (𝒪 Σ[𝓓]) ] U′) holds)
            (r ⁻¹)
            (ψ ((k ∷ []) , λ { _ in-head → p}))

    † : (U is-lub-of ⁅ 𝜸 d ∣ d ε (D , δ) ⁆) holds
    † = †₁ , †₂

    𝒹↑ : ((is , _) (js , _) : D)
       → ∃ (ks , _) ꞉ D , (𝜸 is ⊆ₖ 𝜸 ks) holds × (𝜸 js ⊆ₖ 𝜸 ks) holds
    𝒹↑ (is , 𝕚) (js , 𝕛)= ∣ ((is ++ js) , ♣) , 𝜸-lemma₁ is js , 𝜸-lemma₂ is js ∣
     where
      ♣ : (b : B) → member b (is ++ js) → 𝔘 (β b) holds
      ♣ b q = cases (𝕚 b) (𝕛 b) (split-++-membership b is js q)

    𝒹 : is-directed (𝒪 Σ[𝓓]) ⁅ 𝜸 d ∣ d ε (D , δ) ⁆ holds
    𝒹 = ∣ [] , (λ _ ()) ∣ , 𝒹↑

\end{code}

The lemmas we have proved so far constitute the proof of spectrality when
combined as follows.

\begin{code}

 σᴰ : spectralᴰ Σ[𝓓]
 σᴰ = pr₁ Σ-assoc (𝒷 , 𝜸-gives-compact-opens , τ , μ)
  where
   𝒷 : directed-basisᴰ (𝒪 Σ[𝓓])
   𝒷 = basis-for-Σ[𝓓] , Σ[𝓓]-dir-basis-forᴰ

   τ : contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
   τ = ∥∥-rec
        (holds-is-prop (contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓]))
        †
        (compact-opens-are-basic Σ[𝓓] 𝒷 𝟏[ 𝒪 Σ[𝓓] ] ⊤-is-compact)
    where
     † : Σ is ꞉ List B , (𝜸 is) ＝ 𝟏[ 𝒪 Σ[𝓓] ]
       → contains-top (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
     † (is , p) =
      ∣ is , transport (_holds ∘ is-top (𝒪 Σ[𝓓])) (p ⁻¹) (𝟏-is-top (𝒪 Σ[𝓓])) ∣

   μ : closed-under-binary-meets (𝒪 Σ[𝓓]) basis-for-Σ[𝓓] holds
   μ is js = ∥∥-rec ∃-is-prop † (𝜸-closure-under-∧ is js)
    where
     open Meets (λ x y → x ≤[ poset-of (𝒪 Σ[𝓓]) ] y)

     † : (Σ ks ꞉ List B , 𝜸₁ ks ＝ 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js)
       → ∃ ks ꞉ List B , ((𝜸 ks) is-glb-of (𝜸 is , 𝜸 js)) holds
     † (ks , p) =
      ∣ ks , transport (λ - → (- is-glb-of (𝜸 is , 𝜸 js)) holds) q ‡ ∣
       where
        q : 𝜸 is ∧[ 𝒪 Σ[𝓓] ] 𝜸 js ＝ 𝜸 ks
        q = 𝜸  is ∧[ 𝒪 Σ[𝓓] ] 𝜸  js      ＝⟨ Ⅰ ⟩
            𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸  js      ＝⟨ Ⅱ ⟩
            𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] 𝜸₁ js      ＝⟨ Ⅲ ⟩
            𝜸₁ ks                        ＝⟨ Ⅳ ⟩
            𝜸 ks                         ∎
             where
              Ⅰ = ap (λ - → -     ∧[ 𝒪 Σ[𝓓] ] 𝜸 js) (𝜸-equal-to-𝜸₁ is)
              Ⅱ = ap (λ - → 𝜸₁ is ∧[ 𝒪 Σ[𝓓] ] -   ) (𝜸-equal-to-𝜸₁ js)
              Ⅲ = p ⁻¹
              Ⅳ = 𝜸-equal-to-𝜸₁ ks ⁻¹

        ‡ : ((𝜸 is ∧[ 𝒪 Σ[𝓓] ] 𝜸 js) is-glb-of (𝜸 is , 𝜸 js)) holds
        ‡ = (∧[ 𝒪 Σ[𝓓] ]-lower₁ (𝜸 is) (𝜸 js) , ∧[ 𝒪 Σ[𝓓] ]-lower₂ (𝜸 is) (𝜸 js))
          , λ { (l , φ , ψ) → ∧[ 𝒪 Σ[𝓓] ]-greatest (𝜸 is) (𝜸 js) l φ ψ}

\end{code}

In the module `SpectralScottLocaleConstruction` above, we worked with a
specified basis for convenience. Because the type of bases for algebraic dcpos
has split support, we can carry out the same construction with an unspecified
basis. The following module is a wrapper around the previous
`SpectralScottLocaleConstruction` module in which the spectrality proof is
constructed with only the assumption of an unspecified basis.

\begin{code}

open DefinitionOfScottDomain

module SpectralScottLocaleConstruction₂
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (ua   : Univalence)
        (hl   : has-least (underlying-order 𝓓))
        (sd   : is-scott-domain 𝓓 holds)
        (dc   : decidability-condition 𝓓)
        (pe   : propext 𝓤) where

 𝒷₀ : has-unspecified-small-compact-basis 𝓓
 𝒷₀ = pr₁ sd

 bc : bounded-complete 𝓓 holds
 bc = pr₂ sd

 hscb : has-specified-small-compact-basis 𝓓
 hscb = specified-small-compact-basis-has-split-support ua sr 𝓓 𝒷₀

 𝕒 : structurally-algebraic 𝓓
 𝕒 = structurally-algebraic-if-specified-small-compact-basis 𝓓 hscb

 pe′ : propext 𝓤
 pe′ = univalence-gives-propext (ua 𝓤)

 open SpectralScottLocaleConstruction 𝓓 hl hscb dc bc pe

 σ⦅𝓓⦆ : Locale (𝓤 ⁺) 𝓤 𝓤
 σ⦅𝓓⦆ = Σ[𝓓]

 scott-locale-spectralᴰ : spectralᴰ Σ[𝓓]
 scott-locale-spectralᴰ = σᴰ

 scott-locale-is-spectral : is-spectral Σ[𝓓] holds
 scott-locale-is-spectral = spectralᴰ-gives-spectrality Σ[𝓓] σᴰ

 scott-locale-has-small-𝒦 : has-small-𝒦 Σ[𝓓]
 scott-locale-has-small-𝒦 = spectralᴰ-implies-small-𝒦 Σ[𝓓] σᴰ

 scott-locale-has-spectral-basis : is-spectral-with-small-basis ua Σ[𝓓] holds
 scott-locale-has-spectral-basis =
  scott-locale-is-spectral , scott-locale-has-small-𝒦

\end{code}
