---
title:       The spectral Scott locale of a Scott domain
author:      Ayberk Tosun
start-date:  2023-10-25
---

Ayberk Tosun.

Started on: 2023-10-25.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse
open import UF.Size
open import UF.Classifiers
open import UF.Univalence
open import UF.Equiv hiding (_■)
open import UF.Embeddings

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed                      pt fe 𝓤
 renaming (⊥ to ⊥d)
open import DomainTheory.Basics.WayBelow                     pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases            pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity       pt fe 𝓤
open import DomainTheory.BasesAndContinuity.CompactBasis     pt fe 𝓤
open import Locales.ScottLocale.Definition                   pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import DomainTheory.Topology.ScottTopology              pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties    pt fe 𝓤
open import Locales.Frame                                    pt fe
 hiding (∅)
open import Locales.Compactness                              pt fe
 hiding (is-compact)

open import Locales.SmallBasis pt fe sr

open Universal fe
open Implication fe
open Existential pt
open Disjunction pt
open Conjunction
open PowersetOperations

open Locale

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

_⊆⊆_ : {𝓤 𝓥 : Universe} {X : 𝓤  ̇} → List X → 𝓟 {𝓥} {𝓤} X → 𝓤 ⊔ 𝓥  ̇
_⊆⊆_ {_} {_} {X} xs U = (x : X) → member x xs → x ∈ U

\end{code}

\begin{code}

module SpectralScottLocaleConstruction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (hscb : has-specified-small-compact-basis 𝓓)
        (pe   : propext 𝓤) where

 open ScottLocaleConstruction 𝓓 hscb pe

\end{code}

We denote by `𝒮𝓓` the Scott locale of the dcpo `𝓓`.

\begin{code}

 𝒮𝓓 : Locale (𝓤 ⁺) 𝓤 𝓤
 𝒮𝓓 = ScottLocale

\end{code}

We denote by `(B, β)` the algebraic basis of the pointed dcpo 𝓓.

\begin{code}

 B : 𝓤  ̇
 B = index-of-compact-basis 𝓓 hscb

 β : B → ⟨ 𝓓 ⟩∙
 β i = family-of-basic-opens 𝓓 hscb i

 open structurally-algebraic

 scb : is-small-compact-basis 𝓓 (family-of-basic-opens 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

 open is-small-compact-basis scb


 ϟ : (b : B) → is-compact 𝓓 (β b)
 ϟ = basis-is-compact

\end{code}

We define some nice notation for the prop-valued equality of the dcpo `𝓓`.

\begin{code}

 _＝ₚ_ : ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
 x ＝ₚ y = (x ＝ y) , sethood 𝓓

\end{code}

We now construct the basis for this locale.

\begin{code}

 open DefnOfScottTopology 𝓓 𝓤
 open Properties 𝓓

 open binary-unions-of-subsets pt

 from-list₀ : List B → 𝓟 {𝓤} {𝓤 ⁺} ⟨ 𝓓 ⟩∙
 from-list₀ = foldr _∪_ ∅ ∘ map (principal-filter 𝓓 ∘ β)

 from-list₀-is-upwards-closed : (ks : List B)
                              → is-upwards-closed (from-list₀ ks) holds
 from-list₀-is-upwards-closed []       x y () q
 from-list₀-is-upwards-closed (b ∷ bs) x y p  q =
  ∥∥-rec (holds-is-prop (y ∈ₚ from-list₀ (b ∷ bs))) † p
   where
    † : (β b ⊑⟨ 𝓓 ⟩ x) + x ∈ from-list₀ bs → from-list₀ (b ∷ bs) y holds
    † (inl r) = ∣ inl (principal-filter-is-upwards-closed (β b) x y r q) ∣
    † (inr r) = ∣ inr (from-list₀-is-upwards-closed bs x y r q) ∣

 from-list₀-is-inaccessible-by-directed-joins : (ks : List B)
                                             → is-inaccessible-by-directed-joins
                                                (from-list₀ ks)
                                                 holds
 from-list₀-is-inaccessible-by-directed-joins []       (S , δ) ()
 from-list₀-is-inaccessible-by-directed-joins (k ∷ ks) (S , δ) p =
  ∥∥-rec ∃-is-prop † p
   where
    σ : is-scott-open (↑[ 𝓓 ] β k) holds
    σ = compact-implies-principal-filter-is-scott-open (β k) (basis-is-compact k)

    υ : is-upwards-closed (↑[ 𝓓 ] (β k)) holds
    υ = 𝒪ₛᴿ.pred-is-upwards-closed (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    ι : is-inaccessible-by-directed-joins (↑[ 𝓓 ] β k) holds
    ι = 𝒪ₛᴿ.pred-is-inaccessible-by-dir-joins (to-𝒪ₛᴿ (↑[ 𝓓 ] (β k) , σ))

    † : (β k ⊑⟨ 𝓓 ⟩ (⋁ (S , δ))) + (⋁ (S , δ)) ∈ from-list₀ ks
      → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
    † (inl q) = let
                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ ↑[ 𝓓 ] β k
                   → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
                 ‡ = λ { (i , p) → ∣ i , ∣ inl p ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ (ι (S , δ) q)
    † (inr q) = let
                 IH : ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ ks
                 IH = from-list₀-is-inaccessible-by-directed-joins ks (S , δ) q

                 ‡ : Σ i ꞉ index S , (S [ i ]) ∈ from-list₀ ks
                   → ∃ i ꞉ index S , (S [ i ]) ∈ from-list₀ (k ∷ ks)
                 ‡ = λ { (i , r) → ∣ i , ∣ inr r ∣ ∣ }
                in
                 ∥∥-rec ∃-is-prop ‡ IH

 from-list₀-gives-scott-opens : (ks : List B)
                              → is-scott-open (from-list₀ ks) holds
 from-list₀-gives-scott-opens ks = ⦅𝟏⦆ , ⦅𝟐⦆
  where
   ⦅𝟏⦆ = from-list₀-is-upwards-closed ks
   ⦅𝟐⦆ = from-list₀-is-inaccessible-by-directed-joins ks

 from-list₀-lemma : (x : ⟨ 𝓓 ⟩∙) (ks : List B)
                  → x ∈ from-list₀ ks → ∃ k ꞉ B , member k ks × β k ⊑⟨ 𝓓 ⟩ x
 from-list₀-lemma x []       = λ ()
 from-list₀-lemma x (k ∷ ks) p = ∥∥-rec ∃-is-prop † p
  where
   † : principal-filter 𝓓 (β k) x holds + x ∈ from-list₀ ks
     → ∃ k₀ ꞉ B , member k₀ (k ∷ ks) × underlying-order 𝓓 (β k₀) x
   † (inl q) = ∣ k , (in-head , q) ∣
   † (inr q) = ∥∥-rec
                ∃-is-prop
                (λ { (k₀ , r , s) → ∣ k₀ , in-tail r , s ∣ })
                (from-list₀-lemma x ks q)

\end{code}

\begin{code}

 γ : List B → ⟨ 𝒪 𝒮𝓓 ⟩
 γ ks = from-list₀ ks , from-list₀-gives-scott-opens ks

 γ₁ : List B → ⟨ 𝒪 𝒮𝓓 ⟩
 γ₁ []       = 𝟎[ 𝒪 𝒮𝓓 ]
 γ₁ (k ∷ ks) = ↑ˢ[ (β k , ϟ k) ] ∨[ 𝒪 𝒮𝓓 ] γ₁ ks

\end{code}

\begin{code}

 -- γ-idempotence-lemma : (𝔘 : ⟨ 𝒪 𝒮𝓓 ⟩) (bs : List B)
 --                     → (γ bs ≤[ poset-of (𝒪 𝒮𝓓) ] 𝔘) holds
 --                     → ∃ b ꞉ B , member b bs × ({!!} holds)
 -- γ-idempotence-lemma 𝔘 [] p = {!!}
 -- γ-idempotence-lemma 𝔘 (x ∷ bs) p = {!!}

 principal-filter-is-compact : (b : B)
                             → is-compact-open 𝒮𝓓 ↑ˢ[ (β b , ϟ b) ] holds
 principal-filter-is-compact b S δ p = ∥∥-rec ∃-is-prop † q
  where
   p′ : (↑ˢ[ (β b , ϟ b) ] ⊆ₖ (⋁[ 𝒪 𝒮𝓓 ] S)) holds
   p′ i r = p i r

   q : (β b ∈ₛ (⋁[ 𝒪 𝒮𝓓 ] S)) holds
   q = p b (reflexivity 𝓓 (β b))

   † : Σ k ꞉ index S , (β b ∈ₛ (S [ k ])) holds
     → ∃ i ꞉ index S , ((↑ˢ[ β b , ϟ b ]) ≤[ poset-of (𝒪 𝒮𝓓) ] (S [ i ])) holds
   † (k , φ) = ∣ k , ‡ ∣
    where
     Sₖᴿ : 𝒪ₛᴿ
     Sₖᴿ = to-𝒪ₛᴿ (S [ k ])

     ‡ : (↑ˢ[ β b , ϟ b ] ≤[ poset-of (𝒪 𝒮𝓓) ] (S [ k ])) holds
     ‡ d r = 𝒪ₛᴿ.pred-is-upwards-closed Sₖᴿ (β b) (β d) φ r

\end{code}

\begin{code}

 γ₁-gives-compact-opens : (b⃗ : List B) → is-compact-open 𝒮𝓓 (γ₁ b⃗) holds
 γ₁-gives-compact-opens []       = 𝟎-is-compact 𝒮𝓓
 γ₁-gives-compact-opens (b ∷ bs) = †
  where
   𝔘ᶜ : ⟨ 𝒪 𝒮𝓓 ⟩
   𝔘ᶜ = ↑[ 𝓓 ] (β b)
      , compact-implies-principal-filter-is-scott-open (β b) (basis-is-compact b)

   b-compact : is-compact-open 𝒮𝓓 𝔘ᶜ holds
   b-compact = principal-filter-is-compact b

   𝔘ᶜᵣ : 𝒪ₛᴿ
   𝔘ᶜᵣ = to-𝒪ₛᴿ 𝔘ᶜ

   IH : is-compact-open 𝒮𝓓 (γ₁ bs) holds
   IH = γ₁-gives-compact-opens bs

   † : is-compact-open 𝒮𝓓 (γ₁ (b ∷ bs)) holds
   † = compact-opens-are-closed-under-∨ 𝒮𝓓 𝔘ᶜ (γ₁ bs) b-compact IH

\end{code}

\begin{code}

 basis-for-𝒮𝓓 : Fam 𝓤 ⟨ 𝒪 𝒮𝓓 ⟩
 basis-for-𝒮𝓓 = List B , γ

 open PropertiesAlgebraic 𝓓 𝕒

 𝒮𝓓-dir-basis-forᴰ : directed-basis-forᴰ (𝒪 𝒮𝓓) basis-for-𝒮𝓓
 𝒮𝓓-dir-basis-forᴰ U@(_ , so) = (D , δ) , † , {!!}
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 𝒮𝓓) ] y)

    Uᴿ : 𝒪ₛᴿ
    Uᴿ = to-𝒪ₛᴿ U

    open 𝒪ₛᴿ Uᴿ renaming (pred to 𝔘)

    D : 𝓤  ̇
    D = (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘))

    δ : (Σ b⃗ ꞉ (List B) , ((b : B) → member b b⃗ → (β b) ∈ 𝔘)) → List B
    δ = pr₁

    †₁ : (U is-an-upper-bound-of ⁅ γ d ∣ d ε (D , δ) ⁆) holds
    †₁ (b⃗ , r) b p =
     ∥∥-rec (holds-is-prop (β b ∈ₚ 𝔘)) ‡₁ (from-list₀-lemma (β b) b⃗ p)
      where
       ‡₁ : Σ k ꞉ B , member k b⃗ × β k ⊑⟨ 𝓓 ⟩ β b → β b ∈ 𝔘
       ‡₁ (k , q , φ) = pred-is-upwards-closed (β k) (β b) (r k q) φ

    †₂ : ((U′ , _) : upper-bound ⁅ γ d ∣ d ε (D , δ) ⁆)
       → (U ≤[ poset-of (𝒪 𝒮𝓓) ] U′) holds
    †₂ (U′ , p) = {!!}

    † : (U is-lub-of ⁅ γ d ∣ d ε (D , δ) ⁆) holds
    † = †₁ , †₂

 fun-fact : (ua : is-univalent 𝓤) (fe : funext 𝓤 (𝓤 ⁺))
          → (X : 𝓤  ̇)
          → Subtypes' 𝓤 X ≃ (X → Ω 𝓤)
 fun-fact ua fe X = Ω-is-subtype-classifier' {𝓤 = 𝓤} {𝓥 = 𝓤} ua fe X

 σᴰ : spectralᴰ 𝒮𝓓
 σᴰ = basis-for-𝒮𝓓 , 𝒮𝓓-dir-basis-forᴰ , ({!!} , (τ , μ))
  where
   τ : contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   τ = {!!}

   μ : closed-under-binary-meets (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   μ = {!!}

\end{code}
