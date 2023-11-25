---
title:       The spectral Scott locale of a Scott domain
author:      Ayberk Tosun
start-date:  2023-10-25
---

Ayberk Tosun.

Started on: 2023-10-25.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
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
open import UF.EquivalenceExamples
open import MLTT.Negation

module Locales.ScottLocale.ScottLocalesOfScottDomains
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤  : Universe) where

open import DomainTheory.Basics.Dcpo                         pt fe 𝓤
 renaming (⟨_⟩ to ⟨_⟩∙)
 hiding   (is-directed)
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

open AllCombinators pt fe

open Locale

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

_⊆⊆_ : {𝓤 𝓥 : Universe} {X : 𝓤  ̇} → List X → 𝓟 {𝓥} {𝓤} X → 𝓤 ⊔ 𝓥  ̇
_⊆⊆_ {_} {_} {X} xs U = (x : X) → member x xs → x ∈ U

\end{code}

We define the following predicate that expresses what it means for two elements
of a DCPO `𝓓` to be “bounded above”.

\begin{code}

bounded-above : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → ⟨ 𝓓 ⟩∙ → ⟨ 𝓓 ⟩∙ → Ω (𝓤 ⁺)
bounded-above 𝓓 x y = ∥ upper-bound₂ (x , y) ∥Ω
 where
  open Joins (λ a b → a ⊑⟨ 𝓓 ⟩ₚ b)

infix 30 bounded-above

syntax bounded-above 𝓓 x y = x ↑[ 𝓓 ] y

\end{code}

For the construction, we will assume the following.

\begin{code}

decidability-condition : (𝓓 : DCPO {𝓤 ⁺} {𝓤}) → 𝓤 ⁺  ̇
decidability-condition 𝓓 =
 (x y : ⟨ 𝓓 ⟩∙) → is-decidable (bounded-above 𝓓 x y holds)

\end{code}

\begin{code}

open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤
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

 γ-below-γ₁ : (bs : List B) → (γ bs ≤[ poset-of (𝒪 𝒮𝓓) ] γ₁ bs) holds
 γ-below-γ₁ []       _ ()
 γ-below-γ₁ (i ∷ is) j p =
  ∥∥-rec (holds-is-prop (γ₁ (i ∷ is) .pr₁ (β j))) † p
   where
    IH : (γ is ≤[ poset-of (𝒪 𝒮𝓓) ] γ₁ is) holds
    IH = γ-below-γ₁ is

    † : (β i ⊑⟨ 𝓓 ⟩ β j) + (β j ∈ₛ γ is) holds
      → ((β j) ∈ₛ γ₁ (i ∷ is)) holds
    † (inl q) = ∣ inl ⋆ , q      ∣
    † (inr q) = ∣ inr ⋆ , IH j q ∣

 γ₁-below-γ : (bs : List B) → (γ₁ bs ≤[ poset-of (𝒪 𝒮𝓓) ] γ bs) holds
 γ₁-below-γ []       j p = 𝟎-is-bottom (𝒪 𝒮𝓓) (γ []) j p
 γ₁-below-γ (i ∷ is) j p = ∥∥-rec (holds-is-prop (β j ∈ₛ γ (i ∷ is))) † p
  where
   IH : (γ₁ is ≤[ poset-of (𝒪 𝒮𝓓) ] γ is) holds
   IH = γ₁-below-γ is

   † : (Σ k ꞉ 𝟚 𝓤 ,
         (β j ∈ₛ (⁅ ↑ˢ[ (β i , ϟ i ) ] , γ₁ is ⁆ [ k ])) holds)
     → (β j ∈ₛ γ (i ∷ is)) holds
   † (inl ⋆ , r) = ∣ inl r        ∣
   † (inr ⋆ , r) = ∣ inr (IH j r) ∣

 γ-equal-to-γ₁ : (bs : List B) → γ bs ＝ γ₁ bs
 γ-equal-to-γ₁ bs =
  ≤-is-antisymmetric (poset-of (𝒪 𝒮𝓓)) (γ-below-γ₁ bs) (γ₁-below-γ bs)

\end{code}

\begin{code}

 γ-lemma₁ : (is js : List B) → (γ is ≤[ poset-of (𝒪 𝒮𝓓) ] γ (is ++ js)) holds
 γ-lemma₁ []       js       = λ _ ()
 γ-lemma₁ (i ∷ is) []       = let
                               open PosetNotation (poset-of (𝒪 𝒮𝓓))

                               † : (i ∷ is) ＝ (i ∷ is) ++ []
                               † = []-right-neutral (i ∷ is)

                               ‡ : (γ (i ∷ is) ≤ γ (i ∷ is)) holds
                               ‡ = ≤-is-reflexive (poset-of (𝒪 𝒮𝓓)) (γ (i ∷ is))
                              in
                               transport (λ - → (γ (i ∷ is) ≤ γ -) holds) † ‡
 γ-lemma₁ (i ∷ is) (j ∷ js) x p = Ⅲ x (Ⅱ x (Ⅰ x p))
   where
    † : (γ₁ is ≤[ poset-of (𝒪 𝒮𝓓) ] γ₁ (is ++ (j ∷ js))) holds
    † y q =
     γ-below-γ₁ (is ++ (j ∷ js)) y (γ-lemma₁ is (j ∷ js) y (γ₁-below-γ is y q))

    Ⅰ = γ-below-γ₁ (i ∷ is)
    Ⅱ = ∨[ 𝒪 𝒮𝓓 ]-right-monotone †
    Ⅲ = γ₁-below-γ (i ∷ (is ++ (j ∷ js)))

 γ-lemma₂ : (is js : List B) → (γ js ≤[ poset-of (𝒪 𝒮𝓓) ] γ (is ++ js)) holds
 γ-lemma₂    []        js = ≤-is-reflexive (poset-of (𝒪 𝒮𝓓)) (γ js)
 γ-lemma₂ is@(i ∷ is′) js = λ x p → ∣_∣ (inr (γ-lemma₂ is′ js x p))

\end{code}

\begin{code}

 principal-filter-is-compact₀ : (c : ⟨ 𝓓 ⟩∙)
                              → (κ : is-compact 𝓓 c)
                              → is-compact-open 𝒮𝓓 ↑ˢ[ (c , κ) ] holds
 principal-filter-is-compact₀ c κ S δ p = ∥∥-rec ∃-is-prop † q
  where
   q : (c ∈ₛ (⋁[ 𝒪 𝒮𝓓 ] S)) holds
   q = ⊆ₖ-implies-⊆ₛ ↑ˢ[ (c , κ) ] (⋁[ 𝒪 𝒮𝓓 ] S) p c (reflexivity 𝓓 c)

   † : Σ i ꞉ index S , (c ∈ₛ (S [ i ])) holds
     → ∃ i ꞉ index S , (↑ˢ[ (c , κ) ] ≤[ poset-of (𝒪 𝒮𝓓) ] S [ i ]) holds
   † (i , r) = ∣ i , ‡ ∣
    where
     ‡ :  (↑ˢ[ c , κ ] ≤[ poset-of (𝒪 𝒮𝓓) ] (S [ i ])) holds
     ‡ d = upward-closure (S [ i ]) c (β d) r

 principal-filter-is-compact : (b : B)
                             → is-compact-open 𝒮𝓓 ↑ˢ[ (β b , ϟ b) ] holds
 principal-filter-is-compact b S δ p = ∥∥-rec ∃-is-prop † q
  where
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

 γ-gives-compact-opens : (bs : List B) → is-compact-open 𝒮𝓓 (γ bs) holds
 γ-gives-compact-opens bs =
  transport (λ - → is-compact-open 𝒮𝓓 - holds) (γ-equal-to-γ₁ bs ⁻¹) †
   where
    † : is-compact-open 𝒮𝓓 (γ₁ bs) holds
    † = γ₁-gives-compact-opens bs

\end{code}

\begin{code}

 sup-is-compact : (c d s : ⟨ 𝓓 ⟩∙)
                → (κᶜ : is-compact 𝓓 c)
                → (κᵈ : is-compact 𝓓 d)
                → is-sup (underlying-order 𝓓) s (binary-family 𝓤 c d [_])
                → is-compact 𝓓 s
 sup-is-compact c d s κᶜ κᵈ (p , q) =
  binary-join-is-compact 𝓓 (p (inl ⋆)) (p (inr ⋆)) η κᶜ κᵈ
   where
    η : (d₁ : ⟨ 𝓓 ⟩∙) →
         underlying-order 𝓓 (binary-family 𝓤 c d [ inl ⋆ ]) d₁ →
         underlying-order 𝓓 (binary-family 𝓤 c d [ inr ⋆ ]) d₁ →
         underlying-order 𝓓 s d₁
    η d₁ r₁ r₂ = q d₁ λ { (inl ⋆) → r₁ ; (inr ⋆) → r₂ }

 open DefnOfScottLocale 𝓓 𝓤 pe using (_⊆ₛ_)

 principal-filter-reflects-joins : (c d s : ⟨ 𝓓 ⟩∙)
                                 → (κᶜ : is-compact 𝓓 c)
                                 → (κᵈ : is-compact 𝓓 d)
                                 → (σ : is-sup (underlying-order 𝓓) s (binary-family 𝓤 c d [_]))
                                 →
                                   let
                                    κˢ = sup-is-compact c d s κᶜ κᵈ σ
                                   in
                                    ↑ˢ[ s , κˢ ] ＝ ↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ]
 principal-filter-reflects-joins c d s κᶜ κᵈ σ =
  ≤-is-antisymmetric (poset-of (𝒪 𝒮𝓓)) Ⅰ Ⅱ
   where
    open PosetReasoning (poset-of (𝒪 𝒮𝓓))

    κₛ : is-compact 𝓓 s
    κₛ = sup-is-compact c d s κᶜ κᵈ σ

    † : (↑ˢ[ s , κₛ ] ⊆ₛ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ])) holds
    † x p = (c ⊑⟨ 𝓓 ⟩[ pr₁ σ (inl ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)
          , (d ⊑⟨ 𝓓 ⟩[ pr₁ σ (inr ⋆) ] s ⊑⟨ 𝓓 ⟩[ p ] x ∎⟨ 𝓓 ⟩)

    ‡ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ]) ⊆ₛ ↑ˢ[ s , κₛ ]) holds
    ‡ x (p , q) = pr₂ σ x λ { (inl ⋆) → p ; (inr ⋆) → q }

    Ⅰ : (↑ˢ[ s , κₛ ] ⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ])) holds
    Ⅰ = ⊆ₛ-implies-⊆ₖ ↑ˢ[ s , κₛ ] (↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ]) †

    Ⅱ : ((↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ]) ⊆ₖ ↑ˢ[ s , κₛ ]) holds
    Ⅱ = ⊆ₛ-implies-⊆ₖ (↑ˢ[ c , κᶜ ] ∧[ 𝒪 𝒮𝓓 ] ↑ˢ[ d , κᵈ ]) ↑ˢ[ s , κₛ ] ‡

\end{code}

\begin{code}

 open import Locales.ScottLocale.Properties pt fe 𝓤
 open BottomLemma 𝓓 𝕒 hl
 open ScottLocaleProperties 𝓓 hl hscb pe

 ⊤-is-compact : is-compact-open 𝒮𝓓 𝟏[ 𝒪 𝒮𝓓 ] holds
 ⊤-is-compact = transport (λ - → is-compact-open 𝒮𝓓 - holds) ↑⊥-is-top †
  where
   † : is-compact-open ScottLocale ↑ˢ[ ⊥ᴰ , ⊥κ ] holds
   † = principal-filter-is-compact₀ ⊥ᴰ ⊥κ

 γ-closure-under-∧ : (is js : List B)
                   → ∃ ks ꞉ List B , γ₁ ks ＝ γ₁ is ∧[ 𝒪 𝒮𝓓 ] γ₁ js
 γ-closure-under-∧    []       js       = ∣ [] , † ∣
                                           where
                                            † = 𝟎-left-annihilator-for-∧ (𝒪 𝒮𝓓) (γ₁ js) ⁻¹
 γ-closure-under-∧ is@(_ ∷ _)  []       = ∣ [] , † ∣
                                           where
                                            † = 𝟎-right-annihilator-for-∧ (𝒪 𝒮𝓓) (γ₁ is) ⁻¹
 γ-closure-under-∧    (i ∷ is) (j ∷ js) = ∥∥-rec ∃-is-prop † IH
  where
   open Meets (λ a b → a ⊑⟨ 𝓓 ⟩ₚ b)

   IH : ∃ ks ꞉ List B , γ₁ ks ＝ γ₁ is ∧[ 𝒪 𝒮𝓓 ] γ₁ js
   IH = γ-closure-under-∧ is js

   † : Σ ks′ ꞉ List B , γ₁ ks′ ＝ γ₁ is ∧[ 𝒪 𝒮𝓓 ] γ₁ js
     → ∃ ks ꞉ List B , γ₁ ks ＝ γ₁ (i ∷ is) ∧[ 𝒪 𝒮𝓓 ] γ₁ (j ∷ js)
   † (ks′ , p) = cases †₁ †₂ (dc (β i) (β j))
    where
     †₁ : (β i) ↑[ 𝓓 ] (β j) holds
        → ∃ ks ꞉ List B , γ₁ ks ＝ (γ₁ (i ∷ is)) ∧[ 𝒪 𝒮𝓓 ] (γ₁ (j ∷ js))
     †₁ υ = ∥∥-rec ∃-is-prop ‡₁ υ
      where
       ‡₁ : (Σ u ꞉ ⟨ 𝓓 ⟩∙ , β i ⊑⟨ 𝓓 ⟩ u × β j ⊑⟨ 𝓓 ⟩ u)
          → ∃ ks ꞉ List B , γ₁ ks ＝ γ₁ (i ∷ is) ∧[ 𝒪 𝒮𝓓 ] γ₁ (j ∷ js)
       ‡₁ (u , q , r) =
         ∥∥-rec
          ∃-is-prop
          ♣
          (small-compact-basis-contains-all-compact-elements 𝓓 β scb s κ)
        where
         ς : has-supₚ 𝓓 ⁅ β i , β j ⁆ holds
         ς = bc ⁅ β i , β j ⁆ ∣ u , (ub₂-implies-ub-for-binary-family (underlying-orderₚ 𝓓) (β i) (β j) u (q , r)) ∣

         s : ⟨ 𝓓 ⟩∙
         s = pr₁ ς

         κ : is-compact 𝓓 s
         κ = sup-is-compact (β i) (β j) s (ϟ i) (ϟ j) (pr₂ ς)

         ♣ : Σ k ꞉ B , β k ＝ s
           → ∃ ks ꞉ List B , γ₁ ks ＝ γ₁ (i ∷ is) ∧[ 𝒪 𝒮𝓓 ] γ₁ (j ∷ js)
         ♣ (k , t) = ∣ (k ∷ ks′) , ♢ ∣
          where
           Ⅰ = ap
                (λ - → - ∨[ 𝒪 𝒮𝓓 ] γ₁ ks′)
                (to-subtype-＝ (holds-is-prop ∘ is-scott-open) (ap (principal-filter 𝓓) t))
           Ⅱ = ap (λ - → binary-join (𝒪 𝒮𝓓) ↑ˢ[ s , κ ] -) p
           Ⅲ = binary-distributivity-op (𝒪 𝒮𝓓) ↑ˢ[ s , κ ] (γ₁ is) (γ₁ js)

           𝓁𝒽𝓈 = (↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] γ₁ is) ∧[ 𝒪 𝒮𝓓 ] (↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] γ₁ js)
           𝓇𝒽𝓈 = (↑ˢ[ β i , ϟ i ] ∨[ 𝒪 𝒮𝓓 ] γ₁ is) ∧[ 𝒪 𝒮𝓓 ] (↑ˢ[ β j , ϟ j ] ∨[ 𝒪 𝒮𝓓 ] γ₁ js)

           φ : (𝓁𝒽𝓈 ⊆ₛ 𝓇𝒽𝓈) holds
           φ x (p₁ , p₂) = {!!}

           ψ : (𝓇𝒽𝓈 ⊆ₛ 𝓁𝒽𝓈) holds
           ψ x (p₁ , p₂) = ∥∥-rec₂ (holds-is-prop (x ∈ₛ 𝓁𝒽𝓈)) ϑ p₁ p₂
            where
             ϑ : Sigma (index (binary-family 𝓤 ↑ˢ[ β i , ϟ i ] (γ₁ is)))
                  (λ i₁ →
                     pr₁ (binary-family 𝓤 ↑ˢ[ β i , ϟ i ] (γ₁ is) [ i₁ ]) x holds) →
                  Sigma (index (binary-family 𝓤 ↑ˢ[ β j , ϟ j ] (γ₁ js)))
                  (λ i₁ →
                     pr₁ (binary-family 𝓤 ↑ˢ[ β j , ϟ j ] (γ₁ js) [ i₁ ]) x holds) →
                  (x ∈ₛ 𝓁𝒽𝓈) holds
             ϑ (inl ⋆ , q) (inl ⋆ , s) = {!pr₂ (pr₂ ς)!} , {!!}
             ϑ (inl ⋆ , q) (inr ⋆ , s) = {!!}
             ϑ (inr x , q) (r , s) = {!!}

           ※ = ≤-is-antisymmetric
                (poset-of (𝒪 𝒮𝓓))
                (⊆ₛ-implies-⊆ₖ 𝓁𝒽𝓈 𝓇𝒽𝓈 φ)
                (⊆ₛ-implies-⊆ₖ 𝓇𝒽𝓈 𝓁𝒽𝓈 ψ)

           ♢ : γ₁ (k ∷ ks′) ＝ γ₁ (i ∷ is) ∧[ 𝒪 𝒮𝓓 ] γ₁ (j ∷ js)
           ♢ =
            ↑ˢ[ β k , ϟ k ] ∨[ 𝒪 𝒮𝓓 ] γ₁ ks′                                              ＝⟨ Ⅰ    ⟩
            ↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] γ₁ ks′                                                  ＝⟨ Ⅱ    ⟩
            ↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] (γ₁ is ∧[ 𝒪 𝒮𝓓 ] γ₁ js)                                 ＝⟨ Ⅲ    ⟩
            (↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] γ₁ is) ∧[ 𝒪 𝒮𝓓 ] (↑ˢ[ s , κ ] ∨[ 𝒪 𝒮𝓓 ] γ₁ js)         ＝⟨ ※    ⟩
            (↑ˢ[ β i , ϟ i ] ∨[ 𝒪 𝒮𝓓 ] γ₁ is) ∧[ 𝒪 𝒮𝓓 ] (↑ˢ[ β j , ϟ j ] ∨[ 𝒪 𝒮𝓓 ] γ₁ js) ＝⟨ refl ⟩
            γ₁ (i ∷ is) ∧[ 𝒪 𝒮𝓓 ] γ₁ (j ∷ js)                                             ∎

     †₂ : ¬ (bounded-above 𝓓 (β i) (β j) holds)
        → ∃ ks ꞉ List B , γ₁ ks ＝ (γ₁ (i ∷ is)) ∧[ 𝒪 𝒮𝓓 ] (γ₁ (j ∷ js))
     †₂ = {!!}

\end{code}

\begin{code}

 basis-for-𝒮𝓓 : Fam 𝓤 ⟨ 𝒪 𝒮𝓓 ⟩
 basis-for-𝒮𝓓 = List B , γ

 open PropertiesAlgebraic 𝓓 𝕒

 𝒮𝓓-dir-basis-forᴰ : directed-basis-forᴰ (𝒪 𝒮𝓓) basis-for-𝒮𝓓
 𝒮𝓓-dir-basis-forᴰ U@(_ , so) = (D , δ) , † , 𝒹
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
    †₂ (U′ , ψ) k p = ‡₂ k (reflexivity 𝓓 (β k))
     where
      r : ↑ˢ[ β k , ϟ k ] ＝ γ (k ∷ [])
      r =
       ↑ˢ[ β k , ϟ k ]                         ＝⟨ Ⅰ ⟩
       ↑ˢ[ β k , ϟ k ] ∨[ 𝒪 𝒮𝓓 ] 𝟎[ 𝒪 𝒮𝓓 ]     ＝⟨ Ⅱ ⟩
       γ (k ∷ [])                              ∎
        where
         Ⅰ = 𝟎-left-unit-of-∨ (𝒪 𝒮𝓓) ↑ˢ[ β k , ϟ k ] ⁻¹
         Ⅱ = γ-equal-to-γ₁ (k ∷ []) ⁻¹

      ‡₂ : (↑ˢ[ β k , ϟ k ] ≤[ poset-of (𝒪 𝒮𝓓) ] U′) holds
      ‡₂ = transport
            (λ - → (- ≤[ poset-of (𝒪 𝒮𝓓) ] U′) holds)
            (r ⁻¹)
            (ψ ((k ∷ []) , λ { _ in-head → p }))

    † : (U is-lub-of ⁅ γ d ∣ d ε (D , δ) ⁆) holds
    † = †₁ , †₂

    𝒹↑ : ((is , _) (js , _) : D)
       → ∃ (ks , _) ꞉ D ,
            (γ is ≤[ poset-of (𝒪 𝒮𝓓) ] γ ks) holds
          × (γ js ≤[ poset-of (𝒪 𝒮𝓓) ] γ ks) holds
    𝒹↑ (is , 𝕚) (js , 𝕛)= ∣ ((is ++ js) , ♣) , γ-lemma₁ is js , γ-lemma₂ is js ∣
     where
      ♣ : (b : B) → member b (is ++ js) → 𝔘 (β b) holds
      ♣ b q = cases (𝕚 b) (𝕛 b) (member-in-++ is js b q)

    𝒹 : is-directed (𝒪 𝒮𝓓) (⁅ γ d ∣ d ε (D , δ) ⁆) holds
    𝒹 = ∣ [] , (λ _ ()) ∣ , 𝒹↑

 σᴰ : spectralᴰ 𝒮𝓓
 σᴰ = pr₁ Σ-assoc (𝒷 , (γ-gives-compact-opens , τ , μ))
  where
   𝒷 : directed-basisᴰ (𝒪 𝒮𝓓)
   𝒷 = basis-for-𝒮𝓓 , 𝒮𝓓-dir-basis-forᴰ

   τ : contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   τ = ∥∥-rec
        (holds-is-prop (contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓))
        †
        (compact-opens-are-basic 𝒮𝓓 𝒷 𝟏[ 𝒪 𝒮𝓓 ] ⊤-is-compact)
    where
     † : Σ is ꞉ List B , (γ is) ＝ 𝟏[ 𝒪 𝒮𝓓 ]
       → contains-top (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
     † (is , p) =
      ∣ is , transport (λ - → is-top (𝒪 𝒮𝓓) - holds) (p ⁻¹) (𝟏-is-top (𝒪 𝒮𝓓)) ∣

   μ : closed-under-binary-meets (𝒪 𝒮𝓓) basis-for-𝒮𝓓 holds
   μ = {!!}

\end{code}
