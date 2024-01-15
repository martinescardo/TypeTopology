Ayberk Tosun, 13 September 2023

The module contains the definition of a spectral locale.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.List hiding ([_])
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Size
open import UF.EquivalenceExamples

module Locales.Spectrality.SpectralityOfOmega
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        (𝓤 : Universe)
        (pe : propext 𝓤) where

open import Locales.InitialFrame pt fe
open import Locales.Frame        pt fe
open import Locales.Compactness  pt fe
open import Slice.Family
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.BasisDirectification pt fe sr
open import Locales.SmallBasis pt fe sr

open import UF.Logic
open AllCombinators pt fe
open PropositionalTruncation pt

open Spectrality-of-𝟎 𝓤 pe

bottom-of-𝟎Frm-is-⊥ : ⊥ ＝ 𝟎[ 𝟎-𝔽𝕣𝕞 pe ]
bottom-of-𝟎Frm-is-⊥ = only-𝟎-is-below-𝟎 (𝟎-𝔽𝕣𝕞 pe) ⊥ (λ ())

Ω-frm : Frame (𝓤 ⁺) 𝓤 𝓤
Ω-frm = 𝟎-𝔽𝕣𝕞 pe

𝟏-loc : Locale (𝓤 ⁺) 𝓤 𝓤
𝟏-loc = record { ⟨_⟩ₗ = ⟨ Ω-frm ⟩ ; frame-str-of = pr₂ Ω-frm }

𝟎Frm-is-compact : is-compact 𝟏-loc holds
𝟎Frm-is-compact S (∣i∣ , u) p = ∥∥-rec ∃-is-prop † (p ⋆)
 where
  † : (Σ j ꞉ index S , ((S [ j ]) holds))
    → ∃ j ꞉ index S , (𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] S [ j ]) holds
  † (j , q) = ∣ j , (λ _ → q) ∣

ℬ𝟎-consists-of-compact-opens : consists-of-compact-opens 𝟏-loc ℬ𝟎 holds
ℬ𝟎-consists-of-compact-opens (inl ⋆) =
 transport
  (λ - → is-compact-open 𝟏-loc - holds)
  (bottom-of-𝟎Frm-is-⊥ ⁻¹)
  (𝟎-is-compact 𝟏-loc)
ℬ𝟎-consists-of-compact-opens (inr ⋆) = 𝟎Frm-is-compact

ℬ𝟎↑-consists-of-compact-opens : consists-of-compact-opens 𝟏-loc ℬ𝟎↑ holds
ℬ𝟎↑-consists-of-compact-opens []       = 𝟎-is-compact 𝟏-loc
ℬ𝟎↑-consists-of-compact-opens (i ∷ is) =
 compact-opens-are-closed-under-∨ 𝟏-loc (ℬ𝟎 [ i ]) (ℬ𝟎↑ [ is ]) κ IH
  where
   κ : is-compact-open 𝟏-loc (ℬ𝟎 [ i ]) holds
   κ = ℬ𝟎-consists-of-compact-opens i

   IH : is-compact-open 𝟏-loc (ℬ𝟎↑ [ is ]) holds
   IH = ℬ𝟎↑-consists-of-compact-opens is

and₂-lemma₁ : (x y : 𝟚 𝓤) → (ℬ𝟎 [ and₂ x y ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] ℬ𝟎 [ x ]) holds
and₂-lemma₁ (inl ⋆) y       = λ ()
and₂-lemma₁ (inr ⋆) (inl ⋆) = λ ()
and₂-lemma₁ (inr ⋆) (inr ⋆) = λ { ⋆ → ⋆ }

and₂-lemma₂ : (x y : 𝟚 𝓤) → (ℬ𝟎 [ and₂ x y ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] ℬ𝟎 [ y ]) holds
and₂-lemma₂ (inl ⋆) y       = λ ()
and₂-lemma₂ (inr ⋆) (inl ⋆) = λ ()
and₂-lemma₂ (inr ⋆) (inr ⋆) = λ { ⋆ → ⋆ }

open Meets (λ x y → x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] y) hiding (is-top)

and₂-lemma₃ : (x y : 𝟚 𝓤) ((z , _) : lower-bound (ℬ𝟎 [ x ] , ℬ𝟎 [ y ]))
            → (z ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] ℬ𝟎 [ and₂ x y ]) holds
and₂-lemma₃ (inl ⋆) y (z , p₁ , p₂) = p₁
and₂-lemma₃ (inr ⋆) y (z , p₁ , p₂) = p₂

ℬ𝟎-is-closed-under-binary-meets : closed-under-binary-meets (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎 holds
ℬ𝟎-is-closed-under-binary-meets i j = ∣ and₂ i j , (†₁ , †₂) , and₂-lemma₃ i j ∣
 where
  †₁ : (ℬ𝟎 [ and₂ i j ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] ℬ𝟎 [ i ]) holds
  †₁ = and₂-lemma₁ i j

  †₂ : (ℬ𝟎 [ and₂ i j ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] ℬ𝟎 [ j ]) holds
  †₂ = and₂-lemma₂ i j


ℬ𝟎↑-directed-basisᴰ : directed-basisᴰ (𝟎-𝔽𝕣𝕞 pe)
ℬ𝟎↑-directed-basisᴰ = ℬ𝟎↑ , β↑
 where
  -- TODO: get rid of these projections.
  β↑ : directed-basis-forᴰ (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎↑
  β↑ U = pr₁ (pr₁ ℬ𝟎-is-directed-basis-for-𝟎 U)
       , (pr₂ (pr₁ ℬ𝟎-is-directed-basis-for-𝟎 U)
       , pr₂ ℬ𝟎-is-directed-basis-for-𝟎 U)

𝟎-𝔽𝕣𝕞-is-spectral : is-spectral 𝟏-loc holds
𝟎-𝔽𝕣𝕞-is-spectral =
 spectralᴰ-gives-spectrality
  𝟏-loc
  (ℬ𝟎↑ , pr₂ ℬ𝟎↑-directed-basisᴰ , ℬ𝟎↑-consists-of-compact-opens , γ)
  where
   κ : consists-of-compact-opens 𝟏-loc ℬ𝟎↑ holds
   κ []       = 𝟎-is-compact 𝟏-loc
   κ (i ∷ is) = compact-opens-are-closed-under-∨
                 𝟏-loc
                 (ℬ𝟎 [ i ])
                 (ℬ𝟎↑ [ is ])
                 (ℬ𝟎-consists-of-compact-opens i)
                 (κ is)

   t : is-top (𝟎-𝔽𝕣𝕞 pe) (𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ∨[ 𝟎-𝔽𝕣𝕞 pe ] 𝟎[ 𝟎-𝔽𝕣𝕞 pe ]) holds
   t = transport
        (λ - → is-top (𝟎-𝔽𝕣𝕞 pe) - holds)
        (𝟎-left-unit-of-∨ (𝟎-𝔽𝕣𝕞 pe) 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ⁻¹)
        (𝟏-is-top (𝟎-𝔽𝕣𝕞 pe))

   c : closed-under-binary-meets (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎↑ holds
   c = directify-preserves-closure-under-∧
        (𝟎-𝔽𝕣𝕞 pe)
        ℬ𝟎
        ℬ𝟎-is-basis-for-𝟎
        ℬ𝟎-is-closed-under-binary-meets

   γ : closed-under-finite-meets (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎↑ holds
   γ = ∣ (inr ⋆ ∷ []) , t ∣ , c

\end{code}
