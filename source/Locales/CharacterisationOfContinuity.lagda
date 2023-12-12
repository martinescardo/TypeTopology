Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.Base
open import UF.Subsingletons
open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.SubtypeClassifier

module Locales.CharacterisationOfContinuity (pt : propositional-truncations-exist)
                                            (fe : Fun-Ext)                          where

open import Locales.Frame               pt fe
open import Locales.WayBelowRelation.Definition pt fe
open import UF.Logic
open import Slice.Family
open import Locales.Compactness pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.Properties     pt fe

open PropositionalTruncation pt
open Existential pt
open Universal fe
open Implication fe
open Conjunction

open Locale

\end{code}

\begin{code}

continuity-condition : (Y : Locale 𝓤 𝓥 𝓦) (X : Locale 𝓤' 𝓥' 𝓦)
                     → (⟨ 𝒪 Y ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ⊔ 𝓤' ⊔ 𝓥')
continuity-condition Y X h =
 Ɐ b ꞉ ⟨ 𝒪 X ⟩ , Ɐ x ꞉ ⟨ 𝒪 Y ⟩ , is-compact-open X b ⇒
  b ≤[ poset-of (𝒪 X) ] h x ⇒
   (Ǝ a ꞉ ⟨ 𝒪 Y ⟩ , (is-compact-open Y a ∧ (a ≤y x) ∧ (b ≤ₓ h a)) holds)
    where
     open PosetNotation (poset-of (𝒪 X)) renaming (_≤_ to _≤ₓ_)
     open PosetNotation (poset-of (𝒪 Y)) renaming (_≤_ to _≤y_)

\end{code}

\begin{code}

characterisation-of-continuity : (Y : Locale 𝓤  𝓥  𝓦)
                               → (X : Locale 𝓤' 𝓥' 𝓦)
                               → is-spectral X holds
                               → (h : ⟨ 𝒪 Y ⟩ → ⟨ 𝒪 X ⟩)
                               → is-monotonic (poset-of (𝒪 Y)) (poset-of (𝒪 X)) h holds
                               → continuity-condition Y X h holds
                               → is-scott-continuous (𝒪 Y) (𝒪 X) h holds
characterisation-of-continuity Y X σ h μ ζ S δ = β , γ
 where
  open PosetReasoning (poset-of (𝒪 X))
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  β : (h (⋁[ (𝒪 Y) ] S) is-an-upper-bound-of ⁅ h s ∣ s ε S ⁆) holds
  β i = μ (S [ i ] , ⋁[ (𝒪 Y) ] S) (⋁[ (𝒪 Y) ]-upper S i)

  γ : (Ɐ (u , _) ꞉ upper-bound ⁅ h s ∣ s ε S ⁆ ,
        h (⋁[ (𝒪 Y) ] S) ≤[ poset-of (𝒪 X) ] u) holds
  γ (u , φ) = spectral-yoneda X σ (h (⋁[ 𝒪 Y ] S)) u †
   where
    † : ((K , _) : 𝒦 X)
      → (K ≤[ poset-of (𝒪 X) ] h (⋁[ 𝒪 Y ] S) ⇒ K  ≤[ poset-of (𝒪 X) ] u) holds
    † (K , κ) p = ∥∥-rec
                   (holds-is-prop (K ≤[ poset-of (𝒪 X) ] u))
                   ‡
                   (ζ K (⋁[ (𝒪 Y) ] S) κ p)
      where
       ‡ : _ → (K ≤[ poset-of (𝒪 X) ] u) holds
       ‡ (a , κₐ , q , r) =
         K                        ≤⟨ r                                    ⟩
         h a                      ≤⟨ ♠                                    ⟩
         ⋁[ (𝒪 X) ] ⁅ h s ∣ s ε S ⁆   ≤⟨ ⋁[ (𝒪 X) ]-least ⁅ h s ∣ s ε S ⁆ (u , φ) ⟩
         u                        ■
          where
           ♣ : (Σ i ꞉ index S , (a ≤[ poset-of (𝒪 Y) ] (S [ i ])) holds)
             → (h a ≤[ poset-of (𝒪 X) ] (⋁[ (𝒪 X) ] ⁅ h s ∣ s ε S ⁆)) holds
           ♣ (i , ψ) = h a                    ≤⟨ μ (a , S [ i ]) ψ               ⟩
                       h (S [ i ])            ≤⟨ ⋁[ (𝒪 X) ]-upper ⁅ h s ∣ s ε S ⁆ i  ⟩
                       ⋁[ (𝒪 X) ] ⁅ h s ∣ s ε S ⁆ ■

           ♠ : (h a ≤[ poset-of (𝒪 X) ] (⋁[ (𝒪 X) ] ⁅ h s ∣ s ε S ⁆)) holds
           ♠ = ∥∥-rec
                (holds-is-prop (h a ≤[ poset-of (𝒪 X) ] (⋁[ (𝒪 X) ] ⁅ h s ∣ s ε S ⁆)))
                ♣
                (κₐ S δ q)

\end{code}
