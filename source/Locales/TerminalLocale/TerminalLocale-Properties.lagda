Added on 2024-03-07

Based in part on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size

module Locales.TerminalLocale.TerminalLocale-Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.Clopen pt fe sr
open import Locales.Compactness pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralityOfOmega pt fe sr
open import Locales.StoneImpliesSpectral pt fe sr
open import Slice.Family
open import UF.Logic
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Equiv

open AllCombinators pt fe
open PropositionalTruncation pt

open Locale

\end{code}


\begin{code}

module _ (pe : propext 𝓤) where

 open Spectrality-of-𝟎 𝓤 pe

 finite-join : List (𝟚 𝓤) → 𝟚 𝓤
 finite-join []       = ₀
 finite-join (b ∷ bs) = or₂ b (finite-join bs)

 compact-opens-are-clopen : (P : Ω 𝓤)
                          → is-compact-open (𝟏Loc pe) P holds
                          → (Ǝ K ꞉ 𝟚 𝓤 , P ＝ ℬ𝟎 [ K ]) holds
 compact-opens-are-clopen P κ =
  ∥∥-rec ∃-is-prop γ (κ (𝒮↑ P) (covers-of-directified-basis-are-directed (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎 ℬ𝟎-is-basis-for-𝟎 P) c₀)
   where
    S : Fam 𝓤 (𝟚 𝓤)
    S = pr₁ (ℬ𝟎-is-basis-for-𝟎 P)

    c : P ＝ ⋁[ 𝒪 (𝟏Loc pe) ] 𝒮↑ P
    c = ⋁[ 𝒪 (𝟏Loc pe) ]-unique (𝒮↑ P) P (pr₂ (ℬ𝟎↑-is-basis P))

    c₀ : (P ⇒ ⋁[ 𝒪 (𝟏Loc pe) ] 𝒮↑ P) holds
    c₀ = ⇔-gives-⇒
          P
          (⋁[ 𝒪 (𝟏Loc pe) ] 𝒮↑ P)
          (equal-⊤-gives-holds _ (＝-gives-⇔ pe P (⋁[ 𝒪 (𝟏Loc pe) ] 𝒮↑ P) c))

    open PosetReasoning (poset-of (𝟎-𝔽𝕣𝕞 pe))

    γ : (Σ bs ꞉ List (P holds) , (P ⇒ 𝒮↑ P [ bs ]) holds)
      → (Ǝ K ꞉ 𝟚 𝓤 , P ＝ ℬ𝟎 [ K ]) holds
    γ ([]       , φ) = ∣ inl ⋆ , to-subtype-＝ (λ _ → being-prop-is-prop fe) (pe (holds-is-prop P) 𝟘-is-prop † λ ()) ∣
                        where
                         foo : 𝒮↑ P [ [] ] ＝ 𝟎[ 𝟎-𝔽𝕣𝕞 pe ]
                         foo = refl

                         † : (P ⇒ ⊥) holds
                         † p = 𝟎-is-bottom (𝟎-𝔽𝕣𝕞 pe) ⊥ (φ p)
    γ ((p ∷ ps) , φ) = ∣ inr ⋆ , to-subtype-＝ (λ _ → being-prop-is-prop fe) ((pe (holds-is-prop P) 𝟙-is-prop (λ _ → ⋆) λ ⋆ → p)) ∣

 compact-implies-boolean : (P : Ω 𝓤)
                         → is-compact-open (𝟏Loc pe) P holds
                         → is-decidable (P holds)
 compact-implies-boolean P κ =
  ∥∥-rec (decidability-of-prop-is-prop fe (holds-is-prop P)) γ (compact-opens-are-clopen P κ)
   where
    γ : Σ b ꞉ 𝟚 𝓤 , P ＝ ℬ𝟎 [ b ] → is-decidable (P holds)
    γ (inl p , q) = inr (equal-⊥-gives-fails P q)
    γ (inr _ , p) = inl (equal-⊤-gives-holds P p)

 𝟎-is-⊥ : ⊥ ＝ 𝟎[ 𝒪 (𝟏Loc pe) ]
 𝟎-is-⊥ = ⇔-gives-＝ pe ⊥ 𝟎[ 𝒪 (𝟏Loc pe) ] (holds-gives-equal-⊤ pe fe _ ((λ ()) , 𝟎-is-bottom (𝒪 (𝟏Loc pe)) ⊥))

 compact-implies-clopen : (P : Ω 𝓤)
                        → (is-compact-open (𝟏Loc pe) P
                        ⇒ is-clopen (𝒪 (𝟏Loc pe)) P) holds
 compact-implies-clopen P κ = cases † ‡ (compact-implies-boolean P κ)
  where
   † : P holds → is-clopen (𝒪 (𝟏Loc pe)) P holds
   † p = transport (λ - → is-clopen (𝒪 (𝟏Loc pe)) - holds) (holds-gives-equal-⊤ pe fe P p ⁻¹) (𝟏-is-clopen (𝟎-𝔽𝕣𝕞 pe))

   ‡ : ¬ (P holds) → is-clopen (𝒪 (𝟏Loc pe)) P holds
   ‡ ν = transport (λ - → is-clopen (𝒪 (𝟏Loc pe)) - holds) q (𝟎-is-clopen (𝟎-𝔽𝕣𝕞 pe))
    where
     q : 𝟎[ 𝒪 (𝟏Loc pe) ] ＝ P
     q = 𝟎[ 𝒪 (𝟏Loc pe) ] ＝⟨ 𝟎-is-⊥ ⁻¹ ⟩ ⊥ ＝⟨ fails-gives-equal-⊥ pe fe P ν ⁻¹ ⟩ P ∎


 decidable-implies-compact : (P : Ω 𝓤)
                        → is-decidable (P holds)
                        → is-compact-open (𝟏Loc pe) P holds
 decidable-implies-compact P (inl p) = transport (λ - → is-compact-open (𝟏Loc pe) - holds) (holds-gives-equal-⊤ pe fe P p ⁻¹) (𝟎Frm-is-compact 𝓤 pe)
 decidable-implies-compact P (inr ν) =
  transport (λ - → is-compact-open (𝟏Loc pe) - holds) † (𝟎-is-compact (𝟏Loc pe))
   where
    † : 𝟎[ 𝒪 (𝟏Loc pe) ] ＝ P
    † = 𝟎[ 𝒪 (𝟏Loc pe) ] ＝⟨ 𝟎-is-⊥ ⁻¹ ⟩ ⊥ ＝⟨ fails-gives-equal-⊥ pe fe P ν ⁻¹ ⟩ P ∎

 clopen-implies-compact : (P : Ω 𝓤)
                        → is-clopen (𝒪 (𝟏Loc pe)) P holds
                        → is-compact-open (𝟏Loc pe) P holds
 clopen-implies-compact P 𝔠 =
  clopens-are-compact-in-compact-locales (𝟏Loc pe) (𝟎Frm-is-compact 𝓤 pe) P 𝔠

\end{code}

The type of compact opens of the terminal locale is equivalent to its type of
clopens.

\begin{code}

 clopen-equiv-compact : 𝒦 (𝟏Loc pe) ≃ 𝒞 (𝟏Loc pe)
 clopen-equiv-compact = g , (h ,  †) , h , ‡
  where
   g : 𝒦 (𝟏Loc pe) → 𝒞 (𝟏Loc pe)
   g (K , κ) = K , compact-implies-clopen K κ

   h : 𝒞 (𝟏Loc pe) → 𝒦 (𝟏Loc pe)
   h (K , 𝔠) = K , clopen-implies-compact K 𝔠

   † : (g ∘ h) ∼ id
   † U = to-subtype-＝ (holds-is-prop ∘ is-clopen (𝒪 (𝟏Loc pe))) refl

   ‡ : (h ∘ g) ∼ id
   ‡ U = to-subtype-＝ (holds-is-prop ∘ is-compact-open (𝟏Loc pe)) refl

\end{code}

The type of clopens of the terminal locale is equivalent to the type of
decidable propositions

\begin{code}

 clopen-equiv-decidable : 𝒞 (𝟏Loc pe) ≃ (Σ P ꞉ Ω 𝓤 , is-decidable (P holds))
 clopen-equiv-decidable = g , (h , ‡) , h , †
  where
   g : 𝒞 (𝟏Loc pe) → Σ P ꞉ Ω 𝓤 , is-decidable (P holds)
   g (K , 𝔠) = K , compact-implies-boolean K (clopen-implies-compact K 𝔠)

   h : (Σ P ꞉ Ω 𝓤 , is-decidable (P holds)) → 𝒞 (𝟏Loc pe)
   h (K , κ) = K , compact-implies-clopen K (decidable-implies-compact K κ)

   † : (h ∘ g) ∼ id
   † U =
    to-subtype-＝ (holds-is-prop ∘ is-clopen (𝒪 (𝟏Loc pe))) refl

   ‡ : (g ∘ h) ∼ id
   ‡ (P , _) =
    to-subtype-＝ (λ Q → decidability-of-prop-is-prop fe (holds-is-prop Q)) refl

\end{code}
