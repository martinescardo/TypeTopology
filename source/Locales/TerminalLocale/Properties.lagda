--------------------------------------------------------------------------------
title:        Some properties of the terminal locale
author:       Ayberk Tosun
date-started: 2024-03-09
--------------------------------------------------------------------------------

We collect properties of the terminal locale in this module.

Some of the facts below can be derived from general theorems about Stone spaces,
since the terminal locale is a Stone space. At the moment of writing, however,
the machinery for Stone locales needs a bit refactoring so I'm writing these
easy facts directly.

TODO: Refactor the following as to derive them from more general theorems about
Stone spaces.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size

module Locales.TerminalLocale.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.Clopen pt fe sr
open import Locales.Compactness.Definition pt fe
open import Locales.Frame pt fe
open import Locales.InitialFrame pt fe
open import Locales.Spectrality.SpectralityOfOmega pt fe sr
open import Locales.Stone pt fe sr
open import Locales.StoneImpliesSpectral pt fe sr
open import Locales.ZeroDimensionality pt fe sr
open import Slice.Family
open import UF.Equiv
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt hiding (_∨_; ∨-elim)

module _ (pe : propext 𝓤) where

 open Spectrality-of-𝟎 𝓤 pe

\end{code}

Every compact open of the initial frame is either `⊤` or `⊥`.

\begin{code}

 compact-opens-are-boolean : (P : Ω 𝓤)
                          → is-compact-open (𝟏Loc pe) P holds
                          → (Ǝ K ꞉ 𝟚 𝓤 , P ＝ ℬ𝟎 [ K ]) holds
 compact-opens-are-boolean P κ =
  ∥∥-rec
   ∃-is-prop
   γ
   (κ (𝒮↑ P)
   (covers-of-directified-basis-are-directed (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎 ℬ𝟎-is-basis-for-𝟎 P) c₀)
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
    γ ([]       , φ) = ∣ inl ⋆ , fails-gives-equal-⊥ pe fe P †  ∣
                        where
                         † : ¬ (P holds)
                         † = 𝟘-elim ∘ (𝟎-is-bottom (𝒪 (𝟏Loc pe)) ⊥) ∘ φ
    γ ((p ∷ _) , φ) = ∣ inr ⋆ ,  holds-gives-equal-⊤ pe fe P p ∣

\end{code}

Every compact open of the initial frame is a decidable proposition.

\begin{code}

 compact-implies-boolean : (P : Ω 𝓤)
                         → is-compact-open (𝟏Loc pe) P holds
                         → is-decidable (P holds)
 compact-implies-boolean P κ =
  ∥∥-rec
   (decidability-of-prop-is-prop fe (holds-is-prop P))
   γ
   (compact-opens-are-boolean P κ)
   where
    γ : Σ b ꞉ 𝟚 𝓤 , P ＝ ℬ𝟎 [ b ] → is-decidable (P holds)
    γ (inl p , q) = inr (equal-⊥-gives-fails P q)
    γ (inr _ , p) = inl (equal-⊤-gives-holds P p)

\end{code}

The bottom proposition `⊥` is obviously the same thing as the empty join, but
this fact is not a definitional equality.

\begin{code}

 𝟎-is-⊥ : ⊥ ＝ 𝟎[ 𝒪 (𝟏Loc pe) ]
 𝟎-is-⊥ = ⇔-gives-＝
           pe
           ⊥
           𝟎[ 𝒪 (𝟏Loc pe) ]
           (holds-gives-equal-⊤ pe fe _ (𝟘-elim , 𝟎-is-bottom (𝒪 (𝟏Loc pe)) ⊥))

\end{code}

Added on 2024-05-28.

The following is probably written down somewhere else, but this is the right
place for it.

\begin{code}

 binary-join-is-disjunction : (P Q : ⟨ 𝒪 (𝟏Loc pe) ⟩)
                            → P ∨[ 𝟎-𝔽𝕣𝕞 pe ] Q ＝ P ∨ Q
 binary-join-is-disjunction P Q =
  ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-unique ⁅ P , Q ⁆ (P ∨ Q) (υ , φ) ⁻¹
   where
    open Joins (λ x y → x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] y)

    υ : ((P ∨ Q) is-an-upper-bound-of ⁅ P , Q ⁆) holds
    υ ₀ p = ∣ inl p ∣
    υ ₁ q = ∣ inr q ∣

    φ : ((R , _) : upper-bound ⁅ P , Q ⁆) → ((P ∨ Q) ⇒ R) holds
    φ (R , ψ) = ∨-elim P Q R (ψ (inl ⋆)) (ψ (inr ⋆))

\end{code}

End of addition

Every compact open of the initial frame is a clopen i.e. is a complemented
proposition.

\begin{code}

 compact-implies-clopen : (P : Ω 𝓤)
                        → (is-compact-open (𝟏Loc pe) P
                        ⇒ is-clopen (𝒪 (𝟏Loc pe)) P) holds
 compact-implies-clopen P κ = cases † ‡ (compact-implies-boolean P κ)
  where
   † : P holds → is-clopen (𝒪 (𝟏Loc pe)) P holds
   † p = transport
          (λ - → is-clopen (𝒪 (𝟏Loc pe)) - holds)
          (holds-gives-equal-⊤ pe fe P p ⁻¹)
          (𝟏-is-clopen (𝟎-𝔽𝕣𝕞 pe))

   ‡ : ¬ (P holds) → is-clopen (𝒪 (𝟏Loc pe)) P holds
   ‡ ν = transport
          (λ - → is-clopen (𝒪 (𝟏Loc pe)) - holds)
          q
          (𝟎-is-clopen (𝟎-𝔽𝕣𝕞 pe))
    where
     Ⅰ = 𝟎-is-⊥ ⁻¹
     Ⅱ = fails-gives-equal-⊥ pe fe P ν ⁻¹

     q : 𝟎[ 𝒪 (𝟏Loc pe) ] ＝ P
     q = 𝟎[ 𝒪 (𝟏Loc pe) ] ＝⟨ Ⅰ ⟩ ⊥ ＝⟨ Ⅱ ⟩ P ∎

\end{code}

Every decidable proposition of `Ω` is a compact open of the initial frame.

\begin{code}

 decidable-implies-compact : (P : Ω 𝓤)
                           → is-decidable (P holds)
                           → is-compact-open (𝟏Loc pe) P holds
 decidable-implies-compact P (inl p) = transport
                                        (λ - → is-compact-open (𝟏Loc pe) - holds)
                                        (holds-gives-equal-⊤ pe fe P p ⁻¹)
                                        (𝟎Frm-is-compact 𝓤 pe)
 decidable-implies-compact P (inr ν) =
  transport (λ - → is-compact-open (𝟏Loc pe) - holds) † (𝟎-is-compact (𝟏Loc pe))
   where
    Ⅰ = 𝟎-is-⊥ ⁻¹
    Ⅱ = fails-gives-equal-⊥ pe fe P ν ⁻¹

    † : 𝟎[ 𝒪 (𝟏Loc pe) ] ＝ P
    † = 𝟎[ 𝒪 (𝟏Loc pe) ] ＝⟨ Ⅰ ⟩ ⊥ ＝⟨ Ⅱ ⟩ P ∎

\end{code}

Every clopen of the terminal locale is a compact open.

\begin{code}

 clopen-implies-compact : (P : Ω 𝓤)
                        → (is-clopen (𝒪 (𝟏Loc pe)) P ⇒ is-compact-open (𝟏Loc pe) P)
                           holds
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

Added on 2024-08-05.

\begin{code}

 ℬ𝟎-consists-of-clopens : consists-of-clopens (𝒪 (𝟏Loc pe)) ℬ𝟎 holds
 ℬ𝟎-consists-of-clopens (inl ⋆) =
  transport (λ - → is-clopen (𝒪 (𝟏Loc pe)) - holds) (p ⁻¹) †
   where
    p : ⊥ ＝ 𝟎[ 𝒪 (𝟏Loc pe) ]
    p = 𝟎-is-⊥

    † : is-clopen (𝒪 (𝟏Loc pe)) 𝟎[ 𝒪 (𝟏Loc pe) ] holds
    † = 𝟎-is-clopen (𝒪 (𝟏Loc pe))
 ℬ𝟎-consists-of-clopens (inr ⋆) =
  𝟏-is-clopen (𝒪 (𝟏Loc pe))

 ℬ𝟎↑-consists-of-clopens : consists-of-clopens (𝒪 (𝟏Loc pe)) ℬ𝟎↑ holds
 ℬ𝟎↑-consists-of-clopens []       = 𝟎-is-clopen (𝒪 (𝟏Loc pe))
 ℬ𝟎↑-consists-of-clopens (i ∷ is) =
  clopens-are-closed-under-∨ (𝒪 (𝟏Loc pe)) (ℬ𝟎 [ i ]) (ℬ𝟎↑ [ is ]) † ‡
   where
    † : is-clopen (𝒪 (𝟏Loc pe)) (ℬ𝟎 [ i ]) holds
    † = ℬ𝟎-consists-of-clopens i

    ‡ : is-clopen (𝒪 (𝟏Loc pe)) (ℬ𝟎↑ [ is ]) holds
    ‡ = ℬ𝟎↑-consists-of-clopens is

 𝟏-zero-dimensionalᴰ : zero-dimensionalᴰ (𝒪 (𝟏Loc pe))
 𝟏-zero-dimensionalᴰ = ℬ𝟎↑
                     , pr₂ (ℬ𝟎↑-directed-basisᴰ 𝓤 pe)
                     , ℬ𝟎↑-consists-of-clopens

\end{code}

Added on 2024-08-10.

\begin{code}

 𝟏-stoneᴰ : stoneᴰ (𝟏Loc pe)
 𝟏-stoneᴰ = 𝟎Frm-is-compact 𝓤 pe , 𝟏-zero-dimensionalᴰ

 𝟏-is-stone : is-stone (𝟏Loc pe) holds
 𝟏-is-stone = 𝟎Frm-is-compact 𝓤 pe
            , ∣ 𝟏-zero-dimensionalᴰ ∣

\end{code}
