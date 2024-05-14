--------------------------------------------------------------------------------
author:         Ayberk Tosun
date-started:   2024-03-15
date-completed: 2024-05-13
--------------------------------------------------------------------------------

Let D be a Scott domain satisfying the condition that the existence of binary
upper bounds of compact elements is decidable. Denote by σ(D) the Scott locale
of domain D.

By a “point” of D, we mean a frame homomorphism F : 𝒪(σ(D)) → Ω.

Given a point F, we define the family of compact elements with principal filters
falling in F, i.e.

  { c : 𝒦(D) ∣ ↑c ∈ F }.

The notation 𝒦(D) above is our notation for the type of compact elements of
the domain.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.LawsonLocale.CompactElementsOfPoint
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.ScottDomain      pt fe 𝓤
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe 𝓤
open import Locales.Compactness pt fe hiding (is-compact)
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe hiding (is-inhabited)
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.InitialFrame pt fe
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.Properties pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.TerminalLocale.Properties pt fe sr
open import Slice.Family
open import UF.Logic
open import UF.Powerset
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier renaming (⊥ to ⊥ₚ)
open import UF.Univalence

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work in a module parameterized by a large and locally small locale `X`.

\begin{code}

module Preliminaries (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open ContinuousMaps

\end{code}

We use the abbreviation `𝟏L` for the terminal locale of the category of
`𝓤`-locales (i.e. large and locally small locales over universe `𝓤`).

\begin{code}

 𝟏L : Locale (𝓤 ⁺) 𝓤 𝓤
 𝟏L = 𝟏Loc pe

\end{code}

For the reader who might not be familiar, this is the locale defined by the
frame of opens `Ω`.

\begin{code}

 _ : ⟨ 𝒪 𝟏L ⟩ ＝ Ω 𝓤
 _ = refl

\end{code}

By a point of locale, we mean a continuous map from `𝟏L` into `X`.

\begin{code}

 Point : 𝓤 ⁺  ̇
 Point = 𝟏L ─c→  X

\end{code}

We now proceed to the definition of the family mentioned in the preamble. We
work with a dcpo `𝓓` that is assumed to

  - have a bottom element,
  - be a Scott domain, and
  - satisfy the aforementioned decidability condition for upper boundedness.

\begin{code}

open DefinitionOfScottDomain

module Construction
        (𝓓    : DCPO {𝓤 ⁺} {𝓤})
        (ua   : Univalence)
        (hl   : has-least (underlying-order 𝓓))
        (sd   : is-scott-domain 𝓓 holds)
        (dc   : decidability-condition 𝓓) where

 open SpectralScottLocaleConstruction₂ 𝓓 ua hl sd dc pe
 open SpectralScottLocaleConstruction 𝓓 hl hscb dc bc pe hiding (scb; β; ϟ)
 open DefnOfScottTopology 𝓓 𝓤

 open Preliminaries σ⦅𝓓⦆
 open Properties 𝓓

\end{code}

We denote by `B𝓓` the basis of `𝓓`.

\begin{code}

 B𝓓 : Fam 𝓤 ⟨ 𝓓 ⟩∙
 B𝓓 = index-of-compact-basis 𝓓 hscb , family-of-compact-elements 𝓓 hscb

\end{code}

We use the abbreviation `scb` for the proof that `B𝓓` is a small basis
consisting of compact opens.

\begin{code}

 scb : is-small-compact-basis 𝓓 (family-of-compact-elements 𝓓 hscb)
 scb = small-compact-basis 𝓓 hscb

\end{code}

By `βₖ i`, we denote the element denoted by an index `i`, packaged up with the
proof that it is compact.

\begin{code}

 open is-small-compact-basis scb
 open BottomLemma 𝓓 𝕒 hl

 βₖ : (i : index B𝓓) → Σ c ꞉ ⟨ 𝓓 ⟩∙ , is-compact 𝓓 c
 βₖ i = B𝓓 [ i ] , basis-is-compact i

\end{code}

We now write down the family of compact elements of a point which we denote
`𝒦-in-point`.

\begin{code}

 𝒦-in-point : Point → Fam 𝓤 ⟨ 𝓓 ⟩∙
 𝒦-in-point (F , _) =
  ⁅ B𝓓 [ i ] ∣ (i , _) ∶ (Σ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds) ⁆

\end{code}

The family `𝒦-in-point` is always inhabited.

\begin{code}

 open ScottLocaleProperties 𝓓 hl hscb pe

 𝒦-in-point-is-inhabited
  : (ℱ@(F , _) : Point)
  → is-inhabited (underlying-order 𝓓) (index (𝒦-in-point ℱ))
 𝒦-in-point-is-inhabited ℱ@(F , _) = ∥∥-rec ∃-is-prop † γ
  where
   Ⅲ : F 𝟏[ 𝒪 σ⦅𝓓⦆ ] ＝ ⊤
   Ⅲ = frame-homomorphisms-preserve-top (𝒪 σ⦅𝓓⦆) (𝒪 𝟏L) ℱ

   ζ : 𝟏[ 𝒪 σ⦅𝓓⦆ ] ∈ F
   ζ = equal-⊤-gives-holds (F 𝟏[ 𝒪 σ⦅𝓓⦆ ]) Ⅲ

   † : Σ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ → ∃ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds
   † (i , p) = ∣ i , equal-⊤-gives-holds (F ↑ˢ[ βₖ i ]) ※ ∣
    where
     Ⅰ = ap
          F
          (to-subtype-＝
            (holds-is-prop ∘ is-scott-open)
            (ap (principal-filter 𝓓) p))
     Ⅱ = ap F ↑⊥-is-top

     ※ : F ↑ˢ[ βₖ i ] ＝ ⊤
     ※ = F ↑ˢ[ βₖ i ]    ＝⟨ Ⅰ ⟩
         F ↑ˢ[ ⊥ᴰ , ⊥κ ] ＝⟨ Ⅱ ⟩
         F 𝟏[ 𝒪 σ⦅𝓓⦆ ]   ＝⟨ Ⅲ ⟩
         ⊤               ∎

   γ : ∃ i ꞉ index B𝓓 , B𝓓 [ i ] ＝ ⊥ᴰ
   γ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb ⊥ᴰ ⊥κ

\end{code}

The family `𝒦-in-point` is closed under binary upper bounds.

\begin{code}

 closed-under-binary-upperbounds
  : (ℱ : Point)
  → is-semidirected (underlying-order 𝓓) (𝒦-in-point ℱ [_])
 closed-under-binary-upperbounds ℱ (i , κᵢ) (j , κⱼ) =

\end{code}

To prove this, we use the assumption that upper boundedness of compact elements
is decidable.

\begin{code}

  let
   ϑ : is-decidable (bounded-above 𝓓 (B𝓓 [ i ]) (B𝓓 [ j ]) holds)
   ϑ = dc (B𝓓 [ i ]) (B𝓓 [ j ]) (basis-is-compact i) (basis-is-compact j)
  in

\end{code}

We now proceed by case analysis on whether or not the upper bound of `B𝓓 [ i ]`
and `B𝓓 [ j ]` exists. The cases are given in `case₁` and `case₂`.

\begin{code}

  cases case₁ case₂ ϑ
   where
    open DefnOfScottLocale 𝓓 𝓤 pe

    F = pr₁ ℱ

\end{code}

We denote by `b` and `c`, the elements `B𝓓 [ i ]` and `B𝓓 [ j ]` respectively.

\begin{code}

    b  = B𝓓 [ i ]
    κᵇ = basis-is-compact i
    c  = B𝓓 [ j ]
    κᶜ = basis-is-compact j

\end{code}

We first record, as a lemma that we will use in both cases, that
```
    (↑(b) ∧ ↑(c)) ∈ F
```

This is the case because we know `F(↑(b)) ＝ ⊤` and `F(↑(c)) ＝ ⊤` meaning we
have
```
  F(↑(b) ∧ ↑(c)) ＝ F(↑(b)) ∧ F(↑(c)) ＝ ⊤ ∧ ⊤ ＝ ⊤.
```

\begin{code}

    μₘ : (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ∈ F
    μₘ = equal-⊤-gives-holds (F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])) †
     where
      Ⅰ = frame-homomorphisms-preserve-meets
           (𝒪 Σ⦅𝓓⦆)
           (𝟎-𝔽𝕣𝕞 pe)
           ℱ
           ↑ˢ[ b , κᵇ ]
           ↑ˢ[ c , κᶜ ]

      Ⅱ = holds-gives-equal-⊤ pe fe (F ↑ˢ[ b , κᵇ ] ∧ₚ F ↑ˢ[ c , κᶜ ]) (κᵢ , κⱼ)

      † : F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ＝ ⊤
      † = F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]) ＝⟨ Ⅰ ⟩
          F ↑ˢ[ b , κᵇ ] ∧ₚ F ↑ˢ[ c , κᶜ ]          ＝⟨ Ⅱ ⟩
          ⊤                                         ∎

\end{code}

We now proceed with the case analysis.

Case 1: the upper bound of `b` and `c` exists.

\begin{code}

    case₁ : bounded-above 𝓓 (B𝓓 [ i ]) (B𝓓 [ j ]) holds
          → ∃ k ꞉ index (𝒦-in-point ℱ)
                , (𝒦-in-point ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (𝒦-in-point ℱ [ k ])
                × (𝒦-in-point ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (𝒦-in-point ℱ [ k ])
    case₁ υ = ∥∥-functor ‡₁ 𝒷ᵈ
     where
      𝓈 : has-sup (underlying-order 𝓓) (binary-family 𝓤 b c [_])
      𝓈 = bc (binary-family 𝓤 b c) υ

\end{code}

Thanks to bounded completeness, the fact that an upper bound exists means that
the least upper bound exists. We denote this by `d`.

\begin{code}

      d : ⟨ 𝓓 ⟩∙
      d = pr₁ 𝓈

      p : b ⊑⟨ 𝓓 ⟩ d
      p = pr₁ (pr₂ 𝓈) (inl ⋆)

      q : c ⊑⟨ 𝓓 ⟩ d
      q = pr₁ (pr₂ 𝓈) (inr ⋆)

      κᵈ : is-compact 𝓓 d
      κᵈ = sup-is-compact b c d κᵇ κᶜ (pr₂ 𝓈)

      𝒷ᵈ : (d ∈imageₚ (B𝓓 [_])) holds
      𝒷ᵈ = small-compact-basis-contains-all-compact-elements 𝓓 (B𝓓 [_]) scb d κᵈ

      ‡₁ : Σ k ꞉ index B𝓓 , B𝓓 [ k ] ＝ d
         → Σ k ꞉ index (𝒦-in-point ℱ) ,
                 ((𝒦-in-point ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ pr₁ k ]))
               × ((𝒦-in-point ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ pr₁ k ]))
      ‡₁ (k , ψ) = (k , ※) , ♠ , ♣
       where
        r : ↑ˢ[ d , κᵈ ] ＝ ↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ[𝓓] ] ↑ˢ[ c , κᶜ ]
        r = principal-filter-reflects-joins b c d κᵇ κᶜ (pr₂ 𝓈)

        ♥ : ↑ˢ[ d , κᵈ ] ∈ F
        ♥ = transport (λ - → - ∈ F) (r ⁻¹) μₘ

        ※ : ↑ˢ[ βₖ k ] ∈ F
        ※ = transport
             (λ - → ↑ˢ[ - ] ∈ F)
             (to-subtype-＝ (being-compact-is-prop 𝓓) (ψ ⁻¹))
             ♥

        -- Seems to be necessary for the termination of typechecking within a
        -- reasonable time
        abstract
         ♠ : (B𝓓 [ i ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ k ])
         ♠ = transport (λ - → (B𝓓 [ i ]) ⊑⟨ 𝓓 ⟩ -) (ψ ⁻¹) p

         ♣ : (B𝓓 [ j ]) ⊑⟨ 𝓓 ⟩ (B𝓓 [ k ])
         ♣ = transport (λ - → (B𝓓 [ j ]) ⊑⟨ 𝓓 ⟩ -) (ψ ⁻¹) q

\end{code}

Case 2: the upper bound of `b` and `c` _does not_ exist. We derive a
contradiction in this case.

\begin{code}

    case₂ : ¬ ((B𝓓 [ i ]) ↑[ 𝓓 ] (B𝓓 [ j ]) holds)
          → ∃ k ꞉ index (𝒦-in-point ℱ)
                , (𝒦-in-point ℱ [ i , κᵢ ]) ⊑⟨ 𝓓 ⟩ (𝒦-in-point ℱ [ k ])
                × (𝒦-in-point ℱ [ j , κⱼ ]) ⊑⟨ 𝓓 ⟩ (𝒦-in-point ℱ [ k ])
    case₂ ν = 𝟘-elim (⊥-is-not-⊤ ϟ)
     where

\end{code}

We have that `↑(b) ∧ ↑(c) ＝ 𝟎`, given by `not-bounded-lemma`.

\begin{code}

      β : ↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ] ＝ 𝟎[ 𝒪 Σ⦅𝓓⦆ ]
      β = not-bounded-lemma b c κᵇ κᶜ ν

\end{code}

Because the point `F` is a frame homomorphism, we have that

```
  F(↑b) ∧ F(↑c) ＝ F(↑b ∧ ↑c) ＝ F(𝟎)
```

Because we know that `F(↑b)` and `F(↑c)` hold, we know that `F(𝟎)` holds, which
is a contradiction since `F(𝟎) ＝ ⊥`.

\begin{code}

      Ⅰ = 𝟎-is-⊥ pe
      Ⅱ = frame-homomorphisms-preserve-bottom (𝒪 Σ⦅𝓓⦆) (𝟎-𝔽𝕣𝕞 pe) ℱ ⁻¹
      Ⅲ = ap F (β ⁻¹)
      Ⅳ = holds-gives-equal-⊤ pe fe (F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])) μₘ

      ϟ : ⊥ₚ ＝ ⊤
      ϟ = ⊥ₚ                                          ＝⟨ Ⅰ ⟩
          𝟎[ 𝟎-𝔽𝕣𝕞 pe ]                               ＝⟨ Ⅱ ⟩
          F 𝟎[ 𝒪 Σ⦅𝓓⦆ ]                               ＝⟨ Ⅲ ⟩
          F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ])   ＝⟨ Ⅳ ⟩
          ⊤                                           ∎

\end{code}

We now have everything required to record the proof that the family
`𝒦-in-point ℱ` is directed.

\begin{code}

 𝒦-in-point-is-directed : (ℱ : Point)
                        → is-directed (underlying-order 𝓓) (𝒦-in-point ℱ [_])
 𝒦-in-point-is-directed ℱ = 𝒦-in-point-is-inhabited ℱ
                          , closed-under-binary-upperbounds ℱ

\end{code}
