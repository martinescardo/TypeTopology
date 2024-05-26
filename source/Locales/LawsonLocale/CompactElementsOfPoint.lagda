--------------------------------------------------------------------------------
author:         Ayberk Tosun
date-started:   2024-03-15
date-completed: 2024-05-13
--------------------------------------------------------------------------------

Let D be a Scott domain satisfying the condition that the existence of binary
upper bounds of compact elements is decidable. Denote by σ(D) the Scott locale
of domain D.

By a “point” of D, we mean a continuous map 𝟏 → σ(D) (where 𝟏 denotes the
terminal locale), or equivalently, a frame homomorphism 𝒪(σ(D)) → Ω.

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
open import Locales.Point.Definition pt fe
open import Locales.Point.Properties pt fe 𝓤 pe hiding (𝟏L)
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

This is the locale given by the frame of opens `Ω∙`.

\begin{code}

 Ω∙ : Frame (𝓤 ⁺) 𝓤 𝓤
 Ω∙ = 𝒪 (𝟏Loc pe)

\end{code}

For the reader who might not be familiar, this is the locale defined by the
frame of opens `Ω`.

\begin{code}

 _ : ⟨ 𝒪 𝟏L ⟩ ＝ Ω 𝓤
 _ = refl

\end{code}

By a point of locale, we mean a continuous map from `𝟏L` into `X` as mentioned
in the preamble.

\begin{code}

 Point : 𝓤 ⁺  ̇
 Point = 𝟏L ─c→  X

\end{code}

This is definitionally the same thing as a frame homomorphism `𝒪(X) → Ω`.

\begin{code}

 Point′ : 𝓤 ⁺  ̇
 Point′ = 𝒪 X ─f→ Ω∙

 _ : Point ＝ Point′
 _ = refl

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

We now write down the family of compact elements whose principal ideals fall in
a given point `ℱ`. We denote this `𝒦-in-point ℱ`.

\begin{code}

 𝒦-in-point : Point → Fam 𝓤 ⟨ 𝓓 ⟩∙
 𝒦-in-point (F , _) =
  ⁅ B𝓓 [ i ] ∣ (i , _) ∶ (Σ i ꞉ index B𝓓 , ↑ˢ[ βₖ i ] ∈ₚ F holds) ⁆

\end{code}

Ideally, the name here would be `𝒦-with-principal-ideals-in-point` but this is
too long, which is why we use the name `𝒦-in-point`.

It makes sense to me to think of this as the family of compact approximants to
the given point, but I'm not sure this geometric view is accurate at the time of
writing. I will improve this name in the future as my understanding of the
underlying geometric intuition increases.

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

Before we proceed to proving that the family `𝒦-in-point` is always
semidirected, we prove a lemma that we will use in the proof. The reader not
interested in the lemma may jump directly to the proof which is implemented in
the function called `𝒦-in-point-is-semidirected`.

The lemma is simply the fact that
```
    ↑b ∈ F and ↑c ∈ F    implies    (↑b ∧ ↑c) ∈ F
```
for any two compact elements `b` and `c` of `𝓓`.

This is actually something already implemented in the `Locales.Point` directory,
where it is shown that points correspond to completely prime filters.

\begin{code}

 point-preserves-meets : (ℱ@(F , _) : Point) (c d : ⟨ 𝓓 ⟩∙)
                       → (κc : is-compact 𝓓 c)
                       → (κd : is-compact 𝓓 d)
                       → (F ↑ˢ[ (c , κc) ]
                       ⇒ F ↑ˢ[ (d , κd) ]
                       ⇒ F (↑ˢ[ c , κc ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ d , κd ])) holds
 point-preserves-meets ℱ@(F , _) c d κc κd =
  point-is-closed-under-∧ ↑ˢ[ c , κc ] ↑ˢ[ d , κd ]
   where
    open DefnOfCPF Σ⦅𝓓⦆
    open Pointᵣ (to-pointᵣ Σ⦅𝓓⦆ (𝔰 Σ⦅𝓓⦆ ℱ))

\end{code}

The family `𝒦-in-point` is semidirected.

\begin{code}

 𝒦-in-point-is-semidirected
  : (ℱ : Point)
  → is-semidirected (underlying-order 𝓓) (𝒦-in-point ℱ [_])
 𝒦-in-point-is-semidirected ℱ (i , κᵢ) (j , κⱼ) =

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
        ♥ = transport
             (λ - → - ∈ F)
             (r ⁻¹)
             (point-preserves-meets ℱ b c κᵇ κᶜ κᵢ κⱼ)

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
      Ⅳ = holds-gives-equal-⊤
           pe
           fe
           (F (↑ˢ[ b , κᵇ ] ∧[ 𝒪 Σ⦅𝓓⦆ ] ↑ˢ[ c , κᶜ ]))
           (point-preserves-meets ℱ b c κᵇ κᶜ κᵢ κⱼ)

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
                          , 𝒦-in-point-is-semidirected ℱ

\end{code}

Added on 2024-05-23.

\begin{code}

 𝒦-in-point↑ : (ℱ : Point) → Fam↑
 𝒦-in-point↑ ℱ = 𝒦-in-point ℱ , 𝒦-in-point-is-directed ℱ

\end{code}
