Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.PerfectMaps (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                           where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Compactness.Definition pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.PosetalAdjunction pt fe
open import Locales.Spectrality.Properties     pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.WayBelowRelation.Definition pt fe
open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open ContinuousMaps
open FrameHomomorphismProperties
open Locale
open PropositionalTruncation pt

\end{code}

\begin{code}

module SpectralMaps (X : Locale 𝓤' 𝓥 𝓥) (Y : Locale 𝓤 𝓥 𝓥) where

 is-spectral-map : (X ─c→ Y) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⁺)
 is-spectral-map (f , _) =
  Ɐ U ꞉ ⟨ 𝒪 Y ⟩ , is-compact-open Y U  ⇒ is-compact-open X (f U)

module PerfectMaps (X : Locale 𝓤 𝓥 𝓥) (Y : Locale 𝓤' 𝓥 𝓥)
                                      (𝒷 : has-basis (𝒪 Y) holds) where

 open AdjointFunctorTheorem pt fe X Y 𝒷
 open ContinuousMapNotation X Y

\end{code}

A continuous map `f : X → Y` is called *perfect* if its right adjoint is
Scott-continuous.

\begin{code}

 is-perfect-map : (X ─c→ Y) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⁺)
 is-perfect-map f = is-scott-continuous (𝒪 X) (𝒪 Y) (pr₁ (right-adjoint-of f))

\end{code}

\begin{code}

\end{code}

Perfect maps preserve the way below relation.

\begin{code}

 perfect-preserves-way-below : (𝒻 : X ─c→ Y)
                             → is-perfect-map 𝒻 holds
                             → (U V : ⟨ 𝒪 Y ⟩)
                             → (U ≪[ 𝒪 Y ] V) holds
                             → (𝒻 ⋆∙ U ≪[ 𝒪 X ] 𝒻 ⋆∙ V) holds
 perfect-preserves-way-below f φ U V ϑ S δ p = γ
  where
   open GaloisConnectionBetween (poset-of (𝒪 Y)) (poset-of (𝒪 X))
   open PosetReasoning (poset-of (𝒪 Y))

   T : Fam 𝓥 ⟨ 𝒪 Y ⟩
   T = ⁅ f ⁎· V ∣ V ε S ⁆

   ζ₁ : (V ≤[ poset-of (𝒪 Y) ] (f ⁎· (⋁[ 𝒪 X ] S))) holds
   ζ₁ = adjunction-inequality-forward f (join-of (𝒪 X) S) V p

   ζ₂ : (V ≤[ poset-of (𝒪 Y) ] (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆)) holds
   ζ₂ = V                             ≤⟨ ζ₁ ⟩
        f ⁎· (⋁[ 𝒪 X ] S)             ＝⟨ †  ⟩ₚ
        ⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆   ■
         where
          † = scott-continuous-join-eq (𝒪 X) (𝒪 Y) (f ⁎·_) φ S δ

   T-is-directed : is-directed (𝒪 Y) T holds
   T-is-directed =
    monotone-image-on-directed-family-is-directed (𝒪 X) (𝒪 Y) S δ (f ⁎·_) μ
     where
      μ : is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 Y)) (f ⁎·_) holds
      μ = pr₂ (right-adjoint-of f)

   γ : (Ǝ k ꞉ index S , ((f ⋆∙ U) ≤[ poset-of (𝒪 X) ] (S [ k ])) holds) holds
   γ = ∥∥-rec ∃-is-prop ϵ (ϑ T T-is-directed ζ₂)
    where
     ϵ : _
     ϵ (k , q) = ∣ k , † ∣
      where
       † : ((f ⋆∙ U) ≤[ poset-of (𝒪 X) ] (S [ k ])) holds
       † = adjunction-inequality-backward f (S [ k ]) U q

\end{code}

\begin{code}

 compact-codomain-of-perfect-map-implies-compact-domain : (𝒻 : X ─c→ Y)
                                                        → is-perfect-map 𝒻 holds
                                                        → is-compact Y holds
                                                        → is-compact X holds
 compact-codomain-of-perfect-map-implies-compact-domain 𝒻@(f , φ , _) p κ = γ
  where
   β : (f 𝟏[ 𝒪 Y ] ≪[ 𝒪 X ] f 𝟏[ 𝒪 Y ]) holds
   β = perfect-preserves-way-below 𝒻 p 𝟏[ 𝒪 Y ] 𝟏[ 𝒪 Y ] κ

   γ : (𝟏[ 𝒪 X ] ≪[ 𝒪 X ] 𝟏[ 𝒪 X ]) holds
   γ = transport (λ - → (- ≪[ 𝒪 X ] -) holds) φ β

\end{code}

\begin{code}

 open SpectralMaps X Y

 perfect-maps-are-spectral : (f : X ─c→ Y)
                           → (is-perfect-map f ⇒ is-spectral-map f) holds
 perfect-maps-are-spectral 𝒻@(f , _) φ U κ =
  perfect-preserves-way-below 𝒻 φ U U κ

\end{code}

\begin{code}

 open Joins (λ x y → x ≤[ poset-of (𝒪 Y) ] y)

 scott-continuous-join-eq⁻ : (h : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Y ⟩)
                           → ((S : Fam 𝓥 ⟨ 𝒪 X ⟩)
                              → is-directed (𝒪 X) S holds
                              → h (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝒪 Y ] ⁅ h V ∣ V ε S ⁆)
                           → is-scott-continuous (𝒪 X) (𝒪 Y) h holds
 scott-continuous-join-eq⁻ h φ S δ =
  transport
   (λ - → (- is-lub-of ⁅ h V ∣ V ε S ⁆) holds)
   (φ S δ ⁻¹)
   (⋁[ 𝒪 Y ]-upper ⁅ h V ∣ V ε S ⁆ , ⋁[ 𝒪 Y ]-least ⁅ h V ∣ V ε S ⁆)

 open GaloisConnectionBetween (poset-of (𝒪 Y)) (poset-of (𝒪 X))

 spectral-maps-are-perfect : is-spectral Y holds
                           → (f : X ─c→ Y)
                           → (is-spectral-map f ⇒ is-perfect-map f) holds
 spectral-maps-are-perfect 𝕤 f σ S δ = scott-continuous-join-eq⁻ f₊ † S δ
  where
   open PosetNotation (poset-of (𝒪 X))
   open PosetNotation (poset-of (𝒪 Y)) renaming (_≤_ to _≤y_)

   infix -2 _≤∙_
   _≤∙_ = _≤y_

   f₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 Y)
   f₊ₘ = right-adjoint-of f

   f⁺ : ⟨ 𝒪 Y ⟩ → ⟨ 𝒪 X ⟩
   f⁺ = f ⋆∙_

   f⁺ₘ : poset-of (𝒪 Y) ─m→ poset-of (𝒪 X)
   f⁺ₘ = f⁺ , frame-morphisms-are-monotonic (𝒪 Y) (𝒪 X) f⁺ (pr₂ f)

   f₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Y ⟩
   f₊ = f ⁎·_

   𝕒 : (f⁺ₘ ⊣ f₊ₘ) holds
   𝕒 = f₊-is-right-adjoint-of-f⁺ f

   † : (S : Fam 𝓥 ⟨ 𝒪 X ⟩)
     → is-directed (𝒪 X) S holds
     → f ⁎· (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆
   † S δ = ≤-is-antisymmetric (poset-of (𝒪 Y)) †₁ †₂
    where
     open PosetReasoning (poset-of (𝒪 X))
     open PosetReasoning (poset-of (𝒪 Y)) using    ()
                                          renaming (_≤⟨_⟩_ to _≤⟨_⟩∙_;
                                                    _■ to _𝔔𝔈𝔇)

     ϑ : ((f ⁎· (⋁[ 𝒪 X ] S)) ≤ₖ[ Y ] (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆)) holds
     ϑ (K , κ) p = ∥∥Ω-rec ※ (κ′ S δ q)
      where
       κ′ : is-compact-open X (f⁺ K) holds
       κ′ = σ K κ

       q : (f⁺ K ≤ (⋁[ 𝒪 X ] S)) holds
       q = adjunction-inequality-backward f (⋁[ 𝒪 X ] S) K p

       ※ : Σ k ꞉ index S , (f⁺ K ≤ S [ k ]) holds
         → (K ≤∙ ⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆) holds
       ※ (k , p) =
        K                           ≤⟨ Ⅰ  ⟩∙
        f ⁎· (S [ k ])              ≤⟨ Ⅱ ⟩∙
        ⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆ 𝔔𝔈𝔇
         where
          Ⅰ = adjunction-inequality-forward f (S [ k ]) K p
          Ⅱ = ⋁[ 𝒪 Y ]-upper ⁅ f ⁎· V ∣ V ε S ⁆ k

     †₁ : (f ⁎· (⋁[ 𝒪 X ] S) ≤∙ ⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆) holds
     †₁ =
      spectral-yoneda Y 𝕤 (f ⁎· (⋁[ 𝒪 X ] S)) (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆) ϑ

     ‡₂ : (f ⋆∙ (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆) ≤ (⋁[ 𝒪 X ] S)) holds
     ‡₂ =
      f ⋆∙ (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆)       ＝⟨ Ⅰ ⟩ₚ
      ⋁[ 𝒪 X ] ⁅ f ⋆∙ (f ⁎· V) ∣ V ε S ⁆       ≤⟨ Ⅱ ⟩
      ⋁[ 𝒪 X ] ⁅ V ∣ V ε S ⁆                   ■
       where
        ※ : cofinal-in (𝒪 X) ⁅ f ⋆∙ (f ⁎· V) ∣ V ε S ⁆ S holds
        ※ i = ∣ i , counit f⁺ₘ f₊ₘ 𝕒 (S [ i ]) ∣

        Ⅰ = continuity-of X Y f ⁅ f ⁎· V ∣ V ε S ⁆
        Ⅱ = cofinal-implies-join-covered
             (𝒪 X)
             ⁅ f ⋆∙ (f ⁎· V) ∣ V ε S ⁆
             S
             ※

     †₂ : (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆ ≤∙ f ⁎· (⋁[ 𝒪 X ] S)) holds
     †₂ = adjunction-inequality-forward
           f
           (⋁[ 𝒪 X ] S)
           (⋁[ 𝒪 Y ] ⁅ f ⁎· V ∣ V ε S ⁆)
           ‡₂


\end{code}
