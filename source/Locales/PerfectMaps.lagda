Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
-- open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
-- open import UF.Univalence
open import UF.UA-FunExt
-- open import MLTT.List hiding ([_])

module Locales.PerfectMaps (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                           where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame pt fe
open import Locales.WayBelow pt fe
open import Locales.Compactness pt fe
open import Slice.Family
-- open import UF.Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import UF.Logic
open import UF.SubtypeClassifier
-- open import UF.Subsingletons

open AllCombinators pt fe
open PropositionalTruncation pt

open import Locales.GaloisConnection pt fe

open import Locales.InitialFrame pt fe

open Locale

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
