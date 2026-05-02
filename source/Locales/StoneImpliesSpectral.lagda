Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size

module Locales.StoneImpliesSpectral (pt : propositional-truncations-exist)
                                    (fe : Fun-Ext)
                                    (sr : Set-Replacement pt) where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import Slice.Family
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Importations of other locale theory modules.

\begin{code}

open import Locales.Clopen pt fe sr
open import Locales.Compactness.Definition pt fe
open import Locales.Complements pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.Frame pt fe
open import Locales.ScottContinuity pt fe sr
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import Locales.WayBelowRelation.Definition pt fe
open import Locales.WellInside pt fe sr
open import Locales.ZeroDimensionality pt fe sr

open Locale

\end{code}

The well inside relation implies the way below relation.

\begin{code}

⋜₀-implies-≪-in-compact-frames : (X : Locale 𝓤 𝓥 𝓦)
                               → is-compact X holds
                               → (U V : ⟨ 𝒪 X ⟩)
                               → U ⋜₀[ 𝒪 X ] V
                               → (U ≪[ 𝒪 X ] V) holds
⋜₀-implies-≪-in-compact-frames {𝓦 = 𝓦} X κ U V (W , c₁ , c₂) S d q =
 ∥∥-rec ∃-is-prop θ ζ
  where
   F = 𝒪 X
   open PosetNotation  (poset-of (𝒪 X))
   open PosetReasoning (poset-of (𝒪 X))

   T : Fam 𝓦 ⟨ 𝒪 X ⟩
   T = ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆

   δ : (𝟏[ F ] ≤ (⋁[ F ] T)) holds
   δ =
    𝟏[ F ]                           ＝⟨ c₂ ⁻¹                              ⟩ₚ
    V ∨[ F ] W                       ≤⟨ ∨[ F ]-left-monotone q             ⟩
    (⋁[ F ] S) ∨[ F ] W              ＝⟨ ∨[ F ]-is-commutative (⋁[ F ] S) W ⟩ₚ
    W ∨[ F ] (⋁[ F ] S)              ＝⟨ ∨-is-scott-continuous-eq (𝒪 X) W S d   ⟩ₚ
    ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆  ■

   ε : ((W ∨[ F ] (⋁[ F ] S)) ≤ (⋁[ F ] T)) holds
   ε = W ∨[ F ] (⋁[ F ] S)              ≤⟨ 𝟏-is-top F (W ∨[ F ] (⋁[ F ] S)) ⟩
       𝟏[ F ]                           ≤⟨ δ                                ⟩
       ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆  ■

   up : (Ɐ i , Ɐ j ,
           Ǝ k , (T [ i ] ≤ T [ k ]) holds × (T [ j ] ≤ T [ k ]) holds) holds
   up i j = ∥∥-rec ∃-is-prop r (pr₂ d i j)
    where
     r  = λ (k , p , q) → ∣ k , ∨[ F ]-right-monotone p , ∨[ F ]-right-monotone q ∣

   T-is-directed : (is-directed F ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
   T-is-directed = pr₁ d , up

   ζ : ∥ Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] (S [ i ]))) holds ∥
   ζ = κ ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ T-is-directed δ

   θ : Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] S [ i ])) holds
     → ∃ i ꞉ index S , (U ≤ S [ i ]) holds
   θ (i , p) = ∣ i , well-inside-implies-below F U (S [ i ]) ∣ W , c₁ , ι ∣ ∣
    where
     η = 𝟏[ F ]              ≤⟨ p                                 ⟩
         W ∨[ F ] (S [ i ])  ＝⟨ ∨[ F ]-is-commutative W (S [ i ]) ⟩ₚ
         (S [ i ]) ∨[ F ] W  ■

     ι = only-𝟏-is-above-𝟏 F ((S [ i ]) ∨[ F ] W) η

\end{code}

\begin{code}

⋜-implies-≪-in-compact-frames : (X : Locale 𝓤 𝓥 𝓦)
                              → is-compact X holds
                              → (U V : ⟨ 𝒪 X ⟩)
                              → (U ⋜[ 𝒪 X ] V ⇒ U ≪[ 𝒪 X ] V) holds
⋜-implies-≪-in-compact-frames X κ U V =
 ∥∥-rec (holds-is-prop (U ≪[ 𝒪 X ] V)) (⋜₀-implies-≪-in-compact-frames X κ U V)

\end{code}

Clopens are compact in compact locales.

\begin{code}

clopens-are-compact-in-compact-locales : (X : Locale 𝓤 𝓥 𝓦)
                                       → is-compact X holds
                                       → (U : ⟨ 𝒪 X ⟩)
                                       → (is-clopen (𝒪 X) U
                                       ⇒  is-compact-open X U) holds
clopens-are-compact-in-compact-locales X κ U =
 ⋜₀-implies-≪-in-compact-frames X κ U U

\end{code}

Clopens are basic in compact locales.

\begin{code}

clopens-are-basic : (X : Locale 𝓤 𝓥 𝓦) (st : stoneᴰ X)
                  → (𝒷 : directed-basisᴰ (𝒪 X))
                  → (K : ⟨ 𝒪 X ⟩)
                  → (is-clopen (𝒪 X) K ⇒ is-basic X K 𝒷) holds
clopens-are-basic X (κ , _) 𝒷 K 𝕔 =
 compact-opens-are-basic X 𝒷 K (clopens-are-compact-in-compact-locales X κ K 𝕔)

\end{code}

\begin{code}

stoneᴰ-implies-spectralᴰ : (X : Locale 𝓤 𝓥 𝓦) → stoneᴰ X → spectralᴰ X
stoneᴰ-implies-spectralᴰ {_} {_} {𝓦} X (κₓ , zdₓ) = ℬ , β , κ , μ
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
  ℬ = basis-zd (𝒪 X) zdₓ

  φ : consists-of-clopens (𝒪 X) ℬ holds
  φ = basis-zd-consists-of-clopens (𝒪 X) zdₓ

  β : directed-basis-forᴰ (𝒪 X) ℬ
  β U = cover-index-zd (𝒪 X) zdₓ U , † , d
   where
    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = cover-index-zd (𝒪 X) zdₓ U

    † : (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    † = basis-zd-covers-do-cover (𝒪 X) zdₓ U

    d : is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
    d = basis-zd-covers-are-directed (𝒪 X) zdₓ U

  X-is-compact : is-compact X holds
  X-is-compact =
   clopens-are-compact-in-compact-locales X κₓ 𝟏[ 𝒪 X ] (𝟏-is-clopen (𝒪 X))

  κ : consists-of-compact-opens X ℬ holds
  κ i = clopens-are-compact-in-compact-locales X κₓ (ℬ [ i ]) 𝕔
   where
    𝕔 : is-clopen (𝒪 X) (ℬ [ i ]) holds
    𝕔 = basis-zd-consists-of-clopens (𝒪 X) zdₓ i

  μ₀ : contains-top (𝒪 X) ℬ holds
  μ₀ = ∥∥-rec
        (holds-is-prop (contains-top (𝒪 X) ℬ))
        (λ { (j , p) → ∣ j , transport (λ - → is-top (𝒪 X) - holds) (p ⁻¹) (𝟏-is-top (𝒪 X)) ∣})
        (clopens-are-basic X (κₓ , zdₓ) (ℬ , β) 𝟏[ 𝒪 X ] (𝟏-is-clopen (𝒪 X)))

  open Meets (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  μ₂ : closed-under-binary-meets (𝒪 X) ℬ holds
  μ₂ i j = ∥∥-rec ∃-is-prop † ξ
   where
    ν : is-clopen (𝒪 X) (ℬ [ i ] ∧[ 𝒪 X ] ℬ [ j ]) holds
    ν = clopens-are-closed-under-∧ (𝒪 X) (ℬ [ i ]) (ℬ [ j ]) (φ i) (φ j)

    ξ : is-basic X (ℬ [ i ] ∧[ 𝒪 X ] ℬ [ j ]) (ℬ , β) holds
    ξ = clopens-are-basic X (κₓ , zdₓ) (ℬ , β) (ℬ [ i ] ∧[ 𝒪 X ] ℬ [ j ]) ν

    † : Σ k ꞉ index ℬ , ℬ [ k ] ＝ ℬ [ i ] ∧[ 𝒪 X ] ℬ [ j ]
      → (Ǝ k ꞉ index ℬ , ((ℬ [ k ]) is-glb-of (ℬ [ i ] , ℬ [ j ])) holds) holds
    † (k , p) = ∣ k , ∧[ 𝒪 X ]-is-glb⋆ p ∣

  μ : closed-under-finite-meets (𝒪 X) ℬ holds
  μ = μ₀ , μ₂

\end{code}

`stoneᴰ X` implies that `X` is spectral.

\begin{code}

stone-locales-are-spectral : (X : Locale 𝓤 𝓥 𝓦) → stoneᴰ X → is-spectral X holds
stone-locales-are-spectral X σ@(κ , ζ) = spectralᴰ-gives-spectrality X σᴰ
 where
  σᴰ : spectralᴰ X
  σᴰ = stoneᴰ-implies-spectralᴰ X σ

\end{code}

Added on 2024-08-11.

\begin{code}

stoneᴰ-locales-are-compact : (X : Locale 𝓤 𝓥 𝓦)
                           → stoneᴰ X → is-compact X holds
stoneᴰ-locales-are-compact X (κ , _) = κ

\end{code}

\begin{code}

module continuous-maps-of-stone-locales
        (X : Locale 𝓤 𝓥 𝓥)
        (Y : Locale 𝓤 𝓥 𝓥)
        (𝕤₁ : stoneᴰ X)
        (𝕤₂ : stoneᴰ Y)
       where

 open ContinuousMaps

 κ₁ : is-compact X holds
 κ₁ = stoneᴰ-locales-are-compact X 𝕤₁

 κ₂ : is-compact Y holds
 κ₂ = stoneᴰ-locales-are-compact Y 𝕤₂

 zd₂ : zero-dimensionalᴰ (𝒪 Y)
 zd₂ = pr₂ 𝕤₂

 continuous-maps-between-stone-locales-are-spectral
  : (f : X ─c→ Y)
  → is-spectral-map Y X f holds
 continuous-maps-between-stone-locales-are-spectral 𝒻 K κ =
  clopens-are-compact-in-compact-locales X κ₁ (𝒻 ⋆∙ K) ϑ
   where
    open ContinuousMapNotation X Y

    ψ : is-clopen (𝒪 Y) K holds
    ψ = compacts-are-clopen-in-zd-locales Y ∣ zd₂ ∣ K κ

    K' : ⟨ 𝒪 Y ⟩
    K' = pr₁ ψ

    χ : is-boolean-complement-of (𝒪 Y) K' K holds
    χ = pr₂ ψ

    χ' : is-boolean-complement-of (𝒪 Y) K K' holds
    χ' = complementation-is-symmetric (𝒪 Y) K' K χ

    † : is-boolean-complement-of (𝒪 X) (𝒻 ⋆∙ K') (𝒻 ⋆∙ K) holds
    † = frame-homomorphisms-preserve-complements (𝒪 Y) (𝒪 X) (_⋆ 𝒻) χ'

    ϑ : is-clopen (𝒪 X) (𝒻 ⋆∙ K) holds
    ϑ = 𝒻 ⋆∙ K' , †

\end{code}
