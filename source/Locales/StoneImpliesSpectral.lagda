Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Size

module Locales.StoneImpliesSpectral (pt : propositional-truncations-exist)
                                    (fe : Fun-Ext)
                                    (sr : Set-Replacement pt)              where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Importations of other locale theory modules.

\begin{code}

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame            pt fe
open import Locales.WayBelow         pt fe
open import Locales.Compactness      pt fe
open import Locales.Complements      pt fe
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame     pt fe
open import Locales.Spectrality        pt fe
open import Locales.ZeroDimensionality pt fe sr
open import Locales.Stone              pt fe sr
open import Locales.SmallBasis         pt fe sr
open import Locales.Clopen             pt fe

open Locale

\end{code}

\begin{code}

stoneᴰ-implies-spectralᴰ : (X : Locale 𝓤 𝓥 𝓦) → stoneᴰ X → spectralᴰ X
stoneᴰ-implies-spectralᴰ {_} {_} {𝓦} X (κₓ , zdₓ) = ℬ , β , {!!}
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
  ℬ = basis-zd (𝒪 X) zdₓ

  β : directed-basis-forᴰ (𝒪 X) ℬ
  β U = cover-index-zd (𝒪 X) zdₓ U , (†₁ , {!!}) , d
   where
    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = cover-index-zd (𝒪 X) zdₓ U

    †₁ : (U is-an-upper-bound-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    †₁ j = {!!}

    d : is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
    d = basis-zd-covers-are-directed (𝒪 X) zdₓ U

\end{code}

\begin{code}

{--

stone-locales-are-spectral : (X : Locale 𝓤 𝓥 𝓦)
                           → (is-stone X ⇒ is-spectral X) holds
stone-locales-are-spectral X σ@(κ , ζ) =
 ∥∥-rec (holds-is-prop (is-spectral X)) ♣ ζ
  where
   F = 𝒪 X

   open Meets (λ x y → x ≤[ poset-of F ] y) hiding (is-top)

   ♣ : zero-dimensionalᴰ F → is-spectral X holds
   ♣ (ℬ , δ , ψ) = {! ∣ ℬ , δ , ϑ , † ∣ !}
    where
     ϑ : consists-of-compact-opens X ℬ holds
     ϑ is = {! pr₁ (clopen-iff-compact-in-stone-frame F σ (ℬ [ is ])) (ψ is) !}

     τ : ∥ Σ i ꞉ index ℬ , 𝟏[ F ] ＝ ℬ [ i ] ∥
     τ = {! compact-opens-are-basic-in-compact-frames F ℬ δ κ 𝟏[ F ] κ !}

     †₁ :  {!!}
     †₁ = ∥∥-rec (holds-is-prop (contains-top F ℬ)) ‡₁ τ
      where
       ‡₁ : (Σ i ꞉ index ℬ , 𝟏[ F ] ＝ ℬ [ i ]) → contains-top (𝒪 X) ℬ holds
       ‡₁ (i , p) = ∣ i , transport (λ - → is-top F - holds) p (𝟏-is-top F) ∣

     †₂ : closed-under-binary-meets F ℬ holds
     †₂ i j = ∥∥-rec ∃-is-prop ‡₂ υ
      where
       χ : is-clopen F (ℬ [ i ] ∧[ F ] ℬ [ j ]) holds
       χ = {! clopens-are-closed-under-∧ F (ℬ [ i ]) (ℬ [ j ]) (ψ i) (ψ j) !}

       υ : ∥ Σ k ꞉ index ℬ , (ℬ [ i ]) ∧[ F ] (ℬ [ j ]) ＝ ℬ [ k ] ∥
       υ = {! clopens-are-basic-in-stone-locales F σ ℬ δ (ℬ [ i ] ∧[ F ] ℬ [ j ]) χ !}

       ‡₂ : (Σ k ꞉ index ℬ , (ℬ [ i ]) ∧[ F ] (ℬ [ j ]) ＝ ℬ [ k ])
          → ∥ Σ k ꞉ index ℬ , ((ℬ [ k ]) is-glb-of (ℬ [ i ] , ℬ [ j ])) holds ∥
       ‡₂ (k , p) = ∣ k , ‡₃ ∣
        where
         ρ₁ = ∧[ F ]-lower₁ (ℬ [ i ]) (ℬ [ j ])
         ρ₂ = ∧[ F ]-lower₂ (ℬ [ i ]) (ℬ [ j ])
         ρ₃ = λ { (z , p , q) → ∧[ F ]-greatest (ℬ [ i ]) (ℬ [ j ]) z p q }

         ‡₃ : ((ℬ [ k ]) is-glb-of (ℬ [ i ] , ℬ [ j ])) holds
         ‡₃ = transport
               (λ - → (- is-glb-of (ℬ [ i ] , ℬ [ j ])) holds)
               p
               ((ρ₁ , ρ₂) , ρ₃)

     † : closed-under-finite-meets F ℬ holds
     † = †₁ , †₂

--}

\end{code}
