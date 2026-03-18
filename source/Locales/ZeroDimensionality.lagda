Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size

module Locales.ZeroDimensionality (pt : propositional-truncations-exist)
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


open import Locales.Frame            pt fe           hiding (is-directed-basis)
open import Locales.WayBelowRelation.Definition pt fe
open import Locales.Compactness.Definition pt fe
open import Locales.Complements      pt fe
open import Locales.PosetalAdjunction pt fe
open import Locales.InitialFrame     pt fe
open import Locales.Clopen           pt fe sr
open import Locales.SmallBasis       pt fe sr
open import Locales.Regular          pt fe sr
open import Locales.WellInside       pt fe sr

open Locale

\end{code}

The following is the definition of the notion of a _zero-dimensionality
structure_.

\begin{code}

zero-dimensionalᴰ : Frame 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
zero-dimensionalᴰ {𝓦 = 𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , directed-basis-forᴰ F ℬ
                   × consists-of-clopens F ℬ holds

\end{code}

We define some projections for the components of a ZD structure.

\begin{code}

basis-zd : (L : Frame 𝓤 𝓥 𝓦) → zero-dimensionalᴰ L → Fam 𝓦 ⟨ L ⟩
basis-zd L = pr₁

cover-index-zd : (L : Frame 𝓤 𝓥 𝓦) (zd : zero-dimensionalᴰ L)
               → ⟨ L ⟩ → Fam 𝓦 (index (basis-zd L zd))
cover-index-zd L zd U = pr₁ (pr₁ (pr₂ zd) U)

basis-zd-covers-are-directed : (L : Frame 𝓤 𝓥 𝓦) (zd : zero-dimensionalᴰ L)
                             → (U : ⟨ L ⟩)
                             → let
                                ℬ = basis-zd L zd
                                𝒥 = cover-index-zd L zd U
                               in
                                is-directed L ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
basis-zd-covers-are-directed L zd U = pr₂ (pr₂ (pr₁ (pr₂ zd) U))

basis-zd-covers-do-cover : (L : Frame 𝓤 𝓥 𝓦) (zd : zero-dimensionalᴰ L)
                         → (U : ⟨ L ⟩)
                         → let
                            ℬ = basis-zd L zd
                            𝒥 = cover-index-zd L zd U
                            open Joins (λ x y → x ≤[ poset-of L ] y)
                           in
                            (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
basis-zd-covers-do-cover L zd U = pr₁ (pr₂ (pr₁ (pr₂ zd) U))

basis-of-zero-dimensionalᴰ-frame : (L : Frame 𝓤 𝓥 𝓦)
                                 → zero-dimensionalᴰ L
                                 → Σ ℬ ꞉ Fam 𝓦 ⟨ L ⟩ , directed-basis-forᴰ L ℬ
basis-of-zero-dimensionalᴰ-frame L (ℬ , β , _) = ℬ , β

basis-zd-consists-of-clopens : (L : Frame 𝓤 𝓥 𝓦) (zd : zero-dimensionalᴰ L)
                             → let
                                ℬ = basis-zd L zd
                               in
                                consists-of-clopens L ℬ holds
basis-zd-consists-of-clopens L zd = pr₂ (pr₂ zd)

\end{code}

The notion of a zero-dimensional frame can then be defined simply as the
truncation of this structure.

\begin{code}

is-zero-dimensional : Frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-zero-dimensional F = ∥ zero-dimensionalᴰ F ∥Ω

\end{code}

\begin{code}

zero-dimensionalᴰ-implies-has-basis : (L : Frame 𝓤 𝓥 𝓦)
                                    → zero-dimensionalᴰ L → basisᴰ L
zero-dimensionalᴰ-implies-has-basis {𝓤} {𝓥} {𝓦} L zd = ℬ , †
 where
  open Joins (λ x y → x ≤[ poset-of L ] y)

  ℬ : Fam 𝓦 ⟨ L ⟩
  ℬ = basis-zd L zd

  † : basis-forᴰ L ℬ
  † U = 𝒥 , φ
   where
    𝒥 = cover-index-zd L zd U

    φ : (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    φ = basis-zd-covers-do-cover L zd U

zero-dimensionalᴰ-implies-has-directed-basis : (L : Frame 𝓤 𝓥 𝓦)
                                    → zero-dimensionalᴰ L → directed-basisᴰ L
zero-dimensionalᴰ-implies-has-directed-basis {𝓤} {𝓥} {𝓦} L zd = ℬ , †
 where
  open Joins (λ x y → x ≤[ poset-of L ] y)

  ℬ : Fam 𝓦 ⟨ L ⟩
  ℬ = basis-zd L zd

  † : directed-basis-forᴰ L ℬ
  † U = 𝒥 , φ , d
   where
    𝒥 = cover-index-zd L zd U

    φ : (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    φ = basis-zd-covers-do-cover L zd U

    d : is-directed L ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
    d = basis-zd-covers-are-directed L zd U

\end{code}

\begin{code}

zero-dimensional-locales-are-regular : (F : Frame 𝓤 𝓥 𝓦)
                                     → is-zero-dimensional F holds
                                     → is-regular F holds
zero-dimensional-locales-are-regular {𝓦 = 𝓦} F =
 ∥∥-rec (holds-is-prop (is-regular F)) γ
  where
   open Joins (λ x y → x ≤[ poset-of F ] y)

   γ : zero-dimensionalᴰ F → is-regular F holds
   γ zd@(ℬ , β , ξ) = ∣ ℬ , δ ∣
    where
     δ : Π U ꞉ ⟨ F ⟩ ,
          Σ J ꞉ Fam 𝓦 (index ℬ) ,
             (U is-lub-of (fmap-syntax (_[_] ℬ) J)) holds
           × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] U) holds)
     δ U = 𝒥 , c , ε
      where
       𝒥 = cover-index-zd F zd U

       c : (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
       c = basis-zd-covers-do-cover F zd U

       ε : Π i ꞉ index 𝒥 , (ℬ [ 𝒥 [ i ] ] ⋜[ F ] U) holds
       ε i = ↑↑-is-upwards-closed F ∣ ξ (𝒥 [ i ]) ∣ (pr₁ c i)
        where
         η : ((ℬ [ 𝒥 [ i ] ]) ≤[ poset-of F ] (ℬ [ 𝒥 [ i ] ])) holds
         η = ≤-is-reflexive (poset-of F) (ℬ [ 𝒥 [ i ] ])


\end{code}

\begin{code}

compacts-are-clopen-in-zd-locales : (X : Locale 𝓤 𝓥 𝓦)
                                  → is-zero-dimensional (𝒪 X) holds
                                  → (U : ⟨ 𝒪 X ⟩)
                                  → (is-compact-open X U ⇒ is-clopen (𝒪 X) U) holds
compacts-are-clopen-in-zd-locales X 𝕫 =
 compacts-are-clopen-in-regular-frames X ρ
  where
   ρ : is-regular (𝒪 X) holds
   ρ = zero-dimensional-locales-are-regular (𝒪 X) 𝕫

\end{code}
