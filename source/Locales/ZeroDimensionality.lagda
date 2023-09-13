Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Size

module Locales.ZeroDimensionality (pt : propositional-truncations-exist)
                                  (fe : Fun-Ext)
                                  (sr : Set-Replacement pt) where

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

open import Locales.Frame            pt fe           hiding (is-directed-basis)
open import Locales.WayBelowRelation.Definition pt fe
open import Locales.Compactness      pt fe
open import Locales.Complements      pt fe
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame     pt fe
open import Locales.Clopen           pt fe
open import Locales.SmallBasis       pt fe sr

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
