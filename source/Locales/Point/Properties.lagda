Ayberk Tosun

Started on 22 September 2023.

This module contains the proof that points of a locale are in bijection with the
completely prime filters.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons

module Locales.Point.Properties (pt : propositional-truncations-exist)
                                (fe : Fun-Ext)
                                (𝓤  : Universe)
                                (pe : propext 𝓤)
                                 where

open import Slice.Family
open import UF.Powerset
-- open import Slice.Family
open import UF.SubtypeClassifier

open import Locales.Frame            pt fe
open import Locales.Point.Definition pt fe
open import Locales.InitialFrame     pt fe

open PropositionalTruncation pt

open DefnOfCPF

open Locale

open AllCombinators pt fe

\end{code}

We by `𝟏L` the terminal locale.

\begin{code}

𝟏L : Locale (𝓤 ⁺) 𝓤 𝓤
𝟏L = 𝟏Loc pe

\end{code}

\begin{code}

𝔯₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 𝟏L ⟩
𝔯₀ X (ϕ , cpf) U = ϕ U

𝔰₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → (𝟏L ─c→ X) → (⟨ 𝒪 X ⟩ → Ω 𝓤)
𝔰₀ X 𝒻 U = 𝒻 ⋆∙ U
 where
  open ContinuousMapNotation 𝟏L X using (_⋆∙_)

\end{code}

\begin{code}

𝔯₀-gives-frame-homomorphism : (X : Locale (𝓤 ⁺) 𝓤 𝓤) (x : Point X)
                            → is-a-frame-homomorphism (𝒪 X) (𝒪 𝟏L) (𝔯₀ X x) holds
𝔯₀-gives-frame-homomorphism X 𝓍@(ϕ , cpf) = α , β , γ
 where
  open Pointᵣ
  open Joins (λ U V → U ≤[ poset-of (𝒪 𝟏L) ] V)

  𝓍′ : Pointᵣ X
  𝓍′ = to-pointᵣ X 𝓍

  τ : (𝟏[ 𝒪 X ] ∈ₚ ϕ) holds
  τ = point-contains-top 𝓍′

  μ : closed-under-binary-meets X ϕ holds
  μ = point-is-closed-under-∧ 𝓍′

  υ : is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 𝟏L)) ϕ holds
  υ (U , V) =  point-is-upwards-closed 𝓍′ U V

  α : ϕ 𝟏[ 𝒪 X ] ＝ ⊤
  α = only-𝟏-is-above-𝟏 (𝒪 𝟏L) (ϕ 𝟏[ 𝒪 X ]) (λ _ → τ)

  β : (U V : ⟨ 𝒪 X ⟩) → ϕ (U ∧[ 𝒪 X ] V) ＝ ϕ U ∧[ 𝒪 𝟏L ] ϕ V
  β U V = ≤-is-antisymmetric (poset-of (𝒪 𝟏L)) β₁ β₂
   where
    β₁ : ϕ (U ∧[ 𝒪 X ] V) holds → (ϕ U ∧[ 𝒪 𝟏L ] ϕ V) holds
    β₁ p = υ ((U ∧[ 𝒪 X ] V) , U) (∧[ 𝒪 X ]-lower₁ U V) p
         , υ ((U ∧[ 𝒪 X ] V) , V) (∧[ 𝒪 X ]-lower₂ U V) p

    β₂ : (ϕ U ∧[ 𝒪 𝟏L ] ϕ V) holds → ϕ (U ∧[ 𝒪 X ] V) holds
    β₂ (p , q) = μ U V p q

  γ₀ : (S : Fam 𝓤 ⟨ 𝒪 X ⟩) → ϕ (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝒪 𝟏L ] ⁅ ϕ U ∣ U ε S ⁆
  γ₀ S = ≤-is-antisymmetric (poset-of (𝒪 𝟏L)) † ‡
   where
    open PosetNotation (poset-of (𝒪 𝟏L))

    † : (ϕ (⋁[ 𝒪 X ] S) ≤ (⋁[ 𝒪 𝟏L ] ⁅ ϕ U ∣ U ε S ⁆)) holds
    † = point-is-completely-prime 𝓍′ S

    ‡ : ((⋁[ 𝒪 𝟏L ] ⁅ ϕ U ∣ U ε S ⁆) ≤ ϕ (⋁[ 𝒪 X ] S)) holds
    ‡ p = ∥∥Ω-rec ※ p
     where
      ※ : (Σ i ꞉ index S , ϕ (S [ i ]) holds) → ϕ (⋁[ 𝒪 X ] S) holds
      ※ (i , q) = υ (S [ i ] , ⋁[ 𝒪 X ] S) (⋁[ 𝒪 X ]-upper S i) q

  γ : (S : Fam 𝓤 ⟨ 𝒪 X ⟩) → (ϕ (⋁[ 𝒪 X ] S) is-lub-of ⁅ ϕ U ∣ U ε S ⁆) holds
  γ S = transport (λ - → (- is-lub-of ⁅ ϕ U ∣ U ε S ⁆) holds) (γ₀ S ⁻¹) ※
   where
    ※ : ((⋁[ 𝒪 𝟏L ] ⁅ ϕ U ∣ U ε S ⁆) is-lub-of ⁅ ϕ U ∣ U ε S ⁆) holds
    ※ = ⋁[ 𝒪 𝟏L ]-upper ⁅ ϕ U ∣ U ε S ⁆ , ⋁[ 𝒪 𝟏L ]-least ⁅ ϕ U ∣ U ε S ⁆

\end{code}

\begin{code}

open DefnOfCPF

𝔰₀-gives-filter : (X : Locale (𝓤 ⁺) 𝓤 𝓤) (𝒻 : 𝟏L ─c→ X)
                → is-filter X (𝔰₀ X 𝒻) holds
𝔰₀-gives-filter X 𝒻 = † , ‡
 where
  † : is-upwards-closed X (𝔰₀ X 𝒻) holds
  † = {!!}

  ‡ : {!!}
  ‡ = {!!}

\end{code}

-- to-cpf : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 𝟏L ⟩) → Point X
-- to-cpf X P = {!!} , {!!}

-- tmp : ⟨ 𝒪 𝟏L ⟩ ＝ Ω (𝓤 ⁺)
-- tmp = refl

-- to-map : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X → 𝟏L ─c→ X
-- to-map X ℱ = {!to-predicate X ℱ!} , {!!}

\end{code}
