Ayberk Tosun

Started on 22 September 2023.
Proof of bijection completed on 29 September 2023.

This module contains the proof that points of a locale are in bijection with the
completely prime filters.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons
open import UF.Retracts

module Locales.Point.Properties (pt : propositional-truncations-exist)
                                (fe : Fun-Ext)
                                (𝓤  : Universe)
                                (pe : propext 𝓤)
                                 where

open import Slice.Family
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier
open import UF.Sets
open import UF.Equiv

open import Locales.Frame            pt fe
open import Locales.Point.Definition pt fe
open import Locales.InitialFrame     pt fe

open PropositionalTruncation pt

open DefnOfCPF

open Locale

open AllCombinators pt fe

\end{code}

We denote by `𝟏L` the terminal locale.

\begin{code}

𝟏L : Locale (𝓤 ⁺) 𝓤 𝓤
𝟏L = 𝟏Loc pe

\end{code}

The map sending a CPF to a continuous map `𝟏 → X` is called `𝔯` (for "retract")
and its section is called `𝔰` (for "section"). We first define the underlying
functions of these and call them `𝔯₀` and `𝔰₀`. We then prove separately that
the results they give satisfy the desired conditions of being a continuous map
and being a completely prime filter (respectively).

\begin{code}

𝔯₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 𝟏L ⟩
𝔯₀ X (ϕ , cpf) U = ϕ U

𝔰₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → (𝟏L ─c→ X) → 𝓟 {𝓤} ⟨ 𝒪 X ⟩
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

𝔰₀-gives-cpf : (X : Locale (𝓤 ⁺) 𝓤 𝓤) (𝒻 : 𝟏L ─c→ X)
                → is-cpf X (𝔰₀ X 𝒻) holds
𝔰₀-gives-cpf X 𝒻 = Point′ᵣ.point-is-cpf 𝓍
 where
  open ContinuousMapNotation 𝟏L X using (_⋆∙_)

  υ : is-upwards-closed X (𝒻 ⋆∙_) holds
  υ U V p q =
   frame-morphisms-are-monotonic (𝒪 X) (𝒪 𝟏L) (𝒻 ⋆∙_) (𝒻 .pr₂) (U , V) p q

  τ : 𝟏[ 𝒪 X ] ∈ (𝒻 ⋆∙_)
  τ = equal-⊤-gives-holds
       (𝒻 ⋆∙ 𝟏[ 𝒪 X ])
       (frame-homomorphisms-preserve-top (𝒪 X) (𝒪 𝟏L) 𝒻)

  μ : closed-under-binary-meets X (𝒻 ⋆∙_) holds
  μ U V p q = equal-⊤-gives-holds (𝒻 ⋆∙ (U ∧[ 𝒪 X ] V)) †
   where
    † : 𝒻 ⋆∙ meet-of (𝒪 X) U V ＝ ⊤
    † = (𝒻 ⋆∙ (U ∧[ 𝒪 X ] V))
         ＝⟨ frame-homomorphisms-preserve-meets (𝒪 X) (𝒪 𝟏L) 𝒻 U V ⟩
        𝒻 ⋆∙ U ∧[ 𝒪 𝟏L ] (𝒻 ⋆∙ V)
         ＝⟨ ap (λ - → - ∧ (𝒻 ⋆∙ V)) (holds-gives-equal-⊤ pe fe (𝒻 ⋆∙ U) p) ⟩
        ⊤      ∧[ 𝒪 𝟏L ] (𝒻 ⋆∙ V)
         ＝⟨ ap (λ - → ⊤ ∧ -) (holds-gives-equal-⊤ pe fe (𝒻 ⋆∙ V) q) ⟩
        ⊤      ∧[ 𝒪 𝟏L ] ⊤        ＝⟨ ∧[ 𝒪 𝟏L ]-is-idempotent ⊤ ⁻¹ ⟩
        ⊤ ∎

  cp : is-completely-prime X (𝒻 ⋆∙_) holds
  cp S p = equal-⊤-gives-holds (⋁[ 𝒪 𝟏L ] ⁅ 𝒻 ⋆∙ U ∣ U ε S ⁆) q
   where
    ς : is-set ⟨ 𝒪 𝟏L ⟩
    ς = carrier-of-[ poset-of (𝒪 𝟏L) ]-is-set

    Ⅰ = frame-homomorphisms-preserve-all-joins (𝒪 X) (𝒪 𝟏L) 𝒻 S ⁻¹
    Ⅱ = holds-gives-equal-⊤ pe fe (𝒻 ⋆∙ (⋁[ 𝒪 X ] S)) p

    p′ : 𝒻 ⋆∙ (⋁[ 𝒪 X ] S) ＝ ⊤
    p′ = holds-gives-equal-⊤ pe fe (𝒻 ⋆∙ (⋁[ 𝒪 X ] S)) p

    q : ⋁[ 𝒪 𝟏L ] ⁅ 𝒻 ⋆∙ U ∣ U ε S ⁆ ＝ ⊤
    q = ⋁[ 𝒪 𝟏L ] ⁅ 𝒻 ⋆∙ U ∣ U ε S ⁆   ＝⟨ Ⅰ ⟩
        𝒻 ⋆∙ (⋁[ 𝒪 X ] S)              ＝⟨ Ⅱ ⟩
        ⊤                              ∎

  𝓍 : Point′ᵣ X
  𝓍 = record
       { point                     = 𝒻 ⋆∙_
       ; point-is-upwards-closed   = υ
       ; point-contains-top        = τ
       ; point-is-closed-under-∧   = μ
       ; point-is-completely-prime = cp
       }

\end{code}

\begin{code}

𝔯 : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X → 𝟏L ─c→ X
𝔯 X 𝓍 = 𝔯₀ X 𝓍 , 𝔯₀-gives-frame-homomorphism X 𝓍

𝔰 : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → 𝟏L ─c→ X → Point X
𝔰 X 𝒻 = 𝔰₀ X 𝒻 , 𝔰₀-gives-cpf X 𝒻

cpf-equiv-continuous-map-into-Ω : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Point X ≃ 𝟏L ─c→ X
cpf-equiv-continuous-map-into-Ω X = 𝔯 X , † , ‡
 where
  sec : (𝔯 X ∘ 𝔰 X) ∼ id
  sec 𝒻 = continuous-map-equality (𝒪 X) (𝒪 𝟏L) (𝔯 X (𝔰 X 𝒻)) 𝒻 λ _ → refl

  ret : (𝔰 X ∘ 𝔯 X) ∼ id
  ret 𝓍 = to-subtype-＝ (holds-is-prop ∘ is-cpf X) (dfunext fe λ _ → refl)

  † : has-section (𝔯 X)
  † = 𝔰 X , sec

  ‡ : is-section (𝔯 X)
  ‡ = 𝔰 X , ret

\end{code}
