Ayberk Tosun, 3 January 2022

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import List hiding ([_])

\end{code}

\begin{code}

module PatchTopology
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Frame pt fe hiding (is-directed)

open AllCombinators pt fe
open PropositionalTruncation pt
open import Nucleus pt fe
open import CompactRegular pt fe

\end{code}

A _locale_ is a type that has a frame of opens.

\begin{code}

record locale (𝓤 𝓥 𝓦 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇  where
 field
  ⟨_⟩ₗ         : 𝓤 ̇
  frame-str-of : frame-structure 𝓥 𝓦 ⟨_⟩ₗ

 𝒪 : frame 𝓤 𝓥 𝓦
 𝒪 = ⟨_⟩ₗ , frame-str-of

\end{code}

We fix a locale `X` for the remainder of this module.

\begin{code}

open locale

module PatchConstruction (X : locale 𝓤 𝓥 𝓦) (σ : is-spectral (𝒪 X) holds) where

 _≤_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω 𝓥
 U ≤ V = U ≤[ poset-of (𝒪 X) ] V

 open Meets _≤_

 _⊓_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 U ⊓ V = U ∧[ 𝒪 X ] V

\end{code}

A nucleus is called perfect iff it is Scott-continuous:

\begin{code}

 is-perfect : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
 is-perfect = is-scott-continuous (𝒪 X) (𝒪 X)

\end{code}

\begin{code}

 perfect-nucleus : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 perfect-nucleus = Σ j ꞉ (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) ,
                    ((is-nuclear (𝒪 X) j ∧ is-perfect j) holds)

\end{code}

\section{Poset of perfect nuclei}

\begin{code}

 _$_ : perfect-nucleus → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 (j , _) $ U = j U

\end{code}

\begin{code}

 perfect-nuclei-eq : (𝒿 𝓀 : perfect-nucleus) → 𝒿 $_ ≡ 𝓀 $_ → 𝒿 ≡ 𝓀
 perfect-nuclei-eq 𝒿 𝓀 = to-subtype-≡ γ
  where
   γ : (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
     → is-prop ((is-nuclear (𝒪 X) j ∧ is-perfect j) holds)
   γ j = holds-is-prop (is-nuclear (𝒪 X) j ∧ is-perfect j)

\end{code}

Nuclei are ordered pointwise.

\begin{code}

 _≼_ : perfect-nucleus → perfect-nucleus → Ω (𝓤 ⊔ 𝓥)
 𝒿 ≼ 𝓀 = Ɐ U ∶ ⟨ 𝒪 X ⟩ , (𝒿 $ U) ≤ (𝓀 $ U)

\end{code}

\begin{code}

 ≼-is-reflexive : is-reflexive _≼_ holds
 ≼-is-reflexive 𝒿 U = ≤-is-reflexive (poset-of (𝒪 X)) (𝒿 $ U)

\end{code}

\begin{code}

 ≼-is-transitive : is-transitive _≼_ holds
 ≼-is-transitive 𝒾 𝒿 𝓀 φ ψ U = 𝒾 $ U ≤⟨ φ U ⟩ 𝒿 $ U ≤⟨ ψ U ⟩ 𝓀 $ U ■
  where
   open PosetReasoning (poset-of (𝒪 X))

\end{code}

\begin{code}

 ≼-is-preorder : is-preorder _≼_ holds
 ≼-is-preorder = ≼-is-reflexive , ≼-is-transitive

\end{code}

\begin{code}

 ≼-is-antisymmetric : is-antisymmetric _≼_
 ≼-is-antisymmetric {x = 𝒿} {𝓀} φ ψ = perfect-nuclei-eq 𝒿 𝓀 (dfunext fe γ)
  where
   γ : 𝒿 $_ ∼ 𝓀 $_
   γ U = ≤-is-antisymmetric (poset-of (𝒪 X)) (φ U) (ψ U)

\end{code}

\begin{code}

 patch-poset : poset (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓥)
 patch-poset = perfect-nucleus , _≼_ , ≼-is-preorder , ≼-is-antisymmetric

\end{code}

\section{Meet-semilattice of perfect nuclei}

\begin{code}

 _⋏₀_ : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩  → ⟨ 𝒪 X ⟩)
 j ⋏₀ k = λ x → j x ∧[ 𝒪 X ] k x

 ⋏₀-inflationary : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                 → is-inflationary (𝒪 X) j holds
                 → is-inflationary (𝒪 X) k holds
                 → is-inflationary (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-inflationary j k p q U =
  ∧[ 𝒪 X ]-greatest (j U) (k U) U (p U) (q U)

 ⋏₀-idempotent : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
               → is-idempotent (𝒪 X) j holds
               → is-idempotent (𝒪 X) k holds
               → is-idempotent (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-idempotent j k p q = {!!}

 _⋏₁_ : nucleus (𝒪 X) → nucleus (𝒪 X) → nucleus (𝒪 X)
 𝒿@(j , jn) ⋏₁ 𝓀@(k , kn) = (j ⋏₀ k) , ⋏-𝓃₁ , ⋏-𝓃₂ , ⋏-𝓃₃
  where
   ⋏-𝓃₁ = ⋏₀-inflationary j k (𝓃₁ (𝒪 X) 𝒿) (𝓃₁ (𝒪 X) 𝓀)
   ⋏-𝓃₂ = {!!}
   ⋏-𝓃₃ = {!!}

 _⋏_ : perfect-nucleus → perfect-nucleus → perfect-nucleus
 𝒿 ⋏ 𝓀 = {!!}

\end{code}
