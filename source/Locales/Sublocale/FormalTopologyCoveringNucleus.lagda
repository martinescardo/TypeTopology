---
title:  The covering nucleus induced by a formal topology
author: Ayberk Tosun
date:   2026-10-28
---

In this module, we construct the nucleus that a formal topology's covering
relation defines on the Alexandroff locale.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sublocale.FormalTopologyCoveringNucleus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.Alexandroff.Definition
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.FormalTopology.Definition pt fe
open import Locales.Frame pt fe renaming (⟨_⟩ to ⟨_⟩ᶠ)
open import Locales.Sublocale.Nucleus pt fe
open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.Logic
open import UF.Powerset using (comprehension; _∩_; 𝓟)
open import UF.Powerset-MultiUniverse using (powersets-are-sets)
open import UF.Sets
open import UF.SubtypeClassifier using (Ω; _holds)

\end{code}

We work in a module parameterized by a formal topology `𝒜`.

\begin{code}

module Covering-Nucleus-Of-Formal-Topology (𝒜 : Formal-Topology 𝓤) where

\end{code}

We denote by `𝒜P` the underlying poset of formal topology `𝒜`.

\begin{code}

 𝒜P : Poset 𝓤 𝓤
 𝒜P = underlying-poset-of-formal-topology 𝒜

\end{code}

We denote by `↓𝒜` the frame of downward-closed subsets of `𝒜P`.

\begin{code}

 open Downward-Closed-Subset-Frame 𝓤 pt fe pe

 ↓𝒜 : Frame (𝓤 ⁺) 𝓤 𝓤
 ↓𝒜 = downward-closed-subset-frame 𝒜P

\end{code}

By flipping the covering relation `_◁_`, we obtain an endomap on `𝓟 ⟨ 𝒜 ⟩`. We
denote this by `◇̇`.

\begin{code}

 ◇̇_ : 𝓟 ⟨ 𝒜 ⟩ → 𝓟 ⟨ 𝒜 ⟩
 ◇̇_ U = ⁅ a ꞉ ∣ 𝒜P ∣ₚ ∣ a ◁[ 𝒜 ] U ⁆

 infixr 7 ◇̇_

\end{code}

This operator forms a nucleus when restricted to downward-closed subsets. We
start by defining this restriction, which we denote by `◇` in accordance with
the view of nuclei as modal operators.

\begin{code}

 ◇_ : ⟨ ↓𝒜 ⟩ᶠ → ⟨ ↓𝒜 ⟩ᶠ
 ◇ (U , _) = ◇̇ U , φ
  where
   φ : is-downward-closed 𝒜P ⁅ a ꞉ ∣ 𝒜P ∣ₚ ∣ a ◁[ 𝒜 ] U ⁆ holds
   φ u₀ a cov p = cover-satisfies-left-rule 𝒜 u₀ a U p cov

 infixr 7 ◇_

\end{code}

Negri ([1], p. 22) uses the notation 𝒞_𝒜 for what we called `◇` above. She also
uses the terminology _saturated_ for subsets that are fixed points for this
operator (i.e. the `◇`-stable ones).

\begin{code}

 is-saturated₀ : 𝓟 ⟨ 𝒜 ⟩ → Ω (𝓤 ⁺)
 is-saturated₀ U = ◇̇ U ＝ₚ U
  where
   σ : is-set (𝓟 ⟨ 𝒜 ⟩)
   σ = powersets-are-sets {𝓤} fe pe

   open Equality σ

 is-saturated : ⟨ ↓𝒜 ⟩ᶠ → Ω (𝓤 ⁺)
 is-saturated = is-saturated₀ ∘ underlying-subset-syntax 𝒜P

\end{code}

\section{Inflationarity}

The `◇` operator is inflationary.

\begin{code}

 𝒜₀ : Quasi-Formal-Topology 𝓤
 𝒜₀ = underlying-quasi-formal-topology 𝒜

 ◇-is-inflationary : is-inflationary ↓𝒜 ◇_ holds
 ◇-is-inflationary (U , _) a =
  reflexivity-of-quasi-cover 𝒜₀ a U

\end{code}

\section{Preservation of binary meets}

The `◇` operator preserves binary meets of `↓𝒜`.

\begin{code}

 open FrameHomomorphisms
 open PosetNotation (poset-of ↓𝒜) using (_≤_)

 ◇-preserves-binary-meets : preserves-binary-meets ↓𝒜 ↓𝒜 ◇_ holds
 ◇-preserves-binary-meets 𝔘@(U , φ) 𝔙@(V , ψ) =
  ≤-is-antisymmetric (poset-of ↓𝒜) † ‡
   where
    cov₁ : (U ∩ V ◁⁺[ 𝒜 ] U) holds
    cov₁ a (β , _) = reflexivity-of-quasi-cover 𝒜₀ a U β

    cov₂ : (U ∩ V ◁⁺[ 𝒜 ] V) holds
    cov₂ a (_ , γ) = reflexivity-of-quasi-cover 𝒜₀ a V γ

    cov₁′ : (◇̇ (U ∩ V) ◁⁺[ 𝒜 ] U) holds
    cov₁′ a cov = transitivity-of-quasi-cover 𝒜₀ a (U ∩ V) U cov cov₁

    cov₂′ : (◇̇ (U ∩ V) ◁⁺[ 𝒜 ] V) holds
    cov₂′ a cov = transitivity-of-quasi-cover 𝒜₀ a (U ∩ V) V cov cov₂

    † : (◇ (𝔘 ∧[ ↓𝒜 ] 𝔙) ≤ (◇ 𝔘 ∧[ ↓𝒜 ] ◇ 𝔙)) holds
    † a cov = cov₁′ a cov , cov₂′ a cov

    open Downward-Closure-Intersection-Syntax (λ x y → x ≤[ 𝒜P ] y)

    ‡ : ((◇ 𝔘 ∧[ ↓𝒜 ] ◇ 𝔙) ≤ ◇ (𝔘 ∧[ ↓𝒜 ] 𝔙)) holds
    ‡ a (cov₁ , cov₂) = transport (λ - → (a ◁[ 𝒜 ] -) holds) eq cov
     where
      cov : (a ◁[ 𝒜 ] U ⊓ V) holds
      cov = cover-satisfies-right-rule 𝒜 a U V cov₁ cov₂

      eq : U ⊓ V ＝ U ∩ V
      eq =
       downward-closedness-implies-⊓-coincides-with-∩ pe (≤-is-reflexive 𝒜P) φ ψ

\end{code}

\section{Idempotence}

The idempotence of the `◇` operator follows directly from the transitivity of
`_◁⁺_`.

\begin{code}

 ◇-is-idempotent : is-idempotent ↓𝒜 ◇_ holds
 ◇-is-idempotent (U , _) a cov = † a cov
  where
   open Quasi-Cover-Reasoning 𝒜₀

   † : (◇̇ ◇̇ U ◁⁺[ 𝒜 ] U) holds
   † = ◇̇ ◇̇ U  ◁⁺⟨ (λ _ → id) ⟩
       ◇̇ U    ◁⁺⟨ (λ _ → id) ⟩
       U      ■

\end{code}

Finally, we package everything up into a nucleus.

\begin{code}

 ◁-nucleus : Nucleus ↓𝒜
 ◁-nucleus = ◇_ , ◇-is-inflationary , ◇-is-idempotent , ◇-preserves-binary-meets

\end{code}

The sublocale of the Alexandroff locale given by the above nucleus is the locale
presented by the formal topology in consideration.

\section{Bibliography}

[1]: Sara Negri. _Continuous domains as formal spaces_. Mathematical Structures
     in Computer Science, Volume 12, No. 1, pp. 19–52, 2002.
     DOI:10.1017/S0960129501003450
