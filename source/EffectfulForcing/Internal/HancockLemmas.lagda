---
authors:      ["Bruno Paiva", "Ayberk Tosun"]
date-started: 2024-05-24
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (rec to natrec)
open import EffectfulForcing.Internal.PlumpishOrdinals

module EffectfulForcing.Internal.HancockLemmas
         (PO : PlumpishOrdinals {𝓤})
       where

open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.Dialogue renaming (B to Dialogue)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX renaming (B-Set⟦_⟧ to ⦅_⦆)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import Naturals.Order
open import Ordinals.Brouwer renaming (B to Brw; Z to 𝐙; S to 𝐒; L to lim)
open import Ordinals.BrouwerArithmetic
open import Ordinals.BrouwerOrdering

\end{code}

\section{Preliminaries}

We denote by `Brw` the type of Brouwer ordinals.

\begin{code}

\end{code}

Recall also that `B X` denotes the type of dialogue trees with answer type `X`.
We define some more suggestive notation for this, since the type `B` is also
used for Brouwer trees, which the author finds confusing.

\begin{code}

Dialogue′ : 𝓤  ̇ → 𝓤  ̇
Dialogue′ X = X

\end{code}

We adopt the convention of using the variable letters `c`, `d`, and `e` to range
over dialogue trees (and try to use this as consistently as possible).

The _height_ of a dialogue tree is the longest path that it contains. We have
ω-many children at each node, the maximum of which we compute by taking the
limit of the ω-sequence of children of a given node.

\begin{code}

height : {X : 𝓥 ̇ } → Dialogue X → Brw
height (η _)   = 𝐙
height (β ϕ _) = 𝐒 (lim (height ∘ ϕ))

\end{code}

We now formulate our logical relation that expresses the property of being
hereditarily smaller than `ε₀`. Note that this is formulated directly on
dialogue trees rather than on the syntax.

\begin{code}

hereditarily-smaller-than-ε₀ : {τ : type} → ⦅ τ ⦆ → 𝓤₀  ̇

\end{code}

For the base type, we just assert that the height of the dialogue tree is
less than `ε₀`.

\begin{code}

hereditarily-smaller-than-ε₀ {ι} d = height d ⊏ ε₀

\end{code}

For a function type `σ ⇒ τ`, our logical relation says:

\begin{code}

hereditarily-smaller-than-ε₀ {σ ⇒ τ} f =
 (d : ⦅ σ ⦆) →
  hereditarily-smaller-than-ε₀ d →
   hereditarily-smaller-than-ε₀ (f d)

\end{code}

\begin{code}

zero-is-less-than-one : 𝐙 ⊏ 𝐒 𝐙
zero-is-less-than-one = stop 𝐙 , ⊑-refl 𝐙

zero-is-less-than-any-successor : (b : Brw) → 𝐙 ⊏ 𝐒 b
zero-is-less-than-any-successor b = stop b , Z-⊑ b

is-strictly-increasing : (ℕ → Brw) → 𝓤₀  ̇
is-strictly-increasing f = (n : ℕ) → f n ⊏ f (succ n)

zero-is-below-ω : 𝐙 ⊏ ω
zero-is-below-ω = pick finite 1 (stop 𝐙) , ⊑-refl 𝐙

zero-is-below-ε₀ : 𝐙 ⊏ ε₀
zero-is-below-ε₀ = (pick ω-tower 0 (pr₁ (zero-is-below-ω))) , ⊑-refl 𝐙

zero-is-hereditarily-smaller-than-ε₀ : hereditarily-smaller-than-ε₀ zero'
zero-is-hereditarily-smaller-than-ε₀ = zero-is-below-ε₀

\end{code}
