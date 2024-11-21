---
authors:      ["Bruno Paiva", "Ayberk Tosun"]
date-started: 2024-05-24
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import EffectfulForcing.Internal.PlumpishOrdinals
open import MLTT.Spartan renaming (rec to natrec)
open import UF.FunExt
open import UF.PropTrunc

module EffectfulForcing.Internal.HancockLemmas
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.CombinatoryT hiding (Ω)
open import EffectfulForcing.MFPSAndVariations.Dialogue renaming (B to Dialogue)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX renaming (B-Set⟦_⟧ to ⦅_⦆)
open import Naturals.Order
open import Ordinals.Brouwer renaming (B to Brw; Z to 𝐙; S to 𝐒; L to lim)
open import Ordinals.BrouwerArithmetic
open import Ordinals.BrouwerArithmeticProperties
open import Ordinals.BrouwerOrdering
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe hiding (_⇒_)

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
zero-is-less-than-one = 𝐙 , Z-⊑ 𝐙 , ◂-stop Z≈

zero-is-less-than-any-successor : (b : Brw) → 𝐙 ⊏ 𝐒 b
zero-is-less-than-any-successor b = b , (Z-⊑ b) , ◂-stop (≈-refl b)

is-strictly-increasing : (ℕ → Brw) → 𝓤₀  ̇
is-strictly-increasing f = (n : ℕ) → f n ⊏ f (succ n)

zero-is-below-ω : 𝐙 ⊏ ω
zero-is-below-ω = 𝐙 , Z-⊑ 𝐙 , ◂-pick finite 1 (◂-stop Z≈)

zero-is-below-ε₀ : 𝐙 ⊏ ε₀
zero-is-below-ε₀ = 𝐙 , Z-⊑ 𝐙 , ◂-pick ω-tower zero (◂-pick finite 1 (◂-stop Z≈))

zero-is-hereditarily-smaller-than-ε₀ : hereditarily-smaller-than-ε₀ zero'
zero-is-hereditarily-smaller-than-ε₀ = zero-is-below-ε₀

\end{code}

Added on 2024-06-18 by Ayberk Tosun.

We define a type expressing that a given sequence of Brouwer trees is
increasing.

\begin{code}

is-increasing : (ℕ → Brw) → 𝓤₀  ̇
is-increasing ϕ = (i : ℕ) → ϕ i ⊏ ϕ (succ i)

\end{code}

Alternative formulation of being increasing:

\begin{code}

is-increasing₀ : (ℕ → Brw) → 𝓤₀  ̇
is-increasing₀ ϕ = (i j : ℕ) → (i <ℕ j) → ϕ i ⊏ ϕ j

\end{code}

Using this, we define the following type expressing that all sequences in a
Brouwer tree are increasing.

\begin{code}

all-sequences-are-increasing : Brw → 𝓤₀  ̇
all-sequences-are-increasing 𝐙       = 𝟙
all-sequences-are-increasing (𝐒 t)   = all-sequences-are-increasing t
all-sequences-are-increasing (lim ϕ) = is-increasing ϕ
                                     × ((i : ℕ) → all-sequences-are-increasing (ϕ i))

\end{code}

Added on 2024-06-18 by Ayberk Tosun.

The addition operation preserves the property of all sequences being increasing.

\begin{code}

addition-does-not-add-non-increasing-sequences
 : (s t : Brw)
 → all-sequences-are-increasing s
 → all-sequences-are-increasing t
 → all-sequences-are-increasing (s +B t)
addition-does-not-add-non-increasing-sequences s 𝐙       φ ψ           = φ
addition-does-not-add-non-increasing-sequences s (𝐒 t)   φ ψ           = †
 where
  † : all-sequences-are-increasing (s +B t)
  † = addition-does-not-add-non-increasing-sequences s t φ ψ
addition-does-not-add-non-increasing-sequences s (lim ϕ) φ ψ@(inc , ϑ) = † , ‡
 where
  † : is-increasing (λ i → s +B ϕ i)
  † i = +B-strictly-monotonic-right s (ϕ i) (ϕ (succ i)) (inc i)

  ‡ : (i : ℕ) → all-sequences-are-increasing (s +B ϕ i)
  ‡ i = addition-does-not-add-non-increasing-sequences s (ϕ i) φ (ϑ i)

\end{code}

\begin{code}

one-is-below-the-limit-of-any-increasing-sequence : (ϕ : ℕ → Brw) → is-increasing ϕ → 𝐒 𝐙 ⊏ lim ϕ
one-is-below-the-limit-of-any-increasing-sequence ϕ inc = {!!}

×B-does-not-add-non-increasing-sequences
 : (s t : Brw)
 → all-sequences-are-increasing s
 → all-sequences-are-increasing t
 → all-sequences-are-increasing (s ×B t)
×B-does-not-add-non-increasing-sequences s 𝐙       φ ψ = ψ
×B-does-not-add-non-increasing-sequences s (𝐒 t)   φ ψ =
 addition-does-not-add-non-increasing-sequences (s ×B t) s † φ
  where
   † : all-sequences-are-increasing (s ×B t)
   † = ×B-does-not-add-non-increasing-sequences s t φ ψ
×B-does-not-add-non-increasing-sequences 𝐙 (lim ϕ) φ ψ = {!!}
×B-does-not-add-non-increasing-sequences (𝐒 s) (lim ϕ) φ ψ = {!!} , {!!}
×B-does-not-add-non-increasing-sequences (lim ϕ₁) (lim ϕ₂) (inc , χ) (inc₂ , υ) =
 † , ‡
  where
   Ⅰ : 𝐒 𝐙 ⊏ lim ϕ₁
   Ⅰ = one-is-below-the-limit-of-any-increasing-sequence ϕ₁ inc

   † : is-increasing (λ i → lim ϕ₁ ×B ϕ₂ i)
   † i = ×B-strictly-monotonic-right (lim ϕ₁) (ϕ₂ i) (ϕ₂ (succ i)) Ⅰ (inc₂ i)

   ‡ : (i : ℕ) → all-sequences-are-increasing (lim ϕ₁ ×B ϕ₂ i)
   ‡ i = ×B-does-not-add-non-increasing-sequences (lim ϕ₁) (ϕ₂ i) (inc , χ) (υ i)

\end{code}
