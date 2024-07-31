---
title:          Definition of some combinators and shortcut for sets.
author:         Martin Trucchi
date-started:   2024-06-07
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚 ; ℕ)
open import UF.DiscreteAndSeparated hiding (𝟚-is-set ; ℕ-is-set ; ℕ-is-discrete)
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module SyntheticTopology.SetCombinators
        (𝓤 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import Locales.DiscreteLocale.Two fe pe pt
open import Locales.Frame pt fe
open import UF.ImageAndSurjection pt

open PropositionalTruncation pt

\end{code}

We here define some useful shortcuts for sets, as well as combinators to avoid
messy code in the Synthetic Topology development.

The first one turns propositions into sets, in order to be able to define
compact propositions for example.

\begin{code}

Ωₛ : Ω 𝓤 → hSet 𝓤
Ωₛ p = (p holds , props-are-sets (holds-is-prop p))

\end{code}

Here we define shortcuts rather than combinators for sets used in the module.

\begin{code}

𝟘ₛ-is-set = 𝟘-is-set

𝟘ₛ : hSet 𝓤
𝟘ₛ = 𝟘 , 𝟘ₛ-is-set

𝟙ₛ-is-set = 𝟙-is-set

𝟙ₛ : hSet 𝓤
𝟙ₛ = 𝟙 , 𝟙ₛ-is-set

\end{code}

We use `𝟚` define in `Locales.DiscreteLocale.Two`, to have a universe
polymorphic version of `𝟚`.

\begin{code}

𝟚ₛ-is-set = 𝟚-is-set 𝓤

𝟚ₛ : hSet 𝓤
𝟚ₛ = (𝟚 𝓤) , 𝟚ₛ-is-set

\end{code}

I did not find a universe polymorphic version of `ℕ`. Here it is.

\begin{code}

data ℕ : 𝓤 ̇  where
 zero : ℕ
 succ : ℕ → ℕ

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

boom : ℕ → 𝓤 ̇
boom zero = 𝟘
boom (succ _) = 𝟙

ℕ-is-discrete : is-discrete ℕ
ℕ-is-discrete zero zero = inl refl
ℕ-is-discrete zero (succ m) = inr λ p → 𝟘-elim (𝟘-is-not-𝟙 (ap boom p))
ℕ-is-discrete (succ n) zero = inr λ p → 𝟘-elim (𝟘-is-not-𝟙 (ap boom (p ⁻¹)))
ℕ-is-discrete (succ n) (succ m) =
 cases (λ p → inl (ap succ p))
       (λ p → inr λ ps → p (ap pred ps))
       (ℕ-is-discrete n m)

ℕ-is-set : is-set ℕ
ℕ-is-set = discrete-types-are-sets ℕ-is-discrete

ℕₛ-is-set = ℕ-is-set

ℕₛ : hSet 𝓤
ℕₛ = ℕ , ℕₛ-is-set

\end{code}

We now define the set combinators.

We have the same convention of using `𝒳` as a generic set along with the proof,
with its underlying set being `X`.

Note : for `imageₛ` , the fact that `𝒳` is a set is not useful, but
we define it this way to keep the coherence between the arguments.

\begin{code}

module _ (𝒳 : hSet 𝓤) where
 private
  X = underlying-set 𝒳
  set-X = pr₂ 𝒳

 Πₛ : (X → hSet 𝓤) → hSet 𝓤
 Πₛ f = Π (underlying-set ∘ f) , Π-is-set fe (pr₂ ∘ f)

 module _ (𝒴 : hSet 𝓤) where
  private
   Y = underlying-set 𝒴
   set-Y = pr₂ 𝒴

  _×ₛ_ : hSet 𝓤
  _×ₛ_ = (X × Y) , ×-is-set set-X set-Y

  imageₛ : (X → Y) → hSet 𝓤
  imageₛ f = (image f , Σ-is-set set-Y λ y → props-are-sets ∃-is-prop)

\end{code}

We now define a combinator to get the set induced by a subset. That is, if
`𝒳 = (X , set-X)` is a set, and `U : 𝓟 X` is a subset of 𝒳, we can get the
set induced by `U` using `𝕋ₛ U`.

\begin{code}

 𝕋ₛ : 𝓟 X → hSet 𝓤
 𝕋ₛ U = 𝕋 U , Σ-is-set set-X λ x → props-are-sets (holds-is-prop (U x))

\end{code}
