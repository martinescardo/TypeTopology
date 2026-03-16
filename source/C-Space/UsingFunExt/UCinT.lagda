Chuangjie Xu 2013 (update in February 2015, ported to TypeTopology in 2025)

We extend System T with a Fan functional, use it to formulate the
uniform-continuity principle, and validate the principle via C-spaces.

The syntax of the object language is factored out into
`C-Space.Syntax.SystemTWithFan`. In this module we interpret that syntax in the
C-space model and show that the distinguished formula `Principle[UC]` holds
there.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.UCinT (fe : DN-funext 𝓤₀ 𝓤₀) where

open import Naturals.Properties

open import C-Space.Preliminaries.Booleans.Functions
open import C-Space.Preliminaries.Naturals.Order
open import C-Space.Preliminaries.Sequence
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.Syntax.SystemTWithFan
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.DiscreteSpace fe
open import C-Space.UsingFunExt.YonedaLemma fe
open import C-Space.UsingFunExt.Fan fe
open import C-Space.UsingFunExt.TdefinableFunctionsAreUC fe
     renaming (c⟦_⟧ʸ to ⟦_⟧ʸ ; c⟦_⟧ᶜ to ⟦_⟧ᶜ)
     using (continuous-prj)

\end{code}

Interpretation of the syntax of System T with Fan into C-spaces:

\begin{code}

⟦_⟧ᵐ : {Γ : Cxt}{σ : Ty} → Tm Γ σ → Map ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ
⟦ VAR {Γ} i ⟧ᵐ            = continuous-prj Γ i
⟦ ⊥ {Γ} ⟧ᵐ                = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⟧ʸ ₀
⟦ ⊤ {Γ} ⟧ᵐ                = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⟧ʸ ₁
⟦ IF {Γ} {σ} ⟧ᵐ           = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⇨ σ ⇨ σ ⇨ σ ⟧ʸ (continuous-if ⟦ σ ⟧ʸ)
⟦ ZERO {Γ} ⟧ᵐ             = continuous-constant ⟦ Γ ⟧ᶜ ⟦ Ⓝ ⟧ʸ 0
⟦ SUCC {Γ} ⟧ᵐ             = continuous-constant ⟦ Γ ⟧ᶜ ⟦ Ⓝ ⇨ Ⓝ ⟧ʸ continuous-succ
⟦ REC {Γ} {σ} ⟧ᵐ          = continuous-constant ⟦ Γ ⟧ᶜ ⟦ σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ ⟧ʸ (continuous-rec ⟦ σ ⟧ʸ)
⟦ PAIR {Γ} {σ} {τ} M N ⟧ᵐ = continuous-pair ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ ⟦ N ⟧ᵐ
⟦ PRJ₁ {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₁ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ W ⟧ᵐ
⟦ PRJ₂ {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₂ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ W ⟧ᵐ
⟦ LAM {Γ} {σ} {τ} M ⟧ᵐ    = continuous-λ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ
⟦ _·_ {Γ} {σ} {τ} M N ⟧ᵐ  = continuous-app ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ ⟦ N ⟧ᵐ
⟦ FAN {Γ} ⟧ᵐ              = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ⇨ Ⓝ ⟧ʸ fan

-- Formula semantics: a formula in context Γ is interpreted as a predicate on
-- semantic environments ρ : U ⟦ Γ ⟧ᶜ.
⟦_⟧ᶠ : {Γ : Cxt} → Fml Γ → U ⟦ Γ ⟧ᶜ → Set
⟦ t == u ⟧ᶠ ρ = pr₁ ⟦ t ⟧ᵐ ρ ＝ pr₁ ⟦ u ⟧ᵐ ρ
⟦ φ ∧∧ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) × (⟦ ψ ⟧ᶠ ρ)
⟦ φ →→ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) → (⟦ ψ ⟧ᶠ ρ)

\end{code}

We say a formula is validated by the model if

\begin{code}

_is-validated : {Γ : Cxt} → Fml Γ → Set
φ is-validated = ∀ ρ → ⟦ φ ⟧ᶠ ρ

\end{code}

The uniform-continuity principle is validated by the model:

Given an environment `ρ`, the assumption `EN` says that the interpreted term
`A＝⟦FAN•F⟧B` evaluates to `⊤`. Unfolding the recursor shows that the
interpreted sequences agree on the first `fan f` bits; `fan-behaviour` then
gives equality of the values of `f` on those sequences.

\begin{code}

Theorem : Principle[UC] is-validated
       -- ∀ ρ, if A and B agree on their first FAN(F) bits at ρ, then
       -- the interpreted function F takes the same value on A and B.
Theorem ρ EN = fan-behaviour f α β en
 where
  -- The function and the two sequences named by the distinguished variables in
  -- the context Γ.
  f : Map (ℕSpace ⇒ 𝟚Space) ℕSpace
  f = pr₁ ⟦ F ⟧ᵐ ρ
  α β : Map ℕSpace 𝟚Space
  α = pr₁ ⟦ A ⟧ᵐ ρ
  β = pr₁ ⟦ B ⟧ᵐ ρ

  -- This is the step function of the interpreted recursor used to define
  -- `A＝⟦FAN•F⟧B`.
  g : ℕ → 𝟚 → 𝟚
  g n b = pr₁ (pr₁ (pr₁ ⟦ step ⟧ᵐ ρ) n) b

  -- If the recursive boolean accumulator stays equal to ₁ up to stage k, then
  -- α and β agree on their first k bits.
  lemma : (k : ℕ) → ℕ-induction ₁ g k ＝ ₁ → pr₁ α ＝⟦ k ⟧ pr₁ β
  lemma 0        refl = ＝⟦zero⟧
  lemma (succ k) esk  = ＝⟦succ⟧ IH claim₁
   where
    ek : ℕ-induction ₁ g k ＝ ₁
    ek = pr₂ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
    IH : pr₁ α ＝⟦ k ⟧ pr₁ β
    IH = lemma k ek
    claim₀ : eq (pr₁ α k) (pr₁ β k) ＝ ₁
    claim₀ = pr₁ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
    claim₁ : pr₁ α k ＝ pr₁ β k
    claim₁ = Lemma[eq] (pr₁ α k) (pr₁ β k) claim₀

  -- Applying the previous lemma at k = ⟦ FAN · F ⟧ᵐ ρ converts the assumption
  -- EN into agreement of α and β on the first `fan f` bits.
  en : pr₁ (pr₁ ⟦ A ⟧ᵐ ρ) ＝⟦ pr₁ ⟦ FAN · F ⟧ᵐ ρ ⟧ pr₁ (pr₁ ⟦ B ⟧ᵐ ρ)
  en = lemma (pr₁ ⟦ FAN · F ⟧ᵐ ρ) EN

\end{code}
