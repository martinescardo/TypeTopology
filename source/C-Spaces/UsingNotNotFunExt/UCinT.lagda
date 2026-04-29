Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

We have extended System T with a Fan functional and used it to formulate the
uniform-continuity principle. In this module we interpret the theory in the
C-space model to validate the distinguished formula for the uniform-continuity
principle.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Spaces.UsingNotNotFunExt.UCinT (dnfe : ¬¬ DN-funext 𝓤₀ 𝓤₀) where

open import Naturals.Properties

open import C-Spaces.Preliminaries.Booleans.Functions
open import C-Spaces.Preliminaries.Naturals.Order
open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.UniformContinuity
open import C-Spaces.Coverage
open import C-Spaces.Syntax.SystemTWithFan
open import C-Spaces.UsingNotNotFunExt.Space
open import C-Spaces.UsingNotNotFunExt.CartesianClosedness dnfe
open import C-Spaces.UsingNotNotFunExt.DiscreteSpace dnfe
open import C-Spaces.UsingNotNotFunExt.YonedaLemma dnfe
open import C-Spaces.UsingNotNotFunExt.Fan dnfe

\end{code}

Interpretation of the syntax of System T with Fan into C-spaces:

Types are interpreted as C-spaces and contexts as iterated products.

\begin{code}

⟦_⟧ʸ : Ty → Space
⟦ ② ⟧ʸ = 𝟚Space
⟦ Ⓝ ⟧ʸ = ℕSpace
⟦ σ ⊠ τ ⟧ʸ = ⟦ σ ⟧ʸ ⊗ ⟦ τ ⟧ʸ
⟦ σ ⇨ τ ⟧ʸ = ⟦ σ ⟧ʸ ⇒ ⟦ τ ⟧ʸ

⟦_⟧ᶜ : Cxt → Space
⟦ ε ⟧ᶜ = 𝟙Space
⟦ Γ ₊ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ⊗ ⟦ A ⟧ʸ

\end{code}

The semantic projection corresponding to a de Bruijn variable.

\begin{code}

continuous-prj : (Γ : Cxt)(i : Fin (length Γ)) → Map ⟦ Γ ⟧ᶜ ⟦ Γ [ i ] ⟧ʸ
continuous-prj  ε      ()
continuous-prj (Γ ₊ σ)  zero    = pr₂ , (λ _ → pr₂)
continuous-prj (Γ ₊ σ) (succ i) = prjᵢ₊₁ , cprjᵢ₊₁
 where
  prjᵢ : U ⟦ Γ ⟧ᶜ → U ⟦ Γ [ i ] ⟧ʸ
  prjᵢ = pr₁ (continuous-prj Γ i)
  prjᵢ₊₁ : U ⟦ Γ ₊ σ ⟧ᶜ → U ⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ
  prjᵢ₊₁ (xs , _) = prjᵢ xs
  cprjᵢ : continuous ⟦ Γ ⟧ᶜ ⟦ Γ [ i ] ⟧ʸ prjᵢ
  cprjᵢ = pr₂ (continuous-prj Γ i)
  cprjᵢ₊₁ : continuous ⟦ Γ ₊ σ ⟧ᶜ ⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ prjᵢ₊₁
  cprjᵢ₊₁ p pΓσ = cprjᵢ (pr₁ ∘ p) (pr₁ pΓσ)

\end{code}

Terms are interpreted as continuous maps between the corresponding interpretations.

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

\end{code}

Formula semantics: a formula in context Γ is interpreted as a predicate on
semantic environments ρ : U ⟦ Γ ⟧ᶜ.

\begin{code}

⟦_⟧ᶠ : {Γ : Cxt} → Fml Γ → U ⟦ Γ ⟧ᶜ → Set
⟦ t == u ⟧ᶠ ρ = pr₁ ⟦ t ⟧ᵐ ρ ＝ pr₁ ⟦ u ⟧ᵐ ρ
⟦ φ ∧∧ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) × (⟦ ψ ⟧ᶠ ρ)
⟦ φ →→ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) → (⟦ ψ ⟧ᶠ ρ)

\end{code}

A formula is validated by the model if it holds for every semantic environment.

\begin{code}

_is-validated : {Γ : Cxt} → Fml Γ → Set
φ is-validated = ∀ ρ → ⟦ φ ⟧ᶠ ρ

\end{code}

The uniform-continuity principle, formulated as the formula `Principle[UC]`, says that
if two binary sequences agree on their first `FAN(F)` bits, then the functional `F`
takes the same value on them.

Given an environment `ρ`, the assumption `EN` says that the interpreted term
`A＝⟦FAN•F⟧B` evaluates to `⊤`. Unfolding the recursor defining this term shows
that the interpreted sequences agree on the first `fan f` bits. The theorem
`fan-behaviour` can then be applied to conclude that `f α ＝ f β`.

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
