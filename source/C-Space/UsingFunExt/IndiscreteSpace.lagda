Chuangjie Xu 2014 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (naive-funext)

module C-Space.UsingFunExt.IndiscreteSpace (fe : naive-funext 𝓤₀ 𝓤₀) where

open import UF.Base

open import C-Space.Preliminaries.Sequence
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.Coproduct fe

\end{code}

Indiscrete C-spaces

\begin{code}

indiscrete : Space → Set
indiscrete X = ∀(p : ₂ℕ → U X) → p ∈ Probe X

\end{code}

The arbitrary product of indiscrete spaces is indiscrete.

\begin{code}

Proposition[∏-indiscrete] :

  ∀{I : Set} (X : I → Space) → (∀ i → indiscrete (X i)) → indiscrete (∏ X)

Proposition[∏-indiscrete] X indX p = goal
 where
  goal : p ∈ Probe (∏ X)
      -- ∀ i → (λ α → p α i) ∈ Probe (X i)
  goal i = indX i (λ α → p α i)

\end{code}

The coproduct of countable family of indiscrete spaces is indiscrete, if UC
holds in Set.

\begin{code}

Proposition[UC-∐-indiscrete] : Axiom[UC-ℕ] →

  ∀(X : ℕ → Space) → (∀(i : ℕ) → indiscrete (X i)) → indiscrete (∐ X)

Proposition[UC-∐-indiscrete] uc X indX p = n , prf
 where
  claim₀ : locally-constant (pr₁ ∘ p)
  claim₀ = uc (pr₁ ∘ p)
  n : ℕ
  n = pr₁ claim₀
  claim₁ : ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → pr₁(p α) ＝ pr₁(p β)
  claim₁ = pr₁ (pr₂ claim₀)
  prf : ∀(s : ₂Fin n) → Σ \(i : ℕ) → Σ \(q : ₂ℕ → U(X i)) →
          (q ∈ Probe (X i)) × (∀(α : ₂ℕ) → p(cons s α) ＝ (i , q α))
  prf s = i , q , sclaim₀ , sclaim₁
   where
    i : ℕ
    i = pr₁(p(cons s 0̄))
    e₀ : ∀(α : ₂ℕ) → pr₁(p(cons s α)) ＝ i
    e₀ α = claim₁ (cons s α) (cons s 0̄) (Lemma[cons-＝⟦⟧] s α 0̄)
    q : ₂ℕ → U(X i)
    q α = transport (U ∘ X) (e₀ α) (pr₂(p(cons s α)))
    sclaim₀ : q ∈ Probe(X i)
    sclaim₀ = indX i q
    sclaim₁ : ∀(α : ₂ℕ) → p(cons s α) ＝ (i , q α)
    sclaim₁ α = to-Σ-＝ (e₀ α , refl)

\end{code}
