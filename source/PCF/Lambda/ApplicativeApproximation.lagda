Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc

module PCF.Lambda.ApplicativeApproximation
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import PCF.Lambda.AbstractSyntax pt
open import PCF.Lambda.BigStep pt

_⊏̰_ : {σ : type} → PCF ⟨⟩ σ → PCF ⟨⟩ σ → 𝓤₀ ̇
_⊏̰_ {ι}      M N = (n : ℕ) → M ⇓ numeral n → N ⇓ numeral n
_⊏̰_ {σ ⇒ σ₁} M N = (P : PCF ⟨⟩ σ) → (M · P) ⊏̰ (N · P)

⊏̰-reflexive : {σ : type} → (M : PCF ⟨⟩ σ) → M ⊏̰ M
⊏̰-reflexive {ι}      M = λ n x → x
⊏̰-reflexive {σ ⇒ σ₁} M = λ P → ⊏̰-reflexive (M · P)

⊏̰-transitive : {σ : type} {M N L : PCF ⟨⟩ σ} → M ⊏̰ N → N ⊏̰ L → M ⊏̰ L
⊏̰-transitive {ι} {M} {N} {L} p₁ p₂ n step = γ
 where
  γ : L ⇓ numeral n
  γ = p₂ n (p₁ n step)

⊏̰-transitive {σ ⇒ σ₁} {M} {N} {L} p₁ p₂ P = γ
 where
  γ : (M · P) ⊏̰ (L · P)
  γ = ⊏̰-transitive (p₁ P) (p₂ P)

⊏̰-lemma : {σ : type} (M M' : PCF ⟨⟩ σ)
        → ((V : PCF ⟨⟩ σ) → M ⇓' V → M' ⇓' V)
        → M ⊏̰ M'
⊏̰-lemma {ι}     M M' f n x = ∥∥-functor (λ x₁ → f (numeral n) x₁) x
⊏̰-lemma {σ ⇒ τ} M M' f P   = ⊏̰-lemma (M · P) (M' · P) γ
 where
  γ : (V : PCF ⟨⟩ τ) → (M · P) ⇓' V → (M' · P) ⇓' V
  γ V (·-step {_} {_} {_} {_} {_} {E} x x₁) = ·-step M'-step x₁
   where
    M'-step : M' ⇓' ƛ E
    M'-step = f (ƛ E) x

β-⊏̰ : {σ τ : type} {M : PCF (⟨⟩ ’ σ) τ} {N : PCF ⟨⟩ σ}
    → (M [ N ]) ⊏̰ (ƛ M · N)
β-⊏̰ {σ} {τ} {M} {N} = ⊏̰-lemma (M [ N ]) (ƛ M · N) (λ V x → ·-step ƛ-id x)

fix-⊏̰ : {σ : type} {M : PCF ⟨⟩ (σ ⇒ σ)} → (M · (Fix M)) ⊏̰ (Fix M)
fix-⊏̰ {σ} {M} = ⊏̰-lemma (M · Fix M) (Fix M) (λ V x → Fix-step x)

\end{code}
