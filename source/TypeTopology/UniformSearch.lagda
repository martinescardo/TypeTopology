Ayberk Tosun
10 October 2022

Based directly on Martín Escardó's development from the `CantorSearch` module.

--------------------------------------------------------------------------------

In the `CantorSearch` module, the type `ℕ → 𝟚` is proved to be searchable for
uniformly continuous predicates. In this module, we generalise this to types
`ℕ → X`, where `X` is an arbitrary compact type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import TypeTopology.CompactTypes
open import UF.FunExt

module TypeTopology.UniformSearch (X : 𝓤 ̇ )(fe : funext 𝓤₀ 𝓤) (κ : is-compact∙ X) where

\end{code}

\section{Basic operations on streams}

\begin{code}

head : (ℕ → X) → X
head u = u 0

tail : (ℕ → X) → (ℕ → X)
tail u = u ∘ succ

infixr 9 _∷_

_∷_ : X → (ℕ → X) → (ℕ → X)
(x ∷ α) zero     = x
(x ∷ α) (succ i) = α i


cons-head-tail : (α : ℕ → X) → head α ∷ tail α ＝ α
cons-head-tail α = dfunext fe h
 where
  h : head α ∷ tail α ∼ α
  h zero     = refl
  h (succ i) = refl

\end{code}

\section{Local constancy}

\begin{code}

_＝⟦_⟧_ : (ℕ → X) → ℕ → (ℕ → X) → 𝓤 ̇
𝓊 ＝⟦ zero   ⟧ 𝓋 = 𝟙
𝓊 ＝⟦ succ n ⟧ 𝓋 = (head 𝓊 ＝ head 𝓋) × (tail 𝓊 ＝⟦ n ⟧ tail 𝓋 )

\end{code}

A map `p : ((ℕ → X) → 𝟚)` is called *locally constant* if it has a modulus of
locally constancy.

\begin{code}

_is-a-mod-of-lc-of_ : ℕ → ((ℕ → X) → 𝟚) → 𝓤 ̇
n is-a-mod-of-lc-of p = (𝓊 𝓋 : ℕ → X) → 𝓊 ＝⟦ n ⟧ 𝓋 → p 𝓊 ＝ p 𝓋

is-locally-constant : ((ℕ → X) → 𝟚) → 𝓤 ̇
is-locally-constant p = Σ n ꞉ ℕ , n is-a-mod-of-lc-of p

\end{code}

\begin{code}

cons-decreases-mod-of-lc : (p : (ℕ → X) → 𝟚)
                         → (n : ℕ)
                         → (succ n) is-a-mod-of-lc-of p
                         → (x : X) → n is-a-mod-of-lc-of (p ∘ x ∷_)
cons-decreases-mod-of-lc p n φ x 𝓊 𝓋 eq = φ (x ∷ 𝓊) (x ∷ 𝓋) (refl , eq)

\end{code}

\section{Searchability}

Since `X` is assumed to be `compact∙` it must be pointed. Call this point `x₀`:

\begin{code}

x₀ : X
x₀ = compact∙-types-are-pointed κ

\end{code}

There must be a selection functional `ϵₓ` for `X`:

\begin{code}

X-is-compact∙' : is-compact∙' X
X-is-compact∙' = compact∙-types-are-compact∙' κ

ϵₓ : (X → 𝟚) → X
ϵₓ = pr₁ X-is-compact∙'

specification-of-ϵₓ : (p : X → 𝟚)
                    → p (ϵₓ p) ＝ ₁
                    → (x : X) → p x ＝ ₁
specification-of-ϵₓ = pr₂ X-is-compact∙'

\end{code}

We now define the universal quantifier for type `X` using its selection
functional

\begin{code}

∀ₓ : (X → 𝟚) → 𝟚
∀ₓ p = p (ϵₓ p)

specification-of-∀ₓ-⇒ : (p : X → 𝟚)
                      → ∀ₓ p ＝ ₁
                      → (x : X) → p x ＝ ₁
specification-of-∀ₓ-⇒ = specification-of-ϵₓ

specification-of-∀ₓ-⇐ : (p : X → 𝟚)
                      → ((x : X) → p x ＝ ₁)
                      → ∀ₓ p ＝ ₁
specification-of-∀ₓ-⇐ p φ = φ (ϵₓ p)

\end{code}

We define the selection and universal quantification functionals for `ℕ → X`,
but only for locally constant predicates.

\begin{code}

ϵₙ : ℕ → ((ℕ → X) → 𝟚) → (ℕ → X)
∀ₙ : ℕ → ((ℕ → X) → 𝟚) → 𝟚

ϵₙ zero     p = λ _ → x₀
ϵₙ (succ n) p = y₀ ∷ ϵₙ n (λ α → p (y₀ ∷ α))
 where
  y₀ = ϵₓ λ x → ∀ₙ n λ α → p (x ∷ α)

∀ₙ n p = p (ϵₙ n p)

\end{code}

Specification of `∀ₙ`

\begin{code}

specification-of-∀ₙ-⇒ : (p : (ℕ → X) → 𝟚)
                      → (n : ℕ)
                      → n is-a-mod-of-lc-of p
                      → ((𝓊 : ℕ → X) → p 𝓊 ＝ ₁)
                      → ∀ₙ n p ＝ ₁
specification-of-∀ₙ-⇒ p n ζ φ = φ (ϵₙ n p)

\end{code}

\begin{code}

specification-of-∀ₙ-⇐ : (p : (ℕ → X) → 𝟚)
                      → (n : ℕ)
                      → n is-a-mod-of-lc-of p
                      → ∀ₙ n p ＝ ₁
                      → (𝓊 : ℕ → X) → p 𝓊 ＝ ₁
specification-of-∀ₙ-⇐ p zero     ζ φ 𝓊 = p 𝓊                 ＝⟨ ζ 𝓊 (λ _ → x₀) ⋆ ⟩
                                         p (λ _ → x₀)        ＝⟨ φ                ⟩
                                         ₁                   ∎
specification-of-∀ₙ-⇐ p (succ n) ζ φ 𝓊 = p 𝓊                 ＝⟨ † ⟩
                                         p (head 𝓊 ∷ tail 𝓊) ＝⟨ ‡ ⟩
                                         ₁                   ∎
 where
  x₁ : X
  x₁ = ϵₓ λ y → ∀ₙ n (p ∘ y ∷_)

  ♠ : ∀ₙ n (p ∘ x₁ ∷_) ＝ ₁ → (x : X) → ∀ₙ n (p ∘ x ∷_) ＝ ₁
  ♠ = specification-of-∀ₓ-⇒ λ y → ∀ₙ n (p ∘ y ∷_)

  IH : (x : X) → ∀ₙ n (p ∘ x ∷_) ＝ ₁ → (𝓋 : ℕ → X) → p (x ∷ 𝓋) ＝ ₁
  IH x = specification-of-∀ₙ-⇐ (p ∘ x ∷_) n (cons-decreases-mod-of-lc p n ζ x)

  † : p 𝓊 ＝ p (head 𝓊 ∷ tail 𝓊)
  † = ap p (cons-head-tail 𝓊 ⁻¹)

  ‡ : p (head 𝓊 ∷ tail 𝓊) ＝ ₁
  ‡ = IH (head 𝓊) (♠ φ (head 𝓊)) (tail 𝓊)

\end{code}
