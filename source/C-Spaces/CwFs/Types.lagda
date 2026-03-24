Chuangjie Xu 2026

The standard example of a CwF is given by types and families of types. In specific,
contexts are types, substitutions are functions, types in context are families, and
terms are dependent functions.

\begin{code}

open import MLTT.Spartan

module C-Spaces.CwFs.Types {𝓤 : Universe} where

open import C-Spaces.CwFs.Base

TypeCwF : CwF
TypeCwF = record
  { -- Category of contexts is given by types and functions
    Con = 𝓤 ̇
  ; Sub = λ Γ Δ → Γ → Δ
  ; idSub = id
  ; _○_ = _∘_
  ; ε = 𝟙
  ; εSub = unique-to-𝟙
  ; idl = refl
  ; idr = refl
  ; ○-assoc = refl
  ; εSub-unique = refl

    -- Types are families over a context
  ; Ty = λ (Γ : 𝓤 ̇) → (Γ → 𝓤 ̇)
  ; _[_] = λ A σ x → A (σ x)
  ; ty[id] = refl
  ; ty[○] = refl
  ; Tm = λ (Γ : 𝓤 ̇) (A : Γ → 𝓤 ̇) → ((x : Γ) → A x)
  ; _⁅_⁆ = λ t σ x → t (σ x)
  ; tm[id] = refl
  ; tm[○] = refl

    -- Context extension is given by Sigma types
  ; _₊_ = λ (Γ : 𝓤 ̇) (A : Γ → 𝓤 ̇) → Σ x ꞉ Γ , A x
  ; ⟨_,_⟩ = λ σ t δ → σ δ , t δ
  ; p = pr₁
  ; q = pr₂
  ; p,-β = refl
  ; q,-β = refl
  ; p,q-η = refl
  ; ,○-distrib = refl
  }

\end{code}
