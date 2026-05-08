Chuangjie Xu 2026

The standard example of a CwF is given by types and families of types. In specific,
contexts are types, substitutions are functions, types in context are families, and
terms are dependent functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module C-Spaces.CwFs.Types {𝓤 : Universe} where

open import C-Spaces.CwFs.Base

TypeCwF : CwF
TypeCwF = record
  { structure = record
    { -- Category of contexts is given by types and functions
      Con = 𝓤 ̇
    ; Sub = λ Γ Δ → Γ → Δ
    ; idSub = id
    ; _○_ = _∘_
    ; ε = 𝟙
    ; εSub = unique-to-𝟙

      -- Types are families over a context
    ; Ty = λ (Γ : 𝓤 ̇) → (Γ → 𝓤 ̇)
    ; _[_] = λ A σ x → A (σ x)
    ; Tm = λ (Γ : 𝓤 ̇) (A : Γ → 𝓤 ̇) → ((x : Γ) → A x)
    ; _⁅_⁆ = λ t σ x → t (σ x)

      -- Context extension is given by Sigma types
    ; _₊_ = λ (Γ : 𝓤 ̇) (A : Γ → 𝓤 ̇) → Σ x ꞉ Γ , A x
    ; ⟨_,_⟩ = λ σ t δ → σ δ , t δ
    ; p = pr₁
    ; q = pr₂
    }

  ; laws = record
    { idl = refl
    ; idr = refl
    ; ○-assoc = refl
    ; εSub-unique = refl
    ; ty[id] = refl
    ; ty[○] = refl
    ; tm[id] = refl
    ; tm[○] = refl
    ; p,-β = refl
    ; q,-β = refl
    ; p,q-η = refl
    ; ,○-distrib = refl
    }
  }

\end{code}
