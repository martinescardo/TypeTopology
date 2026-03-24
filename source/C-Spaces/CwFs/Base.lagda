Chuangjie Xu 2026

This module defines the basic structure of a Category with Family (CwF).
Additional structure such as Pi types, Sigma types, and other type 
constructors are developed in separate, specialized modules to maintain 
modularity and clarity of the core definitions.

\begin{code}

module C-Spaces.CwFs.Base where

open import MLTT.Spartan

record CwF : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    -- Category of contexts
    Con : 𝓤 ̇
    Sub : Con → Con → 𝓥 ̇
    idSub : {Γ : Con} → Sub Γ Γ
    _○_ : {Γ Δ Θ : Con} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
    -- Terminal object, i.e., empty context
    ε : Con
    εSub : {Γ : Con} → Sub Γ ε
    -- Rules for substitution
    idl : {Γ Δ : Con} {σ : Sub Γ Δ}
        → idSub ○ σ ＝ σ
    idr : {Γ Δ : Con} {σ : Sub Γ Δ}
        → σ ○ idSub ＝ σ
    ○-assoc : {Γ Δ Θ Ξ : Con} {σ : Sub Θ Ξ} {τ : Sub Δ Θ} {ρ : Sub Γ Δ}
            → (σ ○ τ) ○ ρ ＝ σ ○ (τ ○ ρ)
    εSub-unique : {Γ : Con} {σ : Sub Γ ε}
                → σ ＝ εSub

    -- Type functor
    Ty : Con → 𝓤 ̇
    _[_] : {Γ Δ : Con} → Ty Γ → Sub Δ Γ → Ty Δ
    -- Substitution laws for types
    ty[id] : {Γ : Con} {A : Ty Γ}
           → A [ idSub ] ＝ A
    ty[○]  : {Γ Δ Θ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
           → A [ σ ○ τ ] ＝ A [ σ ] [ τ ]

    -- Term functor
    Tm : (Γ : Con) → Ty Γ → 𝓥 ̇
    _⁅_⁆ : {Γ Δ : Con} {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
    -- Substitution laws for terms
    tm[id] : {Γ : Con} {A : Ty Γ} {t : Tm Γ A}
           → transport (Tm Γ) ty[id]
             (t ⁅ idSub ⁆) ＝ t
    tm[○] : {Γ Δ Θ : Con} {A : Ty Γ} {t : Tm Γ A} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
           → transport (Tm Θ) ty[○]
             (t ⁅ σ ○ τ ⁆) ＝ t ⁅ σ ⁆ ⁅ τ ⁆
    
    -- Context extension
    _₊_ : (Γ : Con) → Ty Γ → Con
    ⟨_,_⟩ : {Γ Δ : Con} {A : Ty Γ}
          → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]) → Sub Δ (Γ ₊ A)
    p : {Γ : Con} {A : Ty Γ} → Sub (Γ ₊ A) Γ
    q : {Γ : Con} {A : Ty Γ} → Tm (Γ ₊ A) (A [ p ])
    -- Laws for context extension
    p,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
         → p ○ ⟨ σ , t ⟩ ＝ σ
    q,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
         → transport (Tm Δ) (ty[○] ⁻¹ ∙ ap (A [_]) p,-β)
          (q ⁅ ⟨ σ , t ⟩ ⁆) ＝ t
    p,q-η : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
          → ⟨ p , q ⟩ ＝ idSub {Γ ₊ A}
    ,○-distrib : {Γ Δ Θ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])} {τ : Sub Θ Δ}
               → ⟨ σ , t ⟩ ○ τ ＝ ⟨ σ ○ τ , transport (Tm Θ) (ty[○] ⁻¹)
                                           (t ⁅ τ ⁆) ⟩

open CwF public

\end{code}
