Chuangjie Xu 2026

This module defines the basic structure of a Category with Family (CwF).
Additional structure such as Pi types, Sigma types, and other type 
constructors are developed in separate, specialized modules to maintain 
modularity and clarity of the core definitions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.CwFs.Base where

open import MLTT.Spartan

record CwFStructure : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    -- Category of contexts
    Con : 𝓤 ̇
    Sub : Con → Con → 𝓥 ̇
    idSub : {Γ : Con} → Sub Γ Γ
    _○_ : {Γ Δ Θ : Con} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ

    -- Terminal object, i.e., empty context
    ε : Con
    εSub : {Γ : Con} → Sub Γ ε

    -- Type functor
    Ty : Con → 𝓤 ̇
    _[_] : {Γ Δ : Con} → Ty Γ → Sub Δ Γ → Ty Δ

    -- Term functor
    Tm : (Γ : Con) → Ty Γ → 𝓥 ̇
    _⁅_⁆ : {Γ Δ : Con} {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
    
    -- Context extension
    _₊_ : (Γ : Con) → Ty Γ → Con
    ⟨_,_⟩ : {Γ Δ : Con} {A : Ty Γ}
          → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]) → Sub Δ (Γ ₊ A)
    p : {Γ : Con} {A : Ty Γ} → Sub (Γ ₊ A) Γ
    q : {Γ : Con} {A : Ty Γ} → Tm (Γ ₊ A) (A [ p ])


record CwFLaws {𝓤 : Universe} {𝓥 : Universe}
               (S : CwFStructure {𝓤} {𝓥})
               : (𝓤 ⊔ 𝓥)⁺ ̇ where
  open CwFStructure S
  field
    -- Rules for substitution
    idl : {Γ Δ : Con} {σ : Sub Γ Δ}
        → idSub ○ σ ＝ σ
    idr : {Γ Δ : Con} {σ : Sub Γ Δ}
        → σ ○ idSub ＝ σ
    ○-assoc : {Γ Δ Θ Ξ : Con} {σ : Sub Θ Ξ} {τ : Sub Δ Θ} {ρ : Sub Γ Δ}
            → (σ ○ τ) ○ ρ ＝ σ ○ (τ ○ ρ)
    εSub-unique : {Γ : Con} {σ : Sub Γ ε}
                → σ ＝ εSub

    -- Substitution laws for types
    ty[id] : {Γ : Con} {A : Ty Γ}
           → A [ idSub ] ＝ A
    ty[○]  : {Γ Δ Θ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
           → A [ σ ○ τ ] ＝ A [ σ ] [ τ ]

    -- Substitution laws for terms
    tm[id] : {Γ : Con} {A : Ty Γ} {t : Tm Γ A}
           → transport (Tm Γ) ty[id]
             (t ⁅ idSub ⁆) ＝ t
    tm[○] : {Γ Δ Θ : Con} {A : Ty Γ} {t : Tm Γ A} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
           → transport (Tm Θ) ty[○]
             (t ⁅ σ ○ τ ⁆) ＝ t ⁅ σ ⁆ ⁅ τ ⁆

    -- Laws for context extension
    p,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
         → p ○ ⟨ σ , t ⟩ ＝ σ
    q,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
         → transport (Tm Δ) {(A [ p ]) [ ⟨ σ , t ⟩ ]} (ty[○] ⁻¹ ∙ ap (A [_]) p,-β)
          (q ⁅ ⟨ σ , t ⟩ ⁆) ＝ t
    p,q-η : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])}
          → ⟨ p , q ⟩ ＝ idSub {Γ ₊ A}
    ,○-distrib : {Γ Δ Θ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ])} {τ : Sub Θ Δ}
               → ⟨ σ , t ⟩ ○ τ ＝ ⟨ σ ○ τ , transport (Tm Θ) {(A [ σ ]) [ τ ]} {A [ σ ○ τ ]} (ty[○] ⁻¹)
                                           (t ⁅ τ ⁆) ⟩

record CwF : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    structure : CwFStructure {𝓤} {𝓥}
    laws : CwFLaws structure

  open CwFStructure structure public
  open CwFLaws laws public

\end{code}
