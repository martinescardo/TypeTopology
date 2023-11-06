Martin Escardo & Vincent Rahli 20 May 2023

This is an adaptation of Internal.lagda written by Martin, which defines dialogue-tree⋆ without using T'
but directly using T.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.InternalWithoutOracle where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.SystemT
open import EffectfulForcing.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)

B⋆⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} {A : Type}
      → T Γ σ
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
B⋆⟦ Zero            ⟧  _ = zero⋆
B⋆⟦ Succ            ⟧  _ = succ⋆
B⋆⟦ Rec {_} {_} {σ} ⟧  _ = rec⋆ {σ}
B⋆⟦ ν i             ⟧ xs = xs i
B⋆⟦ ƛ t             ⟧ xs = λ x → B⋆⟦ t ⟧ (xs ‚‚⋆ x)
B⋆⟦ t · u           ⟧ xs = (B⋆⟦ t ⟧ xs) (B⋆⟦ u ⟧ xs)

B⋆⟦_⟧₀ : {σ : type} {A : Type} → T₀ σ → B⋆〖 σ 〗 A
B⋆⟦ t ⟧₀ = B⋆⟦ t ⟧ ⟪⟫⋆

dialogue-tree⋆ : {A : Type} → T₀ ((ι ⇒ ι) ⇒ ι) → B⋆ ℕ A
dialogue-tree⋆ t = B⋆⟦ t ⟧₀ generic⋆

\end{code}
