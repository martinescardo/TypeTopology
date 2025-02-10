---
author: Ayberk Tosun
date-started: 2025-02-03
---

\begin{code}

{-# OPTIONS --safe #-}

open import UF.FunExt

module EffectfulForcing.Internal.PaperIndex (fe : Fun-Ext) where

open import EffectfulForcing.Internal.Correctness
open import EffectfulForcing.Internal.ExtensionalEquality
open import EffectfulForcing.Internal.External
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.InternalModCont
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type;〖_〗; ι; _⇒_)
open import MLTT.Sigma
open import MLTT.Spartan

\end{code}

\section{A System T Primer}

We define some aliases below to ensure consistency with the notation in the
paper. This also serves as a dictionary for looking up the notation used in the
formalization.

\begin{code}

Termᵀ : Cxt → type → 𝓤₀  ̇
Termᵀ Γ σ = T Γ σ

Termᵀ₀ : type → 𝓤₀  ̇
Termᵀ₀ σ = Termᵀ 〈〉 σ

Typeᵀ : 𝓤₀  ̇
Typeᵀ = type

Ctxᵀ : 𝓤₀  ̇
Ctxᵀ = Cxt

Definition-1 : 𝓤₀  ̇
Definition-1 = Σ Γ ꞉ Cxt , Σ σ ꞉ type , T Γ σ

Definition-2 : {Γ : Cxt} {σ : type}
             → T Γ σ
             → (【 Γ 】 → 〖 σ 〗)
Definition-2 = ⟦_⟧

Definition-3 : {Γ : Cxt} → ℕ → T Γ ι
Definition-3 = numeral

Proposition-4 : {Γ : Cxt} (γ : 【 Γ 】) (n : ℕ) → n ＝ ⟦ numeral n ⟧ γ
Proposition-4 γ n = ⟦numeral⟧ γ n ⁻¹

\end{code}

\section{Oracless Effectful Forcing}

\begin{code}

Definition-5 : (I : 𝓤 ̇ ) →  (O : 𝓥  ̇ ) → (X : 𝓦  ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-5 = D

Definition-6 : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇} → D I O X → (I → O) → X
Definition-6 = dialogue

-- Definition-7a : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇}
--               → ((I → O) → X)
--               → {!!}
-- Definition-7a f = {!!}

\end{code}

\begin{code}

Definition-9 : {X : 𝓤  ̇} {Y : 𝓥  ̇} → (X → B Y) → B X → B Y
Definition-9 = kleisli-extension

Definition-10 : {X Y : 𝓤₀  ̇}
              → (X → Y)
              → B X
              → B Y
Definition-10 f = kleisli-extension (η ∘ f)

-- Definition-11 : {!!}
-- Definition-11 = {!!}

Definition-13 : B ℕ → B ℕ
Definition-13 = generic

Definition-14 : T₀ ((ι ⇒ ι) ⇒ ι) → B ℕ
Definition-14 = dialogue-tree

-- Definition-15 : {!!}
-- Definition-15 = {!!}

\end{code}

\section{Dialogue Trees in System T}

\begin{code}

𝒟ᵀ : type → type → type
𝒟ᵀ A σ = (σ ⇒ A) ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A

-- ηᵀ : {!!}
-- ηᵀ = {!!}

Definition-17a : type → type → type
Definition-17a A σ = 𝒟ᵀ A σ

Definition-17b : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇} {A : 𝓣  ̇}
               → (σ : type)
               → T₀ (σ ⇒ {!B!})
Definition-17b = {!⌜η⌝!}

Definition-17c : {!!}
Definition-17c = {!!}

\end{code}

\begin{code}

Definition-23 : (A : type) → T₀ ((ι ⇒ ι) ⇒ ι) → T₀ (𝒟ᵀ A ι)
Definition-23 A = ⌜dialogue-tree⌝ {A}

\end{code}

Hereditary extensional equality.

\begin{code}

Definition-24 : (σ : type) → 〖 σ 〗 → 〖 σ 〗 → 𝓤₀  ̇
Definition-24 σ = _≡_ {σ}

\end{code}

\begin{code}

Lemma-25a : {σ : type} {a b c : 〖 σ 〗} → a ≡ b → b ≡ a
Lemma-25a = ≡-symm

Lemma-25b : {σ : type} {a b c : 〖 σ 〗} → a ≡ b → b ≡ c → a ≡ c
Lemma-25b = ≡-trans

Lemma-26 : {σ : type} → (t : T₀ σ) → ⟦ t ⟧₀ ≡ ⟦ t ⟧₀
Lemma-26 = ≡-refl₀

\end{code}

\subsection{(4.3) Correctness of the Syntactic Translation}

\begin{code}

Definition-27 : {σ : type} {A : type} → B ℕ → 〖 𝒟ᵀ A ι 〗
Definition-27 = {!!}

\end{code}

\begin{code}

Definition-35 : T₀ (𝒟ᵀ ((ι ⇒ ι) ⇒ ι) (ι ⇒ (ι ⇒ ι) ⇒ ι))
Definition-35 = {!⌜dialogue-tree⌝!}

\end{code}

\section{(5) Computing moduli of continuity internally}

\begin{code}

Definition-38 : B ℕ → (ℕ → ℕ) → ℕ
Definition-38 = max-question fe

\end{code}
