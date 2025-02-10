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
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.InternalModCont
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
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
Definition-1 = Σ Γ ꞉ Ctxᵀ , Σ σ ꞉ Typeᵀ , Termᵀ Γ σ

\end{code}

\begin{code}

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


Dial : (I : 𝓤  ̇) →  (O : 𝓥  ̇) → (X : 𝓦  ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Dial = D

Definition-5 : (I : 𝓤 ̇ ) →  (O : 𝓥  ̇ ) → (X : 𝓦  ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-5 = Dial

Definition-6 : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇} → D I O X → (I → O) → X
Definition-6 = dialogue

Definition-7a : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇}
              → ((I → O) → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-7a {𝓤} {𝓥} {𝓦} {I} {O} {X} f =
 Σ d ꞉ Dial I O X , ((α : I → O) → f α ＝ dialogue d α)

Definition-7b : {O : 𝓥  ̇} {X : 𝓦  ̇} → ((ℕ → O) → X) → 𝓥 ⊔ 𝓦  ̇
Definition-7b = is-continuous₁

\end{code}

TODO: should the definition below be generalized?

\begin{code}

Definition-9 : {I : 𝓤  ̇} {O : 𝓥  ̇} {X Y : 𝓦  ̇}
             → (X → B Y) → B X → B Y
Definition-9 = kleisli-extension

\end{code}

TODO: is there an abbrevation for Definition 10 below?

\begin{code}

Definition-10 : {X Y : 𝓤₀  ̇}
              → (X → Y)
              → B X
              → B Y
Definition-10 f = kleisli-extension (η ∘ f)

-- TODO
-- Definition-11 : {!!}
-- Definition-11 = {!!}

\end{code}

Dialogue interpretation of types, contexts, and terms of System T are given in,
respectively, `Definition-12a`, `Definition-12b`, and `Definition-12c` below.

\begin{code}

Definition-12a : type → 𝓤₀  ̇
Definition-12a = 〖_〗

Definition-12b : type → 𝓤₀  ̇
Definition-12b = 〖_〗

Definition-13 : B ℕ → B ℕ
Definition-13 = generic

Definition-14 : T₀ ((ι ⇒ ι) ⇒ ι) → B ℕ
Definition-14 = dialogue-tree

-- Definition-15 : (σ : type) (α : ℕ → ℕ) (x : 〖 σ 〗) → {!!}
-- Definition-15 σ α x = Rnorm {σ}

Theorem-16 : (α : ℕ → ℕ) (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι))
           → ⟦ t ⟧₀ α ＝ dialogue (dialogue-tree t) α
Theorem-16 α t = dialogue-tree-correct t α

\end{code}

\subsection{(4.1) Church-Encoded Trees in System T}

\section{Dialogue Trees in System T}

For Section 4.1, we work in a module with a fixed type `A`.

\begin{code}


𝒟ᵀ : Typeᵀ → Typeᵀ → Typeᵀ
𝒟ᵀ A σ = ⌜D⋆⌝ ι ι σ A

module _ (A : Typeᵀ) where

 _ : (A : Typeᵀ) (σ : Typeᵀ) → 𝒟ᵀ A σ ＝ ((σ ⇒ A) ⇒ (((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A))
 _ = λ A σ → refl {𝓤₀} {Typeᵀ} {((σ ⇒ A) ⇒ (((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A))}

 ηᵀ : (σ : Typeᵀ) → Termᵀ₀ (σ ⇒ 𝒟ᵀ A σ)
 ηᵀ σ = ⌜η⌝ {ι} {ι} {σ} {A}

 βᵀ : (σ : Typeᵀ) → Termᵀ₀ ((ι ⇒ 𝒟ᵀ A σ) ⇒ ι ⇒ 𝒟ᵀ A σ)
 βᵀ σ = ⌜β⌝ {ι} {ι} {σ} {A} {〈〉}

 Definition-17a : Typeᵀ → Typeᵀ
 Definition-17a = 𝒟ᵀ A

 Definition-17b : (σ : Typeᵀ)
                → Termᵀ₀ (σ ⇒ 𝒟ᵀ A σ)
 Definition-17b = ηᵀ

 Definition-17c : (σ : Typeᵀ)
                → Termᵀ₀ ((ι ⇒ 𝒟ᵀ A σ) ⇒ ι ⇒ 𝒟ᵀ A σ)
 Definition-17c σ = βᵀ σ

\end{code}

The internal Kleisli extension.

\begin{code}

 Definition-18 : Termᵀ₀ ((ι ⇒ 𝒟ᵀ ι ι) ⇒ 𝒟ᵀ ι ι ⇒ 𝒟ᵀ ι ι)
 Definition-18 = ⌜kleisli-extension⌝

\end{code}

The internal functor action.

\begin{code}

 Definition-19 : Termᵀ₀ ((ι ⇒ ι) ⇒ 𝒟ᵀ A ι ⇒ 𝒟ᵀ A ι)
 Definition-19 = ⌜B-functor⌝

\end{code}

The generalised internal Kleisli extension.

\begin{code}

 Definition-20 : (σ : Typeᵀ)
               → Termᵀ₀ ((ι ⇒ B-type〖 σ 〗 A) ⇒ 𝒟ᵀ A ι ⇒ B-type〖 σ 〗 A)
 Definition-20 σ = ⌜Kleisli-extension⌝

\end{code}

The internal dialogue translation.

\begin{code}

 Definition-21 : {!!}
 Definition-21 = {!!}

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

-- Definition-27 : {σ : type} {A : type} → B ℕ → 〖 𝒟ᵀ A ι 〗
-- Definition-27 = {!!}

\end{code}

\begin{code}

-- Definition-35 : T₀ (𝒟ᵀ ((ι ⇒ ι) ⇒ ι) (ι ⇒ (ι ⇒ ι) ⇒ ι))
-- Definition-35 = {!⌜dialogue-tree⌝!}

\end{code}

\section{(5) Computing moduli of continuity internally}

\begin{code}

Definition-38 : B ℕ → (ℕ → ℕ) → ℕ
Definition-38 = max-question fe

\end{code}
