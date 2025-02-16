---
author: Ayberk Tosun
date-started: 2025-02-03
---

\begin{code}

{-# OPTIONS --safe #-}

open import UF.FunExt

module EffectfulForcing.Internal.PaperIndex (fe : Fun-Ext) where

open import EffectfulForcing.Internal.Correctness
  renaming (⌜dialogue⌝ to dialogueᵀ)
open import EffectfulForcing.Internal.ExtensionalEquality
open import EffectfulForcing.Internal.External
  renaming (B【_】 to 【_】𝒟; B⟦_⟧ to ⟦_⟧𝒟)
  hiding (main-lemma)
open import EffectfulForcing.Internal.Internal
  renaming (B-type〖_〗 to 〖_〗𝒟ᵀ; B-context【_】 to 【_】𝒟ᵀ; ⌜_⌝ to ⟦_⟧𝒟ᵀ;
    ⌜dialogue-tree⌝ to dialogue-treeᵀ)
open import EffectfulForcing.Internal.InternalModCont fe hiding (baire)
open import EffectfulForcing.Internal.InternalModUniCont fe hiding (main-lemma)
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
open import EffectfulForcing.MFPSAndVariations.Dialogue
  renaming (D to Dial)
  hiding (decode)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type;〖_〗; ι; _⇒_)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS
  renaming (B〖_〗 to 〖_〗𝒟)
  using (Kleisli-extension)
open import MLTT.Sigma
open import MLTT.Spartan

-- We set up these aliases to better mirror the paper

\end{code}

\section{(2) A System T Primer}

We define some aliases below to ensure consistency with the notation in the
paper. This also serves as a dictionary for looking up the notation used in the
formalization.

\begin{code}

Termᵀ : Cxt → type → 𝓤₀  ̇
Termᵀ Γ σ = T Γ σ

Termᵀ₀ : type → 𝓤₀  ̇
Termᵀ₀ σ = T₀ σ

Typeᵀ : 𝓤₀  ̇
Typeᵀ = type

Ctxᵀ : 𝓤₀  ̇
Ctxᵀ = Cxt

Definition-1 : 𝓤₀  ̇
Definition-1 = Σ Γ ꞉ Ctxᵀ , Σ σ ꞉ Typeᵀ , Termᵀ Γ σ

Definition-2a : Typeᵀ → 𝓤₀  ̇
Definition-2a = 〖_〗

Definition-2b : Ctxᵀ → 𝓤₀  ̇
Definition-2b = 【_】

Definition-2c : {Γ : Ctxᵀ} {σ : Typeᵀ} → Termᵀ Γ σ → (【 Γ 】 → 〖 σ 〗)
Definition-2c = ⟦_⟧

Definition-3 : {Γ : Ctxᵀ} → ℕ → Termᵀ Γ ι
Definition-3 = numeral

Proposition-4 : {Γ : Ctxᵀ} (γ : 【 Γ 】) (n : ℕ) → n ＝ ⟦ numeral n ⟧ γ
Proposition-4 γ n = ⟦numeral⟧ γ n ⁻¹

\end{code}

\section{(3) Oracless Effectful Forcing}

\begin{code}

Definition-5 : (I : 𝓤  ̇) → (O : 𝓥  ̇) → (X : 𝓦  ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-5 = Dial

𝒟 : 𝓤₀ ̇ → 𝓤₀ ̇
𝒟 X = Dial ℕ ℕ X

Definition-6 : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇} → Dial I O X → (I → O) → X
Definition-6 = dialogue

Definition-7a : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇}
              → ((I → O) → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-7a {𝓤} {𝓥} {𝓦} {I} {O} {X} f =
 Σ d ꞉ Dial I O X , ((α : I → O) → f α ＝ dialogue d α)

Definition-7b : {O : 𝓥  ̇} {X : 𝓦  ̇} → ((ℕ → O) → X) → 𝓥 ⊔ 𝓦  ̇
Definition-7b = is-continuous₁

Definition-7c : {O : 𝓥  ̇} {X : 𝓦  ̇} → ((ℕ → O) → X) → 𝓥 ⊔ 𝓦  ̇
Definition-7c = is-uniformly-continuous₁

\end{code}

TODO: should the definition below be generalized?
- bruno: probably but I don't know if we want to change the original file

\begin{code}

Definition-9 : {X Y : 𝓤₀  ̇}
             → (X → 𝒟 Y) → 𝒟 X → 𝒟 Y
Definition-9 = kleisli-extension

𝒟-functor : {X Y : 𝓤₀  ̇} → (X → Y) → 𝒟 X → 𝒟 Y
𝒟-functor = B-functor

Definition-10 : {X Y : 𝓤₀  ̇}
              → (X → Y) → 𝒟 X → 𝒟 Y
Definition-10 = 𝒟-functor

Definition-11 : {X : 𝓤₀  ̇} {σ : Typeᵀ} → (X → 〖 σ 〗𝒟) → 𝒟 X → 〖 σ 〗𝒟
Definition-11 = Kleisli-extension

\end{code}

Dialogue interpretation of types, contexts, and terms of System T are given in,
respectively, `Definition-12a`, `Definition-12b`, and `Definition-12c` below.

\begin{code}

Definition-12a : Typeᵀ → 𝓤₀  ̇
Definition-12a = 〖_〗𝒟

Definition-12b : Ctxᵀ → 𝓤₀  ̇
Definition-12b = 【_】𝒟

Definition-12c : {Γ : Ctxᵀ} {σ : Typeᵀ} → Termᵀ Γ σ → (【 Γ 】𝒟 → 〖 σ 〗𝒟)
Definition-12c = ⟦_⟧𝒟

Definition-13 : 𝒟 ℕ → 𝒟 ℕ
Definition-13 = generic

Definition-14 : Termᵀ₀ ((ι ⇒ ι) ⇒ ι) → 𝒟 ℕ
Definition-14 = dialogue-tree

Definition-15 : (σ : Typeᵀ) → (ℕ → ℕ) → 〖 σ 〗 → 〖 σ 〗𝒟 → Type
Definition-15 σ = R {σ}

Theorem-16 : (α : ℕ → ℕ) (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι))
           → ⟦ t ⟧₀ α ＝ dialogue (dialogue-tree t) α
Theorem-16 α t = dialogue-tree-correct t α

\end{code}

\section{(4) Dialogue Trees in System T}

\subsection{(4.1) Church-Encoded Trees in System T}

\begin{code}


𝒟ᵀ : Typeᵀ → Typeᵀ → Typeᵀ
𝒟ᵀ A σ = ⌜D⋆⌝ ι ι σ A

_ : (A : Typeᵀ) (σ : Typeᵀ) → 𝒟ᵀ A σ ＝ ((σ ⇒ A) ⇒ (((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A))
_ = λ A σ → refl {𝓤₀} {Typeᵀ} {((σ ⇒ A) ⇒ (((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A))}

ηᵀ : (A : Typeᵀ) (σ : Typeᵀ) → Termᵀ₀ (σ ⇒ 𝒟ᵀ A σ)
ηᵀ A σ = ⌜η⌝ {ι} {ι} {σ} {A}

βᵀ : (A : Typeᵀ) (σ : Typeᵀ) → Termᵀ₀ ((ι ⇒ 𝒟ᵀ A σ) ⇒ ι ⇒ 𝒟ᵀ A σ)
βᵀ A σ = ⌜β⌝ {ι} {ι} {σ} {A} {〈〉}

Definition-17a : Typeᵀ → Typeᵀ → Typeᵀ
Definition-17a A = 𝒟ᵀ A

Definition-17b : (A : Typeᵀ) (σ : Typeᵀ)
               → Termᵀ₀ (σ ⇒ 𝒟ᵀ A σ)
Definition-17b = ηᵀ

Definition-17c : (A : Typeᵀ) (σ : Typeᵀ)
               → Termᵀ₀ ((ι ⇒ 𝒟ᵀ A σ) ⇒ ι ⇒ 𝒟ᵀ A σ)
Definition-17c σ = βᵀ σ

\end{code}

The internal Kleisli extension.

\begin{code}

Definition-18 : (A : Typeᵀ) → Termᵀ₀ ((ι ⇒ 𝒟ᵀ A ι) ⇒ 𝒟ᵀ A ι ⇒ 𝒟ᵀ A ι)
Definition-18 A = ⌜kleisli-extension⌝

\end{code}

The internal functor action.

\begin{code}

Definition-19 : (A : Typeᵀ) → Termᵀ₀ ((ι ⇒ ι) ⇒ 𝒟ᵀ A ι ⇒ 𝒟ᵀ A ι)
Definition-19 A = ⌜B-functor⌝

\end{code}

The generalised internal Kleisli extension.

\begin{code}

Definition-20 : (A : Typeᵀ) (σ : Typeᵀ)
              → Termᵀ₀ ((ι ⇒ 〖 σ 〗𝒟ᵀ A) ⇒ 𝒟ᵀ A ι ⇒ 〖 σ 〗𝒟ᵀ A)
Definition-20 σ A = ⌜Kleisli-extension⌝

\end{code}

The internal dialogue translation.

\begin{code}

Definition-21a : Typeᵀ → Typeᵀ → Typeᵀ
Definition-21a A σ = 〖 σ 〗𝒟ᵀ A

Definition-21b : Typeᵀ → Ctxᵀ → Ctxᵀ
Definition-21b A Γ = 【 Γ 】𝒟ᵀ A

Definition-21c : (A : Typeᵀ)
               → (Γ : Ctxᵀ)
               → (σ : Typeᵀ)
               → Termᵀ Γ σ
               → Termᵀ (【 Γ 】𝒟ᵀ A) (〖 σ 〗𝒟ᵀ A)
Definition-21c A Γ σ = ⟦_⟧𝒟ᵀ

\end{code}

The internal generic sequence.

\begin{code}

Definition-22 : (A : Typeᵀ) → Termᵀ₀ (𝒟ᵀ A ι ⇒ 𝒟ᵀ A ι)
Definition-22 A = ⌜generic⌝

\end{code}

The internal dialogue tree operator.

\begin{code}

Definition-23 : (A : Typeᵀ) → Termᵀ₀ ((ι ⇒ ι) ⇒ ι) → Termᵀ₀ (𝒟ᵀ A ι)
Definition-23 A = dialogue-treeᵀ

\end{code}

\subsection{(4.2) Avoiding Function Extensionality}

Hereditary extensional equality.

\begin{code}

Definition-24 : (σ : type) → 〖 σ 〗 → 〖 σ 〗 → 𝓤₀  ̇
Definition-24 σ = _≡_ {σ}

\end{code}

Some properties of hereditary extensionality equality

\begin{code}

Lemma-25a : {σ : type} {a b c : 〖 σ 〗} → a ≡ b → b ≡ a
Lemma-25a = ≡-symm

Lemma-25b : {σ : type} {a b c : 〖 σ 〗} → a ≡ b → b ≡ c → a ≡ c
Lemma-25b = ≡-trans

-- TODO Lemma-25c

Lemma-26 : {σ : type} → (t : T₀ σ) → ⟦ t ⟧₀ ≡ ⟦ t ⟧₀
Lemma-26 = ≡-refl₀

\end{code}

\subsection{(4.3) Correctness of the Syntactic Translation}

The encode function, which is called `church-encode` here.

\begin{code}

Definition-27 : (A : Typeᵀ) → 𝒟 ℕ → 〖 𝒟ᵀ A ι 〗
Definition-27 A = church-encode

\end{code}

The dialogue correctness logical relation.

\begin{code}

Definition-28 : (σ : Typeᵀ) → 〖 σ 〗𝒟 → ({A : Typeᵀ} → Termᵀ₀ (〖 σ 〗𝒟ᵀ A)) → 𝓤₀ ̇
Definition-28 σ = Rnorm

\end{code}

\begin{code}

Lemma-29 : (σ : Typeᵀ)
           (t s : {A : Typeᵀ} → Termᵀ₀ (〖 σ 〗𝒟ᵀ A))
           (x : 〖 σ 〗𝒟)
         → ({A : type} → ⟦ t ⟧₀ ≡[ (〖 σ 〗𝒟ᵀ A) ] ⟦ s ⟧₀)
         → Rnorm x t
         → Rnorm x s
Lemma-29 σ t s x = Rnorm-respects-≡

-- TODO next two require changing formalisation slightly
-- Lemma-30 : {!!}
-- Lemma-30 = {!!}

-- Corollary-31 : {!!}
-- Corollary-31 = {!!}

Lemma-32 : {σ : Typeᵀ}
           (f : ℕ → 〖 σ 〗𝒟)
           (n : 𝒟 ℕ)
           (g : {A : Typeᵀ} → Termᵀ₀ (ι ⇒ (〖 σ 〗𝒟ᵀ A)))
           (m : {A : Typeᵀ} → T₀ (⌜B⌝ ι A))
         → ((x : ℕ) → Rnorm (f x) (g · numeral x))
         → Rnorm n m
         → Rnorm (Kleisli-extension f n) (⌜Kleisli-extension⌝ · g · m)
Lemma-32 f n g m h i = Rnorm-kleisli-lemma f g h n m i

Lemma-33 : {Γ : Ctxᵀ} {σ : Typeᵀ}
           (γ₁ : 【 Γ 】𝒟) (γ₂ : {A : Typeᵀ} → Sub₀ (【 Γ 】𝒟ᵀ A))
           (t : Termᵀ Γ σ)
         → Rnorms γ₁ γ₂
         → Rnorm (⟦ t ⟧𝒟 γ₁) (close ⟦ t ⟧𝒟ᵀ γ₂)
Lemma-33 = Rnorm-lemma

Lemma-34 : (A : Typeᵀ)
           (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι))
         → ⟦ dialogue-treeᵀ t ⟧₀ ≡[ ⌜B⌝ ι A ] church-encode (dialogue-tree t)
Lemma-34 A t = dialogue-tree-agreement t {A}

Definition-35 : Termᵀ₀ (((ι ⇒ ι) ⇒ ι)) → Termᵀ₀ (𝒟ᵀ ((ι ⇒ ι) ⇒ ι) ι)
Definition-35 = dialogue-treeᵀ

Lemma-36 : (d : B ℕ) (α : ℕ → ℕ)
         → dialogue d α ＝ ⟦ dialogueᵀ ⟧₀ (church-encode d) α
Lemma-36 d α = dialogues-agreement d α

\end{code}

\section{(5) Computing moduli of continuity internally}

Max question along a path.

\begin{code}

max-q = max-question

Definition-38 : B ℕ → (ℕ → ℕ) → ℕ
Definition-38 = max-q

\end{code}

Internal max question along a path.

\begin{code}

max-qᵀ = max-questionᵀ

Definition-39 : Termᵀ₀ (𝒟ᵀ ι ι ⇒ (ι ⇒ ι) ⇒ ι)
Definition-39 = max-qᵀ

\end{code}

External and internal modulus operators.

\begin{code}

Definition-41a : B ℕ → (ℕ → ℕ) → ℕ
Definition-41a = modulus

Definition-41b : Termᵀ₀ (⌜B⌝ ι ι ⇒ (ι ⇒ ι) ⇒ ι)
Definition-41b = modulusᵀ

Definition-42 : ((ℕ → ℕ) → ℕ) → (ℕ → ℕ) → ℕ → 𝓤₀  ̇
Definition-42 f α m = m is-a-modulus-of-continuity-for f at α

Lemma-43 : (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι)) (α : ℕ → ℕ)
         →  ⟦ modulusᵀ · (dialogue-treeᵀ t) ⟧₀ α
           is-a-modulus-of-continuity-for
            ⟦ t ⟧₀
           at
            α
Lemma-43 = modulusᵀ-is-a-modulus-operator

Lemma-44 : (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι)) (α : ℕ → ℕ)
         → ⟦ max-qᵀ · dialogue-treeᵀ t ⟧₀ α  ＝ max-question (dialogue-tree t) α
Lemma-44 t α = ⟦ max-qᵀ · dialogue-treeᵀ t ⟧₀ α   ＝⟨ Ⅰ ⟩
               max-question₀ (dialogue-tree t) α   ＝⟨ Ⅱ ⟩
               max-question (dialogue-tree t) α    ∎
                where
                 Ⅰ = main-lemma t α
                 Ⅱ = max-question₀-agreement (dialogue-tree t) α ⁻¹

Theorem-45 : (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι)) (α : ℕ → ℕ)
           → ⟦ modulusᵀ · (dialogue-treeᵀ t) ⟧₀ α
              is-a-modulus-of-continuity-for ⟦ t ⟧₀ at α
Theorem-45 = Lemma-43

\end{code}

\section{(6) Extending it to uniform continuity}

\begin{code}

Definition-46 : Termᵀ₀ (ι ⇒ ι) → 𝓤₀  ̇
Definition-46 = is-boolean-pointᵀ

Definition-47 : B ℕ → Dial ℕ 𝟚 ℕ
Definition-47 = prune

max-q₂  = max-boolean-question
max-q₂ᵀ = max-boolean-questionᵀ

Definition-48 : Dial ℕ 𝟚 ℕ → ℕ
Definition-48 = max-boolean-question

Definition-49 : Termᵀ₀ (𝒟ᵀ ι ι ⇒ ι)
Definition-49 = max-q₂ᵀ

-- TODO: Do we have this exact result?
-- Lemma-50 : (d : B ℕ)
--          → max-q₂ (prune d) ＝ ⟦ max-q₂ᵀ ⟧₀ (church-encode d)
-- Lemma-50 d = max-q₂ (prune d)                        ＝⟨ Ⅰ ⟩
--              max-boolean-question⋆ (church-encode d) ＝⟨ Ⅱ ⟩
--              ⟦ max-q₂ᵀ ⟧₀ (church-encode d)          ∎
--               where
--                Ⅰ = max-boolean-question⋆-agreement d
--                Ⅱ = {! max-boolean-questionᵀ-agreement (church-encode d) ⁻¹!}

\end{code}

The external modulus of uniform continuity operator.

\begin{code}

Definition-51a : Dial ℕ 𝟚 ℕ → ℕ
Definition-51a = modulusᵤ

\end{code}

The internal modulus of uniform continuity operator.

\begin{code}

Definition-51b : Termᵀ₀ ((ι ⇒ ι) ⇒ ι) → Termᵀ₀ ι
Definition-51b = modulusᵤᵀ {〈〉}

Definition-52 : ℕ → ((ℕ → ℕ) → ℕ) → 𝓤₀  ̇
Definition-52 = _is-a-modulus-of-uniform-continuity-for_

Theorem-55 : (t : Termᵀ₀ (baire ⇒ ι))
           → ⟦ modulusᵤᵀ t ⟧₀
              is-a-modulus-of-uniform-continuity-for
             ⟦ t ⟧₀
Theorem-55 t α α′ ψ ψ′ = internal-uni-mod-correct₀ t α α′ ψ ψ′

\end{code}
