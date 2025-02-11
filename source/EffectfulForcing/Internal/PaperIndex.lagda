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
open import EffectfulForcing.Internal.External hiding (main-lemma)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.InternalModCont fe hiding (baire)
open import EffectfulForcing.Internal.InternalModUniCont fe hiding (main-lemma)
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
open import EffectfulForcing.MFPSAndVariations.Dialogue hiding (decode)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type;〖_〗; ι; _⇒_)
open import MLTT.Sigma
open import MLTT.Spartan

\end{code}

\section{(1) A System T Primer}

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

\section{(2) Oracless Effectful Forcing}

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

 Definition-21a : Typeᵀ → Typeᵀ
 Definition-21a σ = B-type〖 σ 〗 A

 Definition-21b : Ctxᵀ → Ctxᵀ
 Definition-21b Γ = B-context【 Γ 】 A

 Definition-21c : (Γ : Ctxᵀ)
                → (σ : Typeᵀ)
                → Termᵀ Γ σ
                → Termᵀ (B-context【 Γ 】 A) (B-type〖 σ 〗 A)
 Definition-21c Γ σ = ⌜_⌝

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

Lemma-26 : {σ : type} → (t : T₀ σ) → ⟦ t ⟧₀ ≡ ⟦ t ⟧₀
Lemma-26 = ≡-refl₀

\end{code}

\subsection{(4.3) Correctness of the Syntactic Translation}

\begin{code}

-- TODO: I could not find this.
Definition-27 : (A : Typeᵀ) → Dial ℕ ℕ ℕ → 〖 𝒟ᵀ A ι 〗
Definition-27 = {!church-encode!}

Definition-28 : (σ : Typeᵀ) → 〖 σ 〗 → Typeᵀ → Termᵀ₀ σ
Definition-28 σ t = {!!}

Lemma-29 : {!!}
Lemma-29 = {!!}

Lemma-30 : {!!}
Lemma-30 = {!!}

Corollary-31 : {!!}
Corollary-31 = {!!}

Lemma-34 : {!!}
Lemma-34 = {!!}

dialogue-treeᵀ : {Γ : Cxt}
               → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))
               → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
dialogue-treeᵀ = ⌜dialogue⌝

Definition-35 : Termᵀ₀ ((⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))) → Termᵀ₀ (((ι ⇒ ι) ⇒ ι))
Definition-35 = ⌜dialogue⌝

Lemma-36 : (d : B ℕ) (α : ℕ → ℕ)
         → dialogue d α ＝ dialogue⋆ (church-encode d) α
Lemma-36 d α = dialogues-agreement d α

\end{code}

\begin{code}

-- Definition-35 : T₀ (𝒟ᵀ ((ι ⇒ ι) ⇒ ι) (ι ⇒ (ι ⇒ ι) ⇒ ι))
-- Definition-35 = {!⌜dialogue-tree⌝!}

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

Definition-39 : {!!}
Definition-39 = {!!}

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
         →  ⟦ modulusᵀ · (⌜dialogue-tree⌝ t) ⟧₀ α
           is-a-modulus-of-continuity-for
            ⟦ t ⟧₀
           at
            α
Lemma-43 = modulusᵀ-is-a-modulus-operator

Lemma-44 : (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι)) (α : ℕ → ℕ)
         → ⟦ max-qᵀ · ⌜dialogue-tree⌝ t ⟧₀ α  ＝ max-question (dialogue-tree t) α
Lemma-44 t α = ⟦ max-qᵀ · ⌜dialogue-tree⌝ t ⟧₀ α   ＝⟨ Ⅰ ⟩
               max-question₀ (dialogue-tree t) α   ＝⟨ Ⅱ ⟩
               max-question (dialogue-tree t) α    ∎
                where
                 Ⅰ = main-lemma t α
                 Ⅱ = max-question₀-agreement (dialogue-tree t) α ⁻¹

Theorem-45 : (t : Termᵀ₀ ((ι ⇒ ι) ⇒ ι)) (α : ℕ → ℕ)
           → ⟦ modulusᵀ · (⌜dialogue-tree⌝ t) ⟧₀ α
              is-a-modulus-of-continuity-for ⟦ t ⟧₀ at α
Theorem-45 = Lemma-43

\end{code}

\section{(6) Extending it to uniform continuity}

\begin{code}

Definition-46 : Termᵀ₀ (ι ⇒ ι) → 𝓤₀  ̇
Definition-46 = is-boolean-pointᵀ

Definition-47 : B ℕ → D ℕ 𝟚 ℕ
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

Definition-52 : ℕ → ((ℕ → 𝟚) → ℕ) → 𝓤₀  ̇
Definition-52 = _is-a-modulus-of-uniform-continuity-for_

Theorem-55 : {!!}
Theorem-55 = {!!}

\end{code}
