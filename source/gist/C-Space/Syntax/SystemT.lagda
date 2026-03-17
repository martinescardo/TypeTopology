Chuangjie Xu 2013 (updated and ported to TypeTopology in 2025)

This module collects the bare syntax of Godel's System T used throughout the
C-space development.

It is intentionally syntax-only: there are no reduction rules, typing
judgements, or semantic interpretations here. Those belong in the modules that
use the language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.C-Space.Syntax.SystemT where

open import MLTT.Spartan

\end{code}

Types

The simple types of System T are generated from booleans, natural numbers,
binary products, and function spaces.

\begin{code}

infixr 10 _⊠_
infixr 10 _⇨_

data Ty : Set where
 ② : Ty
 Ⓝ : Ty
 _⊠_ : Ty → Ty → Ty
 _⇨_ : Ty → Ty → Ty

\end{code}

Contexts and variables

Contexts are represented as snoc-lists. The operation `Γ ₊ σ` extends the
context `Γ` with a fresh variable of type `σ`.

Variables are represented by de Bruijn indices. Since the context is a
snoc-list, `zero` refers to the most recently added variable and `succ`
steps to the left in the context.

\begin{code}

infixl 10 _₊_

data Cxt : Set where
 ε : Cxt
 _₊_ : Cxt → Ty → Cxt

length : Cxt → ℕ
length ε = zero
length (Γ ₊ _) = succ (length Γ)

data Fin : ℕ → Set where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → Fin n → Fin (succ n)

_[_] : (Γ : Cxt) → Fin (length Γ) → Ty
ε        [ () ]
(xs ₊ x) [ zero ]   = x
(xs ₊ x) [ succ i ] = xs [ i ]

\end{code}

Terms

The term formers are the standard constants and constructors of System T:
boolean constants and conditionals, natural numbers with primitive recursion,
binary products, lambda abstraction, and application.

\begin{code}

infixl 10 _·_

data Tm : Cxt → Ty → Set where
 VAR  :  {Γ : Cxt}           → (i : Fin (length Γ)) → Tm Γ (Γ [ i ])
 ⊥    :  {Γ : Cxt}           → Tm Γ ②
 ⊤    :  {Γ : Cxt}           → Tm Γ ②
 IF   :  {Γ : Cxt}{σ : Ty}   → Tm Γ (② ⇨ σ ⇨ σ ⇨ σ)
 ZERO :  {Γ : Cxt}           → Tm Γ Ⓝ
 SUCC :  {Γ : Cxt}           → Tm Γ (Ⓝ ⇨ Ⓝ)
 REC  :  {Γ : Cxt}{σ : Ty}   → Tm Γ (σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ)
 PAIR :  {Γ : Cxt}{σ τ : Ty} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ⊠ τ)
 PRJ₁ :  {Γ : Cxt}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ σ
 PRJ₂ :  {Γ : Cxt}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ τ
 LAM  :  {Γ : Cxt}{σ τ : Ty} → Tm (Γ ₊ σ) τ → Tm Γ (σ ⇨ τ)
 _·_  :  {Γ : Cxt}{σ τ : Ty} → Tm Γ (σ ⇨ τ) → Tm Γ σ → Tm Γ τ

\end{code}
