Chuangjie Xu 2013 (update in February 2015, ported to TypeTopology in 2025)

This module extends the shared syntax of System T with a constant for the Fan
functional.

Like the base `SystemT` module, this file is syntax-only. It also includes a
small formula language and a formalization of the uniform-continuity principle
inside the extended language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Space.Syntax.SystemTWithFan where

open import MLTT.Spartan

open import C-Space.Syntax.SystemT hiding (Tm) public

\end{code}

Terms

These are the System T terms together with one extra constant, `FAN`, of type
`(((Ⓝ ⇨ ②) ⇨ Ⓝ) ⇨ Ⓝ)`.

\begin{code}

infixl 10 _·_

data Tm : Cxt → Ty → Set where
 VAR  : {Γ : Cxt}            → (i : Fin (length Γ)) → Tm Γ (Γ [ i ])
 ⊥    : {Γ : Cxt}            → Tm Γ ②
 ⊤    : {Γ : Cxt}            → Tm Γ ②
 IF   : {Γ : Cxt} {σ : Ty}   → Tm Γ (② ⇨ σ ⇨ σ ⇨ σ)
 ZERO : {Γ : Cxt}            → Tm Γ Ⓝ
 SUCC : {Γ : Cxt}            → Tm Γ (Ⓝ ⇨ Ⓝ)
 REC  : {Γ : Cxt} {σ : Ty}   → Tm Γ (σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ)
 PAIR : {Γ : Cxt} {σ τ : Ty} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ⊠ τ)
 PRJ₁ : {Γ : Cxt} {σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ σ
 PRJ₂ : {Γ : Cxt} {σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ τ
 LAM  : {Γ : Cxt} {σ τ : Ty} → Tm (Γ ₊ σ) τ → Tm Γ (σ ⇨ τ)
 _·_  : {Γ : Cxt} {σ τ : Ty} → Tm Γ (σ ⇨ τ) → Tm Γ σ → Tm Γ τ
 FAN  : {Γ : Cxt}            → Tm Γ (((Ⓝ ⇨ ②) ⇨ Ⓝ) ⇨ Ⓝ)

\end{code}

Formulas

We use a minimal formula language with equality, conjunction, and implication.

\begin{code}

infix  10 _==_
infixr 10 _→→_
infixl 10 _∧∧_

data Fml : Cxt → Set where
 _==_ : {Γ : Cxt}{σ : Ty} → Tm Γ σ → Tm Γ σ → Fml Γ
 _∧∧_ : {Γ : Cxt}         → Fml Γ  → Fml Γ  → Fml Γ
 _→→_ : {Γ : Cxt}         → Fml Γ  → Fml Γ  → Fml Γ

\end{code}

The uniform-continuity principle in the object language

To keep the main statement readable, we name the types that occur in it.

\begin{code}

EQ : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
EQ B₀ B₁ = IF · B₀ · (IF · B₁ · ⊤ · ⊥) · B₁

MIN : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
MIN B₀ B₁ = IF · B₀ · ⊥ · B₁

-- The context consists of a function F : Cantor -> Nat and two binary
-- sequences A and B.
Γ : Cxt
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = VAR (succ (succ zero))

A B : Tm Γ (Ⓝ ⇨ ②)
A = VAR (succ zero)
B = VAR zero

-- In the body of the recursor we work in the extended context
--   Γ , n : Nat , b : ②
-- and refer back to the original sequences A and B.
A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = VAR (succ (succ (succ zero)))
B' = VAR (succ (succ zero))

-- Boolean predicate expressing that A and B agree on their first FAN(F) bits.
-- It is computed by primitive recursion on FAN · F, starting from ⊤ and
-- conjoining the equality test at each index.
step : Tm Γ (Ⓝ ⇨ ② ⇨ ②)
step = LAM (LAM (MIN (EQ (A' · (VAR (succ zero)))
                         (B' · (VAR (succ zero))))
                     (VAR zero)))
A＝⟦FAN•F⟧B : Tm Γ ②
A＝⟦FAN•F⟧B = REC · ⊤ · step · (FAN · F)

-- Uniform continuity principle: If A and B agree on their first FAN(F) bits,
-- then F takes the same value on A and B.
Principle[UC] : Fml Γ
Principle[UC] = (A＝⟦FAN•F⟧B == ⊤) →→ ((F · A) == (F · B))

\end{code}
