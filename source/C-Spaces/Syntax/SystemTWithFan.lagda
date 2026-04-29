Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

This module extends the shared syntax of System T with a constant for the Fan
functional.

Like the base `SystemT` module, this file is syntax-only. It also includes a
small formula language and a formalization of the uniform-continuity principle
inside the extended language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.Syntax.SystemTWithFan where


open import C-Spaces.Syntax.SystemT hiding (Tm) public

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

To formulate uniform continuity in System T, we define some auxiliary functions:
 - `EQ` compares two booleans and
 - `MIN` propagates failure while scanning initial segments of binary sequences.

\begin{code}

EQ : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
EQ B₀ B₁ = IF · B₀ · (IF · B₁ · ⊤ · ⊥) · B₁

MIN : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
MIN B₀ B₁ = IF · B₀ · ⊥ · B₁

\end{code}

To state the uniform-continuity principle, we work in a context consisting of a
functional `F : (Ⓝ ⇨ ②) ⇨ Ⓝ` together with two binary sequences `A` and `B`.

\begin{code}

Γ : Cxt
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = VAR (succ (succ zero))

A B : Tm Γ (Ⓝ ⇨ ②)
A = VAR (succ zero)
B = VAR zero

\end{code}

To define the boolean term expressing that `A` and `B` agree on their first
`FAN(F)` bits, we use primitive recursion on `FAN · F`. Its step term is formed
in the extended context consisting of the original context `Γ` together with a
natural number index and an accumulator boolean. The terms `A'` and `B'` are
the weakened copies of `A` and `B` in this larger context.

\begin{code}

A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = VAR (succ (succ (succ zero)))
B' = VAR (succ (succ zero))

\end{code}

The term `step` compares the values of `A` and `B` at the current index and
combines the result with the accumulator. By primitive recursion on `FAN · F`,
this yields a boolean expressing that `A` and `B` agree on their first
`FAN(F)` bits.

Accordingly, the notation `A＝⟦FAN•F⟧B` is meant to suggest that `A` and `B`
are equal up to the bound computed by applying `FAN` to `F`.

\begin{code}

step : Tm Γ (Ⓝ ⇨ ② ⇨ ②)
step = LAM (LAM (MIN (EQ (A' · (VAR (succ zero)))
                         (B' · (VAR (succ zero))))
                     (VAR zero)))
A＝⟦FAN•F⟧B : Tm Γ ②
A＝⟦FAN•F⟧B = REC · ⊤ · step · (FAN · F)

\end{code}

Uniform continuity principle: If A and B agree on their first FAN(F) bits,
then F takes the same value on A and B.

\begin{code}

Principle[UC] : Fml Γ
Principle[UC] = (A＝⟦FAN•F⟧B == ⊤) →→ ((F · A) == (F · B))

\end{code}
