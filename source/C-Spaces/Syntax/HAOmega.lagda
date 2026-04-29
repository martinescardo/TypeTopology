Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

This module packages the fragment of HAω used in the C-space development.

It reuses the syntax of System T for terms and adds a small language of
formulas, together with the particular formula expressing uniform continuity.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.Syntax.HAOmega where

open import MLTT.Spartan

open import C-Spaces.Syntax.SystemT public

\end{code}

Formulas

The formulas of HAω are built from equality between System T terms,
conjunction, implication, and first-order quantification over simple types.

\begin{code}

infix  9 _==_
infixl 8 _∧∧_
infixr 7 _→→_
infixr 6 Ā_·_
infixr 6 Ē_·_

data HAω : Cxt → Set where
 _==_ : {Γ : Cxt}{σ : Ty} → Tm Γ σ   → Tm Γ σ      → HAω Γ
 _∧∧_ : {Γ : Cxt}         → HAω Γ    → HAω Γ       → HAω Γ
 _→→_ : {Γ : Cxt}         → HAω Γ    → HAω Γ       → HAω Γ
 Ā_·_ : {Γ : Cxt}         → (σ : Ty) → HAω (Γ ₊ σ) → HAω Γ 
 Ē_·_ : {Γ : Cxt}         → (σ : Ty) → HAω (Γ ₊ σ) → HAω Γ

\end{code}

Uniform-continuity principle

To formalize uniform continuity, we first define two auxiliary boolean
operations. The term `EQ` compares two booleans, and `MIN` propagates failure
while scanning initial segments of binary sequences.

\begin{code}

EQ : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
EQ B₀ B₁ = IF · B₀ · (IF · B₁ · ⊤ · ⊥) · B₁

MIN : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
MIN B₀ B₁ = IF · B₀ · ⊥ · B₁

\end{code}

The formula expressing uniform continuity is written in a context containing a
functional `F : (Ⓝ ⇨ ②) ⇨ Ⓝ`, a candidate modulus `M : Ⓝ`, and two binary
sequences `A` and `B`.

\begin{code}

Γ : Cxt
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ Ⓝ ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = VAR (succ (succ (succ zero)))

M : Tm Γ Ⓝ
M = VAR (succ (succ zero))

A B : Tm Γ (Ⓝ ⇨ ②)
A = VAR (succ zero)
B = VAR zero

\end{code}

To define the boolean term expressing that `A` and `B` agree on their first
`M` bits, we use primitive recursion on `M`. Its step term is formed in the
extended context consisting of `Γ` together with a natural number index and an
accumulator boolean. The terms `A'` and `B'` are the weakened copies of `A`
and `B` in this larger context.

\begin{code}

A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = VAR (succ (succ (succ zero)))
B' = VAR (succ (succ zero))

\end{code}

The step term compares the values of `A` and `B` at the current index and
combines that comparison with the accumulated truth value. The resulting term
`A＝⟦M⟧B` is intended to express that `A` and `B` agree up to the bound `M`.

\begin{code}

step : Tm Γ (Ⓝ ⇨ ② ⇨ ②)
step = LAM (LAM (MIN (EQ (A' · (VAR (succ zero)))
                         (B' · (VAR (succ zero))))
                     (VAR zero)))

A＝⟦M⟧B : Tm Γ ②
A＝⟦M⟧B = REC · ⊤ · step · M

\end{code}

We can now write the HAω formulation of uniform continuity: every functional
`F : (Ⓝ ⇨ ②) ⇨ Ⓝ` has some modulus `M` such that, whenever `A` and `B` agree on
their first `M` bits, the values `F · A` and `F · B` are equal.

\begin{code}

Principle[UC] : HAω ε
Principle[UC] =
   Ā (Ⓝ ⇨ ②) ⇨ Ⓝ     · Ē Ⓝ     · Ā Ⓝ ⇨ ②     · Ā Ⓝ ⇨ ②     ·  A＝⟦M⟧B == ⊤  →→  F · A == F · B
-- ∀ f : (Ⓝ ⇨ ②) ⇨ Ⓝ . ∃ m : Ⓝ . ∀ α : Ⓝ ⇨ ② . ∀ β : Ⓝ ⇨ ② .   α ＝⟦m⟧ β     →     f α ＝ f β

\end{code}
