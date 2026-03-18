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

As in the System-T-with-Fan file, `EQ` compares two booleans and `MIN`
propagates failure while scanning initial segments of binary sequences.

\begin{code}

EQ : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
EQ B₀ B₁ = IF · B₀ · (IF · B₁ · ⊤ · ⊥) · B₁

MIN : {Γ : Cxt} → Tm Γ ② → Tm Γ ② → Tm Γ ②
MIN B₀ B₁ = IF · B₀ · ⊥ · B₁

-- The context consists of:
--   F : (Ⓝ ⇨ ②) ⇨ Ⓝ   a function on binary sequences,
--   M : Ⓝ             a candidate modulus,
--   A , B : Ⓝ ⇨ ②     two binary sequences.
Γ : Cxt
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ Ⓝ ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = VAR (succ (succ (succ zero)))

M : Tm Γ Ⓝ
M = VAR (succ (succ zero))

A B : Tm Γ (Ⓝ ⇨ ②)
A = VAR (succ zero)
B = VAR zero

-- In the recursive step we work in the extended context
--   Γ , n : Ⓝ , b : ②
-- and recover the original sequences A and B by de Bruijn indexing.
A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = VAR (succ (succ (succ zero)))
B' = VAR (succ (succ zero))

-- The step checks equality at the current index and combines it with the
-- previously accumulated truth value.
step : Tm Γ (Ⓝ ⇨ ② ⇨ ②)
step = LAM (LAM (MIN (EQ (A' · (VAR (succ zero)))
                         (B' · (VAR (succ zero))))
                     (VAR zero)))

-- Boolean predicate expressing that A and B agree on their first M bits.
A＝⟦M⟧B : Tm Γ ②
A＝⟦M⟧B = REC · ⊤ · step · M

-- The HAω formulation of uniform continuity:
-- every F : (Ⓝ ⇨ ②) ⇨ Ⓝ has some modulus M such that agreement of A and B on
-- the first M bits implies F A ＝ F B.
Principle[UC] : HAω ε
Principle[UC] =
   Ā (Ⓝ ⇨ ②) ⇨ Ⓝ     · Ē Ⓝ     · Ā Ⓝ ⇨ ②     · Ā Ⓝ ⇨ ②     ·  A＝⟦M⟧B == ⊤  →→  F · A == F · B
-- ∀ f : (Ⓝ ⇨ ②) ⇨ Ⓝ . ∃ m : Ⓝ . ∀ α : Ⓝ ⇨ ② . ∀ β : Ⓝ ⇨ ② .   α ＝⟦m⟧ β     →     f α ＝ f β

\end{code}
