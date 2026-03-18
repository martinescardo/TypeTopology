Chuangjie Xu and Martin Escardó 2014 (updated in February 2015)
(Revised and ported to TypeTopology in 2026 by Chuangjie Xu)

Experiments in computing moduli of uniform continuity

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Spaces.UsingNotNotFunExt.ComputationExperiments (dnfe : ¬¬ DN-funext 𝓤₀ 𝓤₀) where

\end{code}

The development of C-spaces used here depends on the double negation of
function extensionality. This assumption has the form `¬¬ FunExt`, so it occurs
only under negation. Consequently it carries no computational content of its
own and does not obstruct normalization of closed Agda terms.

When we apply the Fan function to a System T-definable function `₂ℕ → ℕ`, we
obtain its least modulus of uniform continuity as a closed Agda term of type
`ℕ`, and this term can normalize to a numeral.

Here we present some functions ₂ℕ → ℕ, their definitions in System T (extended
with a Fan functional), and the normalization result of their uniform-continuity
moduli computed by the Fan functional from the model of C-spaces.

\begin{code}

open import Naturals.Addition

open import C-Spaces.Preliminaries.Booleans.Functions using (if)
open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.Syntax.SystemTWithFan
open import C-Spaces.UsingNotNotFunExt.Space
open import C-Spaces.UsingNotNotFunExt.CartesianClosedness dnfe
open import C-Spaces.UsingNotNotFunExt.DiscreteSpace dnfe
open import C-Spaces.UsingNotNotFunExt.YonedaLemma dnfe
open import C-Spaces.UsingNotNotFunExt.Fan dnfe
open import C-Spaces.UsingNotNotFunExt.UCinT dnfe

\end{code}

We write `⟦ t ⟧` for the interpretation of a closed System-T-with-Fan term
`t : ((Ⓝ ⇨ ②) ⇨ Ⓝ)` as an ordinary function `₂ℕ → ℕ`, and `modu t` for the
modulus computed for `t` by the Fan functional:

\begin{code}

⟦_⟧ : Tm ε ( ((Ⓝ ⇨ ②) ⇨ Ⓝ)) → ₂ℕ → ℕ
⟦ t ⟧ α = pr₁ (pr₁ ⟦ t ⟧ᵐ ⋆) (ID α)

modu : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ℕ
modu F = pr₁ fan (pr₁ ⟦ F ⟧ᵐ ⋆)

ONE TWO THREE FOUR FIVE : {Γ : Cxt} → Tm Γ Ⓝ
ONE   = SUCC · ZERO
TWO   = SUCC · ONE
THREE = SUCC · TWO
FOUR  = SUCC · THREE
FIVE  = SUCC · FOUR

PLUS : {Γ : Cxt} → Tm Γ (Ⓝ ⇨ Ⓝ ⇨ Ⓝ)
PLUS = REC · (LAM (VAR zero)) · LAM (LAM (LAM (SUCC · (VAR (succ zero) · VAR zero))))

PLUS-interpretation : ∀ n m → pr₁ (pr₁ (pr₁ ⟦ PLUS {ε} ⟧ᵐ ⋆) n) m ＝ n +ᴸ m 
PLUS-interpretation  0       m = refl
PLUS-interpretation (succ n) m = ap succ (PLUS-interpretation n m)

\end{code}

`F₁` is constant.

\begin{code}

F₁ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₁ = LAM TWO

F₁-interpretation : ⟦ F₁ ⟧ ＝ λ α → 2 
F₁-interpretation = refl

modulus-of-F₁ : modu F₁ ＝ 0
modulus-of-F₁ = refl

\end{code}

`F₂` is constant, even though it inspects the first input bit.

\begin{code}

F₂  : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₂ = LAM (IF · (VAR zero · ZERO) · ONE · ONE)

F₂-interpretation : ⟦ F₂ ⟧ ＝ λ α → if (α 0) 1 1
F₂-interpretation = refl

modulus-of-F₂ : modu F₂ ＝ 0
modulus-of-F₂ = refl

\end{code}

`F₃` returns `5` if the fourth bit is `⊥`.
It returns `1` if the fourth bit is `⊤` and the fifth bit is `⊥`.
It returns `2` if both the fourth and fifth bits are `⊤`.

\begin{code}

F₃ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₃ = LAM (IF · (VAR zero · THREE)
             · FIVE
             · (IF · (VAR zero · FOUR) · ONE · TWO))

F₃-interpretation : ⟦ F₃ ⟧ ＝ λ α → if (α 3) 5 (if (α 4) 1 2) 
F₃-interpretation = refl

modulus-of-F₃ : modu F₃ ＝ 5
modulus-of-F₃ = refl

\end{code}

`F₄` is constant. It inspects the second bit and then the third or fourth bit,
but always returns `0`.

\begin{code}

F₄ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₄ = LAM (IF · (VAR zero · ONE)
             · (IF · (VAR zero · TWO) · ZERO · ZERO)
             · (IF · (VAR zero · THREE) · ZERO · ZERO))

F₄-interpretation : ⟦ F₄ ⟧ ＝ λ α → if (α 1) (if (α 2) 0 0) (if (α 3) 0 0)
F₄-interpretation = refl

modulus-of-F₄ : modu F₄ ＝ 0
modulus-of-F₄ = refl

\end{code}

If the second bit is `⊥`, then `F₅` applies `SUCC` to `ZERO` three times, so it
returns `3`. If the second bit is `⊤`, then `F₅` applies `SUCC` to `ZERO` twice,
so it returns `2`.

\begin{code}

F₅ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₅ = LAM (REC · ZERO · LAM SUCC · (IF · (VAR zero · ONE) · THREE · TWO))

F₅-interpretation : ⟦ F₅ ⟧ ＝ λ α → ℕ-induction zero (λ _ → succ) (if (α 1) 3 2)
F₅-interpretation = refl

modulus-of-F₅ : modu F₅ ＝ 2
modulus-of-F₅ = refl

\end{code}

A more complicated example

\begin{code}

F₆ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₆ = LAM (REC · (IF · (VAR zero · (F₅ · VAR zero)) · FIVE · TWO)
              · LAM SUCC
              · (IF · (VAR zero · (F₄ · VAR zero)) · THREE · TWO))

F₆-interpretation : ⟦ F₆ ⟧ ＝ λ α → ℕ-induction (if (α (⟦ F₅ ⟧ α)) 5 2)
                                                (λ _ → succ)
                                                (if (α (⟦ F₄ ⟧ α)) 3 2)
F₆-interpretation = refl

modulus-of-F₆ : modu F₆ ＝ 4
modulus-of-F₆ = refl

\end{code}

An example that explicitly uses the Fan functional

\begin{code}

F₇ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₇ = LAM (IF · (VAR zero · (FAN · F₅))
             · (PLUS · (FAN · F₆) · (FAN · F₃))
             · (FAN · F₁))

F₇-interpretation : ⟦ F₇ ⟧ ＝ λ α → if (α (modu F₅))
                                       (modu F₆ + modu F₃)
                                       (modu F₁)
F₇-interpretation = refl

modulus-of-F₇ : modu F₇ ＝ 3
modulus-of-F₇ = refl

\end{code}
