Chuangjie Xu and Martin Escardo 2014 (updated in February 2015)
(Revised and ported to TypeTopology in 2025)

Experiment of computing moduli of uniform continuity

\begin{code}

{-# OPTIONS --without-K #-}

module C-Space.UsingNotNotFunExt.ComputationExperiments where

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

\end{code}

The development of C-spaces in this module depends on the double negation of
function extensionality. Because negated types have no computational content,
we can safely postulate the double negation of function extensionality. When
applying the Fan function to a System T-definable function ₂ℕ → ℕ, we get its
least modulus of uniform continuity, which is a closed Agda term of type ℕ that
can normalize to a numeral.

Here we present some functions ₂ℕ → ℕ, their definitions in System T (extended
with a Fan functional), and the normalization result of their uniform-coninuity
moduli computed by the Fan functional from the model of C-spaces.

\begin{code}

postulate dnfe : ¬¬ DN-funext 𝓤₀ 𝓤₀
------------------------------------

open import Naturals.Addition

open import C-Space.Preliminaries.Sequence
open import C-Space.UsingNotNotFunExt.Space
open import C-Space.UsingNotNotFunExt.CartesianClosedness dnfe
open import C-Space.UsingNotNotFunExt.DiscreteSpace dnfe
open import C-Space.UsingNotNotFunExt.YonedaLemma dnfe
open import C-Space.UsingNotNotFunExt.Fan dnfe
open import C-Space.UsingNotNotFunExt.UCinT dnfe

\end{code}

We define an abbreviation of the interpretation of closed terms with
meaning in the function space ₂ℕ → ℕ:

\begin{code}

⟦_⟧ : Tm ε ( ((Ⓝ ⇨ ②) ⇨ Ⓝ)) → ₂ℕ → ℕ
⟦ t ⟧ α = pr₁ (pr₁ ⟦ t ⟧ᵐ ⋆) (ID α)

modu : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ℕ
modu F = pr₁ fan (pr₁ ⟦ F ⟧ᵐ ⋆)

ONE TWO THREE FOUR FIVE : {n : ℕ}{Γ : Cxt n} → Tm Γ Ⓝ
ONE   = SUCC ◦ ZERO
TWO   = SUCC ◦ ONE
THREE = SUCC ◦ TWO
FOUR  = SUCC ◦ THREE
FIVE  = SUCC ◦ FOUR

PLUS : {n : ℕ} {Γ : Cxt n} → Tm Γ (Ⓝ ⇨ Ⓝ ⇨ Ⓝ)
PLUS = REC ◦ (LAM (VAR zero)) ◦ LAM (LAM (LAM (SUCC ◦ (VAR (succ zero) ◦ VAR zero))))

PLUS-interpretation : ∀ n m → pr₁ (pr₁ (pr₁ ⟦ PLUS {0} {ε} ⟧ᵐ ⋆) n) m ＝ n +ᴸ m 
PLUS-interpretation  0       m = refl
PLUS-interpretation (succ n) m = ap succ (PLUS-interpretation n m)

\end{code}

F₁ is constant.

\begin{code}

F₁ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₁ = LAM TWO

F₁-interpretation : ⟦ F₁ ⟧ ＝ λ α → 2 
F₁-interpretation = refl

modulus-of-F₁ : modu F₁ ＝ 0
modulus-of-F₁ = refl

\end{code}

F₂ is constant, though it looks at the 1st bit of input.

\begin{code}

F₂  : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₂ = LAM (IF ◦ (VAR zero ◦ ZERO) ◦ ONE ◦ ONE)

F₂-interpretation : ⟦ F₂ ⟧ ＝ λ α → if (α 0) 1 1
F₂-interpretation = refl

modulus-of-F₂ : modu F₂ ＝ 0
modulus-of-F₂ = refl

\end{code}

F₃ returns 5, if the 4th bit is ⊥.
F₃ returns 1, if the 4th bit is ⊤ and the 5th one is ⊥.
F₃ returns 2, if both the 4th and 5th bits are ⊤.

\begin{code}

F₃ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₃ = LAM (IF ◦ (VAR zero ◦ THREE)
             ◦ FIVE
             ◦ (IF ◦ (VAR zero ◦ FOUR) ◦ ONE ◦ TWO))

F₃-interpretation : ⟦ F₃ ⟧ ＝ λ α → if (α 3) 5 (if (α 4) 1 2) 
F₃-interpretation = refl

modulus-of-F₃ : modu F₃ ＝ 5
modulus-of-F₃ = refl

\end{code}

F₄ is constant. It looks at 2nd and 3rd or 4th bits and then returns 0.

\begin{code}

F₄ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₄ = LAM (IF ◦ (VAR zero ◦ ONE)
             ◦ (IF ◦ (VAR zero ◦ TWO) ◦ ZERO ◦ ZERO)
             ◦ (IF ◦ (VAR zero ◦ THREE) ◦ ZERO ◦ ZERO))

F₄-interpretation : ⟦ F₄ ⟧ ＝ λ α → if (α 1) (if (α 2) 0 0) (if (α 3) 0 0)
F₄-interpretation = refl

modulus-of-F₄ : modu F₄ ＝ 0
modulus-of-F₄ = refl

\end{code}

If the 2nd bit is ⊥, then F₅ applies SUCC to ZERO 3 times, i.e. returns 3.
If the 2nd bit is ⊤, then F₅ applies SUCC to ZERO twice, i.e. returns 2.

\begin{code}

F₅ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₅ = LAM (REC ◦ ZERO ◦ LAM SUCC ◦ (IF ◦ (VAR zero ◦ ONE) ◦ THREE ◦ TWO))

F₅-interpretation : ⟦ F₅ ⟧ ＝ λ α → ℕ-induction zero (λ _ → succ) (if (α 1) 3 2)
F₅-interpretation = refl

modulus-of-F₅ : modu F₅ ＝ 2
modulus-of-F₅ = refl

\end{code}

A more complicated example

\begin{code}

F₆ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₆ = LAM (REC ◦ (IF ◦ (VAR zero ◦ (F₅ ◦ VAR zero)) ◦ FIVE ◦ TWO)
              ◦ LAM SUCC
              ◦ (IF ◦ (VAR zero ◦ (F₄ ◦ VAR zero)) ◦ THREE ◦ TWO))

F₆-interpretation : ⟦ F₆ ⟧ ＝ λ α → ℕ-induction (if (α (⟦ F₅ ⟧ α)) 5 2)
                                                (λ _ → succ)
                                                (if (α (⟦ F₄ ⟧ α)) 3 2)
F₆-interpretation = refl

modulus-of-F₆ : modu F₆ ＝ 4
modulus-of-F₆ = refl

\end{code}

An example with the Fan functional

\begin{code}

F₇ : {n : ℕ} {Γ : Cxt n} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₇ = LAM (IF ◦ (VAR zero ◦ (FAN ◦ F₅))
             ◦ (PLUS ◦ (FAN ◦ F₆) ◦ (FAN ◦ F₃))
             ◦ (FAN ◦ F₁))

F₇-interpretation : ⟦ F₇ ⟧ ＝ λ α → if (α (modu F₅))
                                       (modu F₆ + modu F₃)
                                       (modu F₁)
F₇-interpretation = refl

modulus-of-F₇ : modu F₇ ＝ 3
modulus-of-F₇ = refl

\end{code}
