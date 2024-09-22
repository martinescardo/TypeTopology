Martin Escardo 11th September 2024

The type ℕ₋₂ of integers ≥ -2, used for truncation levels.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.TruncationLevels where

open import MLTT.Spartan hiding (_+_)
open import Naturals.Order
open import Notation.Order
open import Notation.Decimal

data ℕ₋₂ : 𝓤₀ ̇ where
 −2   : ℕ₋₂
 succ : ℕ₋₂ → ℕ₋₂

−1 : ℕ₋₂
−1 = succ −2

\end{code}

Input "−2" in the emacs mode as "\minus 2" (and not as "-2").  And
similarly for "−1". The two different unicode minus symbols look the
same (good), but they are not the same (also good).

The following allows us to write e.g. 3 as an element of ℕ₋₂.

\begin{code}

ℕ-to-ℕ₋₂ : (n : ℕ) {{_ : No-Constraint}} → ℕ₋₂
ℕ-to-ℕ₋₂ 0              = succ −1
ℕ-to-ℕ₋₂ (succ n) {{c}} = succ (ℕ-to-ℕ₋₂ n {{c}})

instance
 Decimal-ℕ-to-ℕ₋₂ : Decimal ℕ₋₂
 Decimal-ℕ-to-ℕ₋₂ = make-decimal-with-no-constraint ℕ-to-ℕ₋₂

\end{code}

Examples.

\begin{code}

_ : ℕ₋₂
_ = 3

_ : succ (succ −2) ＝ 0
_ = refl

_ : succ −2 ＝ −1
_ = refl

\end{code}

Addition of a natural number to an integer ≥ -2.

\begin{code}

_+_ : ℕ₋₂ → ℕ → ℕ₋₂
n + 0        = n
n + (succ m) = succ (n + m)

\end{code}

Order.

\begin{code}

_≤ℕ₋₂_ : ℕ₋₂ → ℕ₋₂ → 𝓤₀ ̇
−2     ≤ℕ₋₂ n      = 𝟙
succ m ≤ℕ₋₂ −2     = 𝟘
succ m ≤ℕ₋₂ succ n = m ≤ℕ₋₂ n

instance
 Order-ℕ₋₂-ℕ₋₂ : Order ℕ₋₂ ℕ₋₂
 _≤_ {{Order-ℕ₋₂-ℕ₋₂}} = _≤ℕ₋₂_

\end{code}

Added by Ian Ray 22nd September, 2024.

TODO: Show ℕ₋₂ ≃ ℕ.

\begin{code}

ℕ₋₂-to-ℕ : ℕ₋₂ → ℕ
ℕ₋₂-to-ℕ −2 = 0
ℕ₋₂-to-ℕ (succ x) = succ (ℕ₋₂-to-ℕ x)

ℕ₋₂-to-ℕ' : ℕ₋₂ → ℕ
ℕ₋₂-to-ℕ' −2 = 0
ℕ₋₂-to-ℕ' (succ −2) = 0
ℕ₋₂-to-ℕ' (succ (succ −2)) = 0
ℕ₋₂-to-ℕ' (succ (succ (succ x))) = succ (ℕ₋₂-to-ℕ' (succ (succ x)))

ℕ₋₂-to-ℕ'-is-identity : (m : ℕ₋₂) → 0 ≤ℕ₋₂ m → Σ n ꞉ ℕ , ℕ₋₂-to-ℕ' m ＝ n
ℕ₋₂-to-ℕ'-is-identity (succ (succ m)) o = (ℕ₋₂-to-ℕ' (succ (succ m)) , refl)

telescoping-+2 : (n : ℕ₋₂) → (−2 + ℕ₋₂-to-ℕ' (succ (succ n))) ＝ n
telescoping-+2 −2 = refl
telescoping-+2 (succ n) = ap succ (telescoping-+2 n)

assoc-ℕ₋₂-+1 : (m : ℕ₋₂) (n : ℕ) → succ m + n ＝ succ(m + n)
assoc-ℕ₋₂-+1 m zero = refl
assoc-ℕ₋₂-+1 m (succ n) = ap succ (assoc-ℕ₋₂-+1 m n)

subtraction-ℕ₋₂ : (m n : ℕ₋₂) → m ≤ℕ₋₂ n → Σ k ꞉ ℕ , m + k ＝ n
subtraction-ℕ₋₂ −2 n o = (ℕ₋₂-to-ℕ' (n + 2) , telescoping-+2 n)
subtraction-ℕ₋₂ (succ m) (succ n) o = (k , p)
 where
  IH : Σ k ꞉ ℕ , m + k ＝ n
  IH = subtraction-ℕ₋₂ m n o
  k = pr₁ IH
  q = pr₂ IH 
  p : (succ m + k) ＝ succ n
  p = succ m + k ＝⟨ assoc-ℕ₋₂-+1 m k ⟩
      succ(m + k)＝⟨ ap succ q ⟩
      succ n     ∎

\end{code}
