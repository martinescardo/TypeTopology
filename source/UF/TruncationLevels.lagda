Martin Escardo 11th September 2024

The type ℕ₋₂ of integers ≥ -2, used for truncation levels.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.TruncationLevels where

open import MLTT.Spartan hiding (_+_)
open import Notation.Order
open import Notation.Decimal
open import UF.Equiv

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

instance
 Decimal-ℕ-to-ℕ₋₂ : Decimal ℕ₋₂
 Decimal-ℕ-to-ℕ₋₂ = make-decimal-with-no-constraint ℕ-to-ℕ₋₂
  where
   ℕ-to-ℕ₋₂ : (n : ℕ) {{_ : No-Constraint}} → ℕ₋₂
   ℕ-to-ℕ₋₂ 0              = succ −1
   ℕ-to-ℕ₋₂ (succ n) {{c}} = succ (ℕ-to-ℕ₋₂ n {{c}})

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

We show that ℕ₋₂ ≃ ℕ.

\begin{code}

ℕ₋₂-to-ℕ : ℕ₋₂ → ℕ
ℕ₋₂-to-ℕ −2 = 0
ℕ₋₂-to-ℕ (succ x) = succ (ℕ₋₂-to-ℕ x)

ℕ-to-ℕ₋₂ : ℕ → ℕ₋₂
ℕ-to-ℕ₋₂ 0 = −2
ℕ-to-ℕ₋₂ (succ x) = succ (ℕ-to-ℕ₋₂ x)

ℕ₋₂-ℕ-equivalence : ℕ₋₂ ≃ ℕ
ℕ₋₂-ℕ-equivalence =
 (ℕ₋₂-to-ℕ , qinvs-are-equivs ℕ₋₂-to-ℕ (ℕ-to-ℕ₋₂ , H , G))
 where
  H : ℕ-to-ℕ₋₂ ∘ ℕ₋₂-to-ℕ  ∼ id
  H −2 = refl
  H (succ x) = ap succ (H x)
  G : ℕ₋₂-to-ℕ ∘ ℕ-to-ℕ₋₂ ∼ id
  G 0 = refl
  G (succ x) = ap succ (G x)

\end{code}

We demonstrate an analogous notion of 'subtraction' in ℕ₋₂.

\begin{code}

ℕ₋₂-to-ℕ' : ℕ₋₂ → ℕ
ℕ₋₂-to-ℕ' −2 = 0
ℕ₋₂-to-ℕ' (succ −2) = 0
ℕ₋₂-to-ℕ' (succ (succ −2)) = 0
ℕ₋₂-to-ℕ' (succ (succ (succ x))) = succ (ℕ₋₂-to-ℕ' (succ (succ x)))

telescoping-sum-2 : (n : ℕ₋₂) → (−2 + ℕ₋₂-to-ℕ' (succ (succ n))) ＝ n
telescoping-sum-2 −2 = refl
telescoping-sum-2 (succ n) = ap succ (telescoping-sum-2 n)

succ-ℕ₋₂-assoc : (m : ℕ₋₂) (n : ℕ) → succ m + n ＝ succ (m + n)
succ-ℕ₋₂-assoc m 0 = refl
succ-ℕ₋₂-assoc m (succ n) = ap succ (succ-ℕ₋₂-assoc m n)

subtraction-ℕ₋₂ : (m n : ℕ₋₂) → m ≤ n → Σ k ꞉ ℕ , m + k ＝ n
subtraction-ℕ₋₂ −2 n o = (ℕ₋₂-to-ℕ' (n + 2) , telescoping-sum-2 n)
subtraction-ℕ₋₂ (succ m) (succ n) o = (k , p)
 where
  IH : Σ k ꞉ ℕ , m + k ＝ n
  IH = subtraction-ℕ₋₂ m n o
  k = pr₁ IH
  q = pr₂ IH
  p : (m + 1) + k ＝ n + 1
  p = (m + 1) + k ＝⟨ succ-ℕ₋₂-assoc m k ⟩
      (m + k) + 1 ＝⟨ ap succ q ⟩
      n + 1       ∎

subtraction-ℕ₋₂-term : (m n : ℕ₋₂) → m ≤ n → ℕ
subtraction-ℕ₋₂-term m n o = pr₁ (subtraction-ℕ₋₂ m n o)

subtraction-ℕ₋₂-identification : (m n : ℕ₋₂)
                               → (o : m ≤ n)
                               → m + subtraction-ℕ₋₂-term m n o ＝ n
subtraction-ℕ₋₂-identification m n o = pr₂ (subtraction-ℕ₋₂ m n o)

\end{code}

Added by Martin Escardo 17th August 2024. Declare ℕ-to-ℕ₋₂ as a
canonical map so that we can use the ι notation for it. Modules that
use this must import Notation.CanonicalMap.

\begin{code}

open import Notation.CanonicalMap

instance
 canonical-map-ℕ-to-ℕ₋₂ : Canonical-Map ℕ ℕ₋₂
 ι {{canonical-map-ℕ-to-ℕ₋₂}} = ℕ-to-ℕ₋₂

instance
 canonical-map-ℕ₋₂-to-ℕ : Canonical-Map ℕ₋₂ ℕ
 ι {{canonical-map-ℕ₋₂-to-ℕ}} = ℕ₋₂-to-ℕ'

\end{code}
