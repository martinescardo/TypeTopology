Chuangjie Xu, November 2026

We construct a modified bar recursor for each bar-continuous outcome functional
of type (ℕ → A) → R and verify its recursion equation. We also prove that the
recursor is independent of the bar-continuity witness.

Our formulation of modified bar recursion differs from that of Berger and Oliva
in two respects.

First, we use concatenation in place of overwriting. But this formulation is
interdefinable with theirs, as explained in Remark 2.2 of their "Modified Bar
Recursion" (BRICS RS-02-14, 2002).

Second, we allow R to be any set, assuming Y is bar continuous. The control
functional in their counterexample with result type ℕ → ℕ, given in the same
remark, is not bar continuous.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan hiding (𝓤 ; 𝓥)
open import UF.FunExt using (Fun-Ext ; dfunext)
open import UF.Sets using (is-set)

module InductiveBars.ModifiedBarRecursion
 (fe : Fun-Ext)
 {𝓤 𝓥 : Universe}
 (A : 𝓤 ̇)
 (R : 𝓥 ̇)
 (R-is-set : is-set R)
 where

open import MLTT.List

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe A R R-is-set

\end{code}

We first evaluate a witness that the determining prefixes of the outcome
functional Y bar the current prefix s, by recursion on that witness.

If a₀ : A, then the base case can be simply given by Y (pad-with a₀ s).
However, we do not require A to be inhabited, so no fixed padding element
is available. Because s determines Y in the base case, the choice
of continuation does not affect the outcome. So we use H to produce a
continuation without recursive calls.

\begin{code}

private
 eval : (Y : (ℕ → A) → R)
      → (List A → (A → R) → ℕ → A)
      → (s : List A)
      → (determining-prefixes Y) bars s
      → R
 eval Y H s (hit _)  = Y (s ++∞ H s (λ a → Y (pad-with a s)))
 eval Y H s (step φ) = Y (s ++∞ H s (λ a → eval Y H (s ++ [ a ]) (φ a)))

\end{code}

Evaluation is independent of the barring witness. We will use this fact
to verify the equation of modified bar recursion.

In the step/step case, function extensionality identifies the pointwise
equal functions of child results before they are passed to H.

\begin{code}

 eval-witness-independent
  : (Y : (ℕ → A) → R)
  → (H : List A → (A → R) → ℕ → A)
  → (s : List A) (b b' : determining-prefixes Y bars s)
  → eval Y H s b ＝ eval Y H s b'
 eval-witness-independent Y H s (hit _) (hit _) = refl
 eval-witness-independent Y H s (hit det) (step φ') = goal
  where
   α β : ℕ → A
   α = H s (λ a → Y (pad-with a s))
   β = H s (λ a → eval Y H (s ++ [ a ]) (φ' a))
   goal : Y (s ++∞ α) ＝ Y (s ++∞ β)
   goal = det (s ++∞ α) (s ++∞ β) (++∞-extends s α) (++∞-extends s β)
 eval-witness-independent Y H s (step φ) (hit det') = goal
  where
   α β : ℕ → A
   α = H s (λ a → eval Y H (s ++ [ a ]) (φ a))
   β = H s (λ a → Y (pad-with a s))
   goal : Y (s ++∞ α) ＝ Y (s ++∞ β)
   goal = det' (s ++∞ α) (s ++∞ β) (++∞-extends s α) (++∞-extends s β)
 eval-witness-independent Y H s (step φ) (step φ') = goal
  where
   ih : (a : A)
      → eval Y H (s ++ a ∷ []) (φ a) ＝ eval Y H (s ++ a ∷ []) (φ' a)
   ih a = eval-witness-independent Y H (s ++ [ a ]) (φ a) (φ' a)
   e : (λ a → eval Y H (s ++ a ∷ []) (φ a)) ＝
       (λ a → eval Y H (s ++ a ∷ []) (φ' a))
   e = dfunext fe ih
   goal : Y (s ++∞ H s (λ a → eval Y H (s ++ a ∷ []) (φ a))) ＝
          Y (s ++∞ H s (λ a → eval Y H (s ++ a ∷ []) (φ' a)))
   goal = ap (λ x → Y (s ++∞ H s x)) e

 eval-spec : (Y : (ℕ → A) → R)
           → (H : List A → (A → R) → ℕ → A)
           → (s : List A)
           → (b : determining-prefixes Y bars s)
           → (φ : (a : A) → (determining-prefixes Y) bars (s ++ [ a ]))
           → eval Y H s b ＝ Y (s ++∞ H s (λ a → eval Y H (s ++ [ a ]) (φ a)))
 eval-spec Y H s b φ = eval-witness-independent Y H s b (step φ)

\end{code}

Bar continuity supplies a barring witness at every prefix. Evaluating
these witnesses defines the modified bar recursor. Its witness independence
and recursion equation follow from the corresponding properties of the
evaluation function.

\begin{code}

mbr : (Y : (ℕ → A) → R)
    → is-bar-continuous″ Y
    → (List A → (A → R) → ℕ → A)
    → List A → R
mbr Y bc H s = eval Y H s (bc s)

mbr-witness-independent
 : (Y : (ℕ → A) → R)
 → (bc bc' : is-bar-continuous″ Y)
 → (H : List A → (A → R) → ℕ → A)
 → (s : List A)
 → mbr Y bc H s ＝ mbr Y bc' H s
mbr-witness-independent Y bc bc' H s
 = eval-witness-independent Y H s (bc s) (bc' s)

modified-bar-recursion-spec
 : (Y : (ℕ → A) → R)
 → (bc : is-bar-continuous″ Y)
 → (H : List A → (A → R) → ℕ → A)
 → (s : List A)
 → mbr Y bc H s ＝ Y (s ++∞ H s (λ a → mbr Y bc H (s ++ [ a ])))
modified-bar-recursion-spec Y bc H s
 = eval-spec Y H s (bc s) (λ a → bc (s ++ [ a ]))

\end{code}
