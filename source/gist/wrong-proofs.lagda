Martin Escardo 20 Deceber 2025.

This is regarding this discussion at mathstodon:
https://mathstodon.xyz/deck/@MartinEscardo/115751523590095370

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.wrong-proofs where

open import MLTT.Spartan
open import MLTT.Bool
open import Naturals.Properties
open import UF.Sets

wrong-proof₀ : (x : Bool) (p : x ＝ x) → p ＝ refl
wrong-proof₀ false refl = refl
wrong-proof₀ true refl = refl

wrong-proof₁ : is-set Bool
wrong-proof₁ {x} p refl = wrong-proof₀ x p

wrong-proof₂ : {y z : ℕ} (p : succ y ＝ succ z) → p ＝ ap succ (succ-lc p)
wrong-proof₂ refl = refl

wrong-proof₃ : (x : ℕ) (p : x ＝ x) → p ＝ refl
wrong-proof₃ zero refl = refl
wrong-proof₃ (succ x) p =
 p                   ＝⟨ wrong-proof₂ p ⟩
 ap succ (succ-lc p) ＝⟨ ap (ap succ) I ⟩
 ap succ refl        ＝⟨ refl ⟩
 refl                ∎
 where
  I : succ-lc p ＝ refl
  I = wrong-proof₃ x (succ-lc p)

wrong-proof₄ : is-set ℕ
wrong-proof₄ {x} p refl = wrong-proof₃ x p

\end{code}
