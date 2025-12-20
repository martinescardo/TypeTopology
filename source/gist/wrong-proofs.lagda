\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.wrong-proofs where

open import MLTT.Spartan
open import Naturals.Properties
open import UF.Sets

data Bool : 𝓤₀ ̇ where
 false true : Bool

wrong-proof₀ : (x : Bool) (p : x ＝ x) → p ＝ refl
wrong-proof₀ false refl = refl
wrong-proof₀ true refl = refl

wrong-proof₁ : is-set Bool
wrong-proof₁ {x} {y} p refl = wrong-proof₀ x p

wrong-proof₂ : (y z : ℕ) (p : succ y ＝ succ z) → p ＝ ap succ (succ-lc p)
wrong-proof₂ y z refl = refl

wrong-proof₃ : (x : ℕ) (p : x ＝ x) → p ＝ refl
wrong-proof₃ zero refl = refl
wrong-proof₃ (succ x) p =
 p                   ＝⟨ wrong-proof₂ x x p ⟩
 ap succ (succ-lc p) ＝⟨ ap (ap succ) I ⟩
 ap succ refl        ＝⟨ refl ⟩
 refl                ∎
 where
  I : succ-lc p ＝ refl
  I = wrong-proof₃ x (succ-lc p)

wrong-proof₄ : is-set ℕ
wrong-proof₄ {x} {y} p refl = wrong-proof₃ x p

\end{code}
