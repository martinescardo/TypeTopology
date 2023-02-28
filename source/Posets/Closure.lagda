We define closure operators on a poset as a monotone increasing function 𝑓
such that 𝑓(𝑥) ≥ 𝑥 and 𝑓(𝑓(𝑥)) = 𝑓(𝑥).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Posets.Closure
        (fe : Fun-Ext)
       where
open import Posets.Poset fe

module Closure
        {D : 𝓤 ̇ }
        (_⊑_ : D → D → 𝓣 ̇ )
        (f : D → D)
       where
  closure-η = ∀ x → x ⊑ f x
  closure-μ = ∀ x → f (f x) ⊑ f x

  open PosetAxioms _⊑_  -- TODO bundle more things

  idempotent
    : closure-η
    → closure-μ
    → is-antisymmetric
    → ∀ x → f (f x) ＝ f x
  idempotent η μ a x = a _ _ (μ _) (η _)


\end{code}

