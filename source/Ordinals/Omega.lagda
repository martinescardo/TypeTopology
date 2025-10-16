Fredrik Nordvall Forsberg, 9 October 2025

We characterise the initial segments of ω as ω ↓ n = Fin n (as expected).

Hence, in particular, we see that ω = sup (λ n → Fin n), since
α = sup (λ (a : α) → α ↓ a + 1) for all ordinals α, and Fin n + 1 = Fin (n + 1).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Omega
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import Fin.Type
open import Fin.Variation
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Fin
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open PropositionalTruncation pt
open suprema pt sr

ω-↓ : (n : ℕ) → ω ↓ n ＝ Fin-ordinal n
ω-↓ n = eqtoidₒ (ua _) fe' (ω ↓ n) (Fin-ordinal n) (f , f-is-order-equiv)
 where
  f : Σ k ꞉ ℕ , k < n → Fin n
  f = Fin-unprime n

  f-order-preserving : is-order-preserving (ω ↓ n) (Fin-ordinal n) f
  f-order-preserving k k' =
   transport₂⁻¹ (λ z w → pr₁ z < pr₁ w) (ηFin n k) (ηFin n k')

  f-order-reflecting : is-order-reflecting (ω ↓ n) (Fin-ordinal n) f
  f-order-reflecting m m' =
   transport₂ (λ z w → pr₁ z < pr₁ w) (ηFin n m) (ηFin n m')

  f-is-order-equiv : is-order-equiv (ω ↓ n) (Fin-ordinal n) f
  f-is-order-equiv =
   order-preserving-reflecting-equivs-are-order-equivs
    (ω ↓ n)
    (Fin-ordinal n)
    f
    (inverses-are-equivs (Fin-prime n) (Fin-prime-is-equiv n))
    f-order-preserving
    f-order-reflecting

ω-is-sup-of-Fin : ω ＝ sup (λ (n : ℕ) → Fin-ordinal n)
ω-is-sup-of-Fin = ω                                      ＝⟨ I ⟩
                  sup (λ (n : ℕ) → (ω ↓ n) +ₒ 𝟙ₒ)        ＝⟨ II ⟩
                  sup (λ (n : ℕ) → Fin-ordinal (succ n)) ＝⟨ III ⟩
                  sup (λ (n : ℕ) → Fin-ordinal n)        ∎
 where
  I = supremum-of-successors-of-initial-segments pt sr ω
  II = ap sup (dfunext fe' (λ n → ap (_+ₒ 𝟙ₒ) (ω-↓ n) ∙ Fin-ordinal-succ' ua n ⁻¹))
  III = ⊴-antisym _ _ (sup-composition-⊴ succ Fin-ordinal)
                      (sup-monotone Fin-ordinal (Fin-ordinal ∘ succ) III')
   where
    III' : (m : ℕ) → Fin-ordinal m ⊴ Fin-ordinal (succ m)
    III' m = Fin-ordinal-preserves-≤ ua (≤-succ m)

\end{code}
