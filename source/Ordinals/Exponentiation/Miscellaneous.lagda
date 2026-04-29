Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
16 October 2025.

A collection of properties of exponentiation that did not nicely fit
the other files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Miscellaneous
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Fin.Type
open import MLTT.Spartan hiding (_^_)
open import Naturals.Exponentiation
open import Naturals.Order
open import Notation.Order

open import Ordinals.Arithmetic fe
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Fin
open import Ordinals.Omega ua pt sr
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

Fin-ordinal-_^ₒω-is-ω_ : (k : ℕ) → 1 < k → Fin-ordinal k ^ₒ ω ＝ ω
Fin-ordinal- k@(succ (succ k')) ^ₒω-is-ω p =
  𝕜 ^ₒ ω                           ＝⟨ ap (𝕜 ^ₒ_) ω-is-sup-of-Fin ⟩
  𝕜 ^ₒ (sup (λ n → Fin-ordinal n)) ＝⟨ I ⟩
  sup (λ n → 𝕜 ^ₒ Fin-ordinal n)   ＝⟨ II ⟩
  sup (λ n → Fin-ordinal (k ^ n))  ＝⟨ ⊴-antisym _ _ III IV ⟩
  sup (λ n → Fin-ordinal n)        ＝⟨ ω-is-sup-of-Fin ⁻¹ ⟩
  ω                                ∎
   where
    𝕜 = Fin-ordinal k

    I = ^ₒ-satisfies-sup-specification 𝕜 𝕜-non-zero ∣ 0 ∣ Fin-ordinal
     where
      𝕜-non-zero : 𝕜 ≠ 𝟘ₒ
      𝕜-non-zero eq = transport ⟨_⟩ eq fzero

    II = ap sup (dfunext fe' λ n → Fin-ordinal-^ₒ ua pt sr (succ k') n ⁻¹)

    III : sup (λ n → Fin-ordinal (k ^ n)) ⊴ sup (λ n → Fin-ordinal n)
    III = sup-composition-⊴ (k ^_) Fin-ordinal

    IV : sup (λ n → Fin-ordinal n) ⊴ sup (λ n → Fin-ordinal (k ^ n))
    IV = sup-monotone Fin-ordinal (Fin-ordinal ∘ (k ^_)) IV₀
     where
      IV₀ : (n : ℕ) → Fin-ordinal n ⊴ Fin-ordinal (k ^ n)
      IV₀ n = Fin-ordinal-preserves-≤ ua
               (exponent-smaller-than-exponential-for-base-at-least-two n k ⋆)

\end{code}
