Ayberk Tosun

Finished on 31 August 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module EffectfulForcing.Internal.Degrees (fe : Fun-Ext) where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type; ι; _⇒_;〖_〗)
open import MLTT.NaturalNumbers
open import Naturals.Order using (max)
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.InternalModCont fe

\end{code}

The degree of a type is the height of the tallest exponent tower involved in it.

\begin{code}

degree : type → ℕ
degree ι         = 0
degree (τ₁ ⇒ τ₂) = max (succ (degree τ₁)) (degree τ₂)

\end{code}

Some examples of `degree`.

\begin{code}

degree-example₁ : degree (ι ⇒ ι) ＝ 1
degree-example₁ = refl

degree-example₂ : degree (ι ⇒ (ι ⇒ ι)) ＝ 1
degree-example₂ = refl

degree-example₃ : degree ((ι ⇒ ι) ⇒ ι) ＝ 2
degree-example₃ = refl

\end{code}

\begin{code}

rank : {Γ : Cxt} {τ : type} → T Γ τ → ℕ
rank {_} {ι} Zero          = 0
rank {_} {ι} (Succ t)      = rank t
rank {_} {τ} (Rec t t₁ t₂) = max (max (degree τ) (rank t₁)) (rank t₂)
rank {_} {τ} (ν i)         = 0
rank {_} {τ} (ƛ t)         = rank t
rank {_} {_} (t₁ · t₂)     = max (rank t₁) (rank t₂)

\end{code}
