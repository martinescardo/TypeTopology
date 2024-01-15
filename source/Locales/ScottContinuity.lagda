Ayberk Tosun, 12 September 2023

Split out from the `CompactRegular` module.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Size

module Locales.ScottContinuity (pt : propositional-truncations-exist)
                               (fe : Fun-Ext)
                               (sr : Set-Replacement pt)              where

open import Locales.Frame pt fe
open import Slice.Family
open import UF.SubtypeClassifier
open import UF.Subsingletons

open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.GaloisConnection pt fe

open import Locales.InitialFrame pt fe

\end{code}

\begin{code}

∨-is-scott-continuous : (F : Frame 𝓤 𝓥 𝓦)
                      → (U : ⟨ F ⟩)
                      → is-scott-continuous F F (λ - → U ∨[ F ] -) holds
∨-is-scott-continuous F U S dir = β , γ
 where
  open PosetNotation  (poset-of F) using (_≤_)
  open PosetReasoning (poset-of F)
  open Joins _≤_

  β : ((U ∨[ F ] (⋁[ F ] S)) is-an-upper-bound-of ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
  β i = ∨[ F ]-right-monotone (⋁[ F ]-upper S i)

  γ : (Ɐ (U′ , _) ꞉ upper-bound ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ ,
        ((U ∨[ F ] (⋁[ F ] S)) ≤ U′)) holds
  γ (u′ , p) = ∨[ F ]-least γ₁ γ₂
   where
    δ₁ : index S → (U ≤ u′) holds
    δ₁ i = U                  ≤⟨ ∨[ F ]-upper₁ U (S [ i ]) ⟩
           U ∨[ F ] (S [ i ]) ≤⟨ p i                       ⟩
           u′                 ■

    γ₁ : (U ≤[ poset-of F ] u′) holds
    γ₁ = ∥∥-rec (holds-is-prop (U ≤[ poset-of F ] u′)) δ₁ (pr₁ dir)

    γ₂ : ((⋁[ F ] S) ≤[ poset-of F ] u′) holds
    γ₂ = ⋁[ F ]-least S (u′ , δ₂)
     where
      δ₂ : (u′ is-an-upper-bound-of S) holds
      δ₂ i = S [ i ]                         ≤⟨ ∨[ F ]-upper₂ U (S [ i ]) ⟩
             U ∨[ F ] (S [ i ])              ≤⟨ p i                       ⟩
             u′                              ■

\end{code}

\begin{code}

∨-is-scott-continuous-eq : (F : Frame 𝓤 𝓥 𝓦)
                         → (U : ⟨ F ⟩)
                         → (S : Fam 𝓦 ⟨ F ⟩)
                         → is-directed F S holds
                         → U ∨[ F ] (⋁[ F ] S) ＝ ⋁[ F ] ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆
∨-is-scott-continuous-eq F U S dir =
 ⋁[ F ]-unique ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ (U ∨[ F ] (⋁[ F ] S)) (γ , δ)
  where
   γ = pr₁ ((∨-is-scott-continuous F U) S dir)
   δ = pr₂ ((∨-is-scott-continuous F U) S dir)

\end{code}
