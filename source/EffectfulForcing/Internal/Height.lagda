\begin{code}
{-# OPTIONS --without-K #-}

open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Univalence

module EffectfulForcing.Internal.Height
        (ua : Univalence)
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import Ordinals.Brouwer renaming (B to BO)
open import Ordinals.Maps
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Equivalence
open import Ordinals.Underlying
open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
open import EffectfulForcing.MFPSAndVariations.Combinators

open import EffectfulForcing.Internal.Ordinals ua pt sr

-- TODO add back --safe

height : {X : 𝓤 ̇ } → B X → BO
height (η _)   = Z
height (β ϕ _) = S (L (height ∘ ϕ))

P : {σ : type} → B-Set⟦ σ ⟧ → 𝓤₁ ̇
P {ι}     d = ⦅ height d ⦆ ⊲ ε₀
P {σ ⇒ τ} f = (x : B-Set⟦ σ ⟧) → P x → P (f x)

P-kleisli-lemma-ι : (g : ℕ → B ℕ)
                    (d : B ℕ)
                  → ((m : ℕ) → P (g m))
                  → P d
                  → ⦅ height (kleisli-extension g d) ⦆ ⊲ ε₀ -- P (kleisli-extension g d)
P-kleisli-lemma-ι g (η n)   pg pd = pg n
P-kleisli-lemma-ι g (β ϕ i) pg pd = goal
 where
  I : ⦅ L (height ∘ ϕ) ⦆ ⊲ ε₀
  I = ⊲-is-transitive _ _ _ (B-⊲-S (L (height ∘ ϕ))) pd

  II : ∀ m → ⦅ height (ϕ m) ⦆ ⊲ ε₀
  II m = {!!} -- ⊴-and-⊲-implies-⊲ _ _ _ (B-⊴-L (height ∘ ϕ) m) I

  IH : ∀ m → ⦅ height (kleisli-extension g (ϕ m)) ⦆ ⊲ ε₀
  IH m = P-kleisli-lemma-ι g (ϕ m) pg (II m)

  goal : ⦅ S (L (λ x → height (kleisli-extension g (ϕ x)))) ⦆ ⊲ ε₀
  goal = {!!}

P-kleisli-lemma : (σ : type)
                  (g : ℕ → B-Set⟦ σ ⟧)
                  (d : B ℕ)
                → ((m : ℕ) → P (g m))
                → P d
                → P (Kleisli-extension g d)
P-kleisli-lemma ι g d pg pd = P-kleisli-lemma-ι g d pg pd
P-kleisli-lemma (σ ⇒ τ) g f pg pf d pd = P-kleisli-lemma τ (λ z → g z d) f (λ m → pg m d pd) pf

P-main-lemma : {σ : type} (t : TΩ σ)
             → P B⟦ t ⟧
P-main-lemma {(ι ⇒ ι)} Ω = {!!}
P-main-lemma {ι} Zero = {!!}
P-main-lemma {(ι ⇒ ι)} Succ = {!!}
P-main-lemma {((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)} Iter s ps z pz d pd = P-kleisli-lemma σ (iter s z) d goal pd
 where
  goal : (m : ℕ) → P (iter s z m)
  goal zero     = pz
  goal (succ m) = ps (iter s z m) (goal m)
P-main-lemma {(_ ⇒ _ ⇒ _)} K = λ x z x₁ _ → z
P-main-lemma {((_ ⇒ _ ⇒ _) ⇒ (_ ⇒ _) ⇒ _ ⇒ _)} S = λ x z x₁ z₁ x₂ z₂ → z x₂ z₂ (x₁ x₂) (z₁ x₂ z₂)
P-main-lemma {σ} (t · t₁) = P-main-lemma t B⟦ t₁ ⟧ (P-main-lemma t₁)
--

\end{code}
