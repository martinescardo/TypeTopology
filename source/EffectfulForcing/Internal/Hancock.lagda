--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import EffectfulForcing.Internal.PlumpishOrdinals

module EffectfulForcing.Internal.Hancock
         (PO : PlumpishOrdinals {𝓤})
       where

open import EffectfulForcing.MFPSAndVariations.CombinatoryT
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
open import EffectfulForcing.MFPSAndVariations.Combinators

open PlumpishOrdinals PO

height : {X : 𝓥 ̇ } → B X → O
height (η _)   = Zₒ
height (β ϕ _) = Sₒ (Lₒ (height ∘ ϕ))

-- TODO decide if we want to define ε₀ or postulate it as an element of O
ε₀ : O
ε₀ = {!!}

P : {σ : type} → B-Set⟦ σ ⟧ → 𝓤 ̇
P {ι}     d = height d ⊏ ε₀
P {σ ⇒ τ} f = (x : B-Set⟦ σ ⟧) → P x → P (f x)

P-kleisli-lemma-ι : (g : ℕ → B ℕ)
                    (d : B ℕ)
                  → ((m : ℕ) → height (g m) ⊏ ε₀)
                  → height d ⊏ ε₀
                  → height (kleisli-extension g d) ⊏ ε₀
P-kleisli-lemma-ι g (η n)   pg pd = pg n
P-kleisli-lemma-ι g (β ϕ i) pg pd = goal
 where
  I : Lₒ (height ∘ ϕ) ⊏ ε₀
  I = ⊏-trans _ _ _ (S-inflationary (Lₒ (height ∘ ϕ))) pd

  II : ∀ m → height (ϕ m) ⊏ ε₀
  II m = ⊑-and-⊏-implies-⊏ _ _ _ (L-upper-bound (height ∘ ϕ) m) I

  IH : ∀ m → height (kleisli-extension g (ϕ m)) ⊏ ε₀
  IH m = P-kleisli-lemma-ι g (ϕ m) pg (II m)

  goal : Sₒ (Lₒ (λ x → height (kleisli-extension g (ϕ x)))) ⊏ ε₀
  goal = {!!}

P-kleisli-lemma : (σ : type)
                  (g : ℕ → B-Set⟦ σ ⟧)
                  (d : B ℕ)
                → ((m : ℕ) → P (g m))
                → P d
                → P (Kleisli-extension g d)
P-kleisli-lemma ι       g d pg pd      = P-kleisli-lemma-ι g d pg pd
P-kleisli-lemma (σ ⇒ τ) g d pg pd f pf =
 P-kleisli-lemma τ (λ x → g x f) d (λ m → pg m f pf) pd

P-main-lemma : {σ : type} (t : TΩ σ)
             → P B⟦ t ⟧

P-main-lemma Ω = {!!}

P-main-lemma Zero = {!!}

P-main-lemma Succ = {!!}

P-main-lemma Iter s ps z pz d pd = P-kleisli-lemma _ (iter s z) d P-iter pd
 where
  P-iter : ∀ m → P (iter s z m)
  P-iter zero     = pz
  P-iter (succ m) = ps (iter s z m) (P-iter m)

P-main-lemma K x px y py = px

P-main-lemma S f pf g pg x px = pf x px (g x) (pg x px)

P-main-lemma (t · r) = P-main-lemma t B⟦ r ⟧ (P-main-lemma r)

\end{code}
