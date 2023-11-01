Martin Escardo 2012

Combinatory version of Gödel's System T and its standard set-theoretic
semantics.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.CombinatoryT where

open import MLTT.Spartan
open import MLTT.Athenian
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Combinators
open import UF.Base

data type : 𝓤₀  ̇  where
 ι   : type
 _⇒_ : type → type → type

data T : (σ : type) → 𝓤₀  ̇  where
 Zero  : T ι
 Succ  : T (ι ⇒ ι)
 Iter  : {σ : type}     → T ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 K     : {σ τ : type}   → T (σ ⇒ τ ⇒ σ)
 S     : {ρ σ τ : type} → T ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
 _·_   : {σ τ : type}   → T (σ ⇒ τ) → T σ → T τ

infixr 1 _⇒_
infixl 1 _·_

Set⟦_⟧ : type → 𝓤₀  ̇
Set⟦ ι ⟧     = ℕ
Set⟦ σ ⇒ τ ⟧ = Set⟦ σ ⟧ → Set⟦ τ ⟧

⟦_⟧ : {σ : type} → T σ → Set⟦ σ ⟧
⟦ Zero  ⟧ = zero
⟦ Succ  ⟧ = succ
⟦ Iter  ⟧ = iter
⟦ K     ⟧ = Ķ
⟦ S     ⟧ = Ş
⟦ t · u ⟧ = ⟦ t ⟧ ⟦ u ⟧

is-T-definable : {σ : type} → Set⟦ σ ⟧ → 𝓤₀ ̇
is-T-definable {σ} x = Σ t ꞉ T σ , ⟦ t ⟧ ＝ x

\end{code}

System T extended with oracles.

\begin{code}

data TΩ : (σ : type) → 𝓤₀ ̇  where
 Ω     : TΩ (ι ⇒ ι)
 Zero  : TΩ ι
 Succ  : TΩ (ι ⇒ ι)
 Iter  : {σ : type}     → TΩ ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 K     : {σ τ : type}   → TΩ (σ ⇒ τ ⇒ σ)
 S     : {ρ σ τ : type} → TΩ ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
 _·_   : {σ τ : type}   → TΩ (σ ⇒ τ) → TΩ σ → TΩ τ

⟦_⟧' : {σ : type} → TΩ σ → Baire → Set⟦ σ ⟧
⟦ Ω     ⟧' α = α
⟦ Zero  ⟧' α = zero
⟦ Succ  ⟧' α = succ
⟦ Iter  ⟧' α = iter
⟦ K     ⟧' α = Ķ
⟦ S     ⟧' α = Ş
⟦ t · u ⟧' α = ⟦ t ⟧' α (⟦ u ⟧' α)

embedding : {σ : type} → T σ → TΩ σ
embedding Zero    = Zero
embedding Succ    = Succ
embedding Iter    = Iter
embedding K       = K
embedding S       = S
embedding (t · u) = embedding t · embedding u

preservation : {σ : type} → (t : T σ) → (α : Baire) → ⟦ t ⟧ ＝ ⟦ embedding t ⟧' α
preservation Zero    α = refl
preservation Succ    α = refl
preservation Iter    α = refl
preservation K       α = refl
preservation S       α = refl
preservation (t · u) α = ap₂ id (preservation t α) (preservation u α)

\end{code}
