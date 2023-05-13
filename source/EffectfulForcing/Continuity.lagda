Martin Escardo 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Continuity where

open import MLTT.Spartan
open import MLTT.Athenian

Baire : 𝓤₀ ̇
Baire = ℕ → ℕ

data _＝⟪_⟫_ {X : 𝓤₀ ̇ } : (ℕ → X) → List ℕ → (ℕ → X) → 𝓤₀ ̇  where
  []  : {α α' : ℕ → X} → α ＝⟪ [] ⟫ α'
  _∷_ : {α α' : ℕ → X} {i : ℕ} {s : List ℕ} → α i ＝ α' i → α ＝⟪ s ⟫ α' → α ＝⟪ i ∷ s ⟫ α'

infix 0 _＝⟪_⟫_
infixr 3 _∷_

is-continuous : (Baire → ℕ) → 𝓤₀ ̇
is-continuous f = (α : Baire) → Σ s ꞉ List ℕ , ((α' : Baire) → α ＝⟪ s ⟫ α' → f α ＝ f α')

continuity-extensional : (f g : Baire → ℕ)
                       → (f ∼ g)
                       → is-continuous f
                       → is-continuous g
continuity-extensional f g t c α = (pr₁ (c α) ,
                                    (λ α' r → g α  ＝⟨ (t α)⁻¹ ⟩
                                              f α  ＝⟨ pr₂(c α) α' r ⟩
                                              f α' ＝⟨ t α' ⟩
                                              g α' ∎))

Cantor : 𝓤₀ ̇
Cantor = ℕ → 𝟚

data BT (X : 𝓤₀ ̇ ) : 𝓤₀ ̇  where
  []   : BT X
  _∷_ : X → (𝟚 → BT X) → BT X

data _＝⟦_⟧_ {X : 𝓤₀ ̇ } : (ℕ → X) → BT ℕ → (ℕ → X) → 𝓤₀ ̇  where
  []  : {α α' : ℕ → X} → α ＝⟦ [] ⟧ α'
  _∷_ : {α α' : ℕ → X}{i : ℕ}{s : 𝟚 → BT ℕ}
         → α i ＝ α' i → ((j : 𝟚) → α ＝⟦ s j ⟧ α') → α ＝⟦ i ∷ s ⟧ α'

is-uniformly-continuous : (Cantor → ℕ) → 𝓤₀ ̇
is-uniformly-continuous f = Σ s ꞉ BT ℕ , ((α α' : Cantor) → α ＝⟦ s ⟧ α' → f α ＝ f α')

UC-extensional : (f g : Cantor → ℕ)
               → (f ∼ g)
               → is-uniformly-continuous f
               → is-uniformly-continuous g
UC-extensional f g t (u , c) = (u ,
                                (λ α α' r → g α  ＝⟨ (t α)⁻¹ ⟩
                                            f α  ＝⟨ c α α' r ⟩
                                            f α' ＝⟨ t α' ⟩
                                            g α' ∎))

embedding-𝟚-ℕ : 𝟚 → ℕ
embedding-𝟚-ℕ ₀ = zero
embedding-𝟚-ℕ ₁ = succ zero

embedding-C-B : Cantor → Baire
embedding-C-B = embedding-𝟚-ℕ ∘_

C-restriction : (Baire → ℕ) → (Cantor → ℕ)
C-restriction = _∘ embedding-C-B

\end{code}
