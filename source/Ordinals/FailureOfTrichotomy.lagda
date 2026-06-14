Martin Escardo, 14th June 2026.

This is a companion to Ordinals.BrouwerCodesInterpretations.

Recall that Brouwer ordinal codes are countably branching trees,
inductively defined by the constructors

  Z : B,
  S : B → B,
  L : (ℕ → B) → B.

The standard interpretation, given in Ordinals.BrouwerCodesInterpretations,
interprets Z as zero, S as successor, and L as supremum (least upper
bound). We show that the assumption that ⟦ b ⟧₀ is trichotomous for
every Brouwer code b implies the constructive taboo LPO.

We exhibit, from any given conatural u, a code such that if the
standard interpretation of the code is trichotomous then the
finiteness of u is decidable, which amounts to LPO.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.FailureOfTrichotomy
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

open import CoNaturals.Type
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Decidable
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.BrouwerCodes
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Taboos.LPO
open import UF.Base

open PropositionalTruncation pt
open suprema pt sr

\end{code}

The standard interpretation of Brouwer ordinal codes is called ⟦_⟧₀.

\begin{code}

open import Ordinals.BrouwerCodesInterpretations ua pt sr using (⟦_⟧₀)

\end{code}

From a given conatural, we construct various Brouwer codes and
associated ordinals.

\begin{code}

module _ (u : ℕ∞) where

 private
  𝟎 𝟏 𝟐 : B
  𝟎 = Z
  𝟏 = S 𝟎
  𝟐 = S 𝟏

 𝟚-to-B : 𝟚 → B
 𝟚-to-B ₀ = 𝟏
 𝟚-to-B ₁ = 𝟎

 g : ℕ → B
 g i = S (𝟚-to-B (ι u i))

 α : ℕ → Ordinal 𝓤₀
 α i = ⟦ g i ⟧₀

 h : ℕ → B
 h 0               = 𝟐
 h 1               = S (L g)
 h (succ (succ _)) = 𝟎

 β : ℕ → Ordinal 𝓤₀
 β i = ⟦ h i ⟧₀

 α-is-𝟚ₒ : (i : ℕ) → ι u i ＝ ₀ → α i ＝ 𝟚ₒ
 α-is-𝟚ₒ i e = α i              ＝⟨ ap (λ - → ⟦ 𝟚-to-B - ⟧₀ +ₒ 𝟙ₒ) e ⟩
               (𝟘ₒ +ₒ 𝟙ₒ) +ₒ 𝟙ₒ ＝⟨ ap (_+ₒ 𝟙ₒ) (𝟘ₒ-left-neutral 𝟙ₒ) ⟩
               𝟙ₒ +ₒ 𝟙ₒ         ∎

 α-is-𝟙ₒ : (i : ℕ) → ι u i ＝ ₁ → α i ＝ 𝟙ₒ
 α-is-𝟙ₒ i e = α i      ＝⟨ ap (λ - → ⟦ 𝟚-to-B - ⟧₀ +ₒ 𝟙ₒ) e ⟩
               𝟘ₒ +ₒ 𝟙ₒ ＝⟨ 𝟘ₒ-left-neutral 𝟙ₒ ⟩
               𝟙ₒ       ∎

 x₀ : ⟨ sup α ⟩
 x₀ = [ α 0 , sup α ]⟨ sup-is-upper-bound α 0 ⟩ (inr ⋆)

 β₀-is-𝟚ₒ : β 0 ＝ 𝟚ₒ
 β₀-is-𝟚ₒ = ap (_+ₒ 𝟙ₒ) (𝟘ₒ-left-neutral 𝟙ₒ)

 supα⊲β₁ : sup α ⊲ β 1
 supα⊲β₁ = (inr ⋆ , ((successor-lemma-right (sup α)) ⁻¹))

 𝟙ₒ⊲supβ : 𝟙ₒ ⊲ sup β
 𝟙ₒ⊲supβ = ⊲-⊴-gives-⊲ 𝟙ₒ (β 0) (sup β)
           (transport (𝟙ₒ ⊲_) (β₀-is-𝟚ₒ ⁻¹) 𝟙ₒ⊲𝟚ₒ)
           (sup-is-upper-bound β 0)

 supα⊲supβ : sup α ⊲ sup β
 supα⊲supβ = ⊲-⊴-gives-⊲ (sup α) (β 1) (sup β)
              supα⊲β₁
              (sup-is-upper-bound β 1)

 y₀ y₁ : ⟨ sup β ⟩
 y₀ = ⊲-witness 𝟙ₒ⊲supβ
 y₁ = ⊲-witness supα⊲supβ

 lower-set-of-y₀-is-𝟙ₒ : sup β ↓ y₀ ＝ 𝟙ₒ
 lower-set-of-y₀-is-𝟙ₒ = (⊲-witness-property 𝟙ₒ⊲supβ)⁻¹

 lower-set-of-y₁-is-supα : sup β ↓ y₁ ＝ sup α
 lower-set-of-y₁-is-supα = (⊲-witness-property supα⊲supβ)⁻¹

 ¬supα⊲𝟙ₒ : ¬ (sup α ⊲ 𝟙ₒ)
 ¬supα⊲𝟙ₒ (b , e) = 𝟘-elim (transport ⟨_⟩ I x₀)
  where
   I : sup α ＝ 𝟘ₒ
   I = sup α  ＝⟨ e ⟩
       𝟙ₒ ↓ b ＝⟨ 𝟙ₒ-↓ ⟩
       𝟘ₒ     ∎

 finite-gives-𝟙ₒ⊲supα : is-finite u → 𝟙ₒ ⊲ sup α
 finite-gives-𝟙ₒ⊲supα (n , e) =
  ⊲-⊴-gives-⊲ 𝟙ₒ (α n) (sup α)
   (transport (𝟙ₒ ⊲_) ((α-is-𝟚ₒ n I) ⁻¹) 𝟙ₒ⊲𝟚ₒ)
   (sup-is-upper-bound α n)
  where
   I : ι u n ＝ ₀
   I = ι u n     ＝⟨ ap (λ - → ι - n) (e ⁻¹) ⟩
       ι (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
       ₀         ∎

 𝟙ₒ⊲supα-gives-finite : 𝟙ₒ ⊲ sup α → is-finite u
 𝟙ₒ⊲supα-gives-finite (s , e) =
  ∥∥-rec
   (being-finite-is-prop fe' u)
   I
   (sup-is-upper-bound-jointly-surjective α s)
  where
   I : (Σ i ꞉ ℕ , Σ b ꞉ ⟨ α i ⟩ , [ α i , sup α ]⟨ sup-is-upper-bound α i ⟩ b ＝ s)
     → is-finite u
   I (i , b , q) = 𝟚-equality-cases III₀ III₁
    where
     II : 𝟙ₒ ＝ α i ↓ b
     II = 𝟙ₒ                                                  ＝⟨ e ⟩
          sup α ↓ s                                           ＝⟨ II₀ ⟩
          sup α ↓ [ α i , sup α ]⟨ sup-is-upper-bound α i ⟩ b ＝⟨ II₁ ⟩
          α i ↓ b                                             ∎
           where
            II₀ = ap (sup α ↓_) (q ⁻¹)
            II₁ = initial-segment-of-sup-at-component α i b

     III₀ : ι u i ＝ ₀ → is-finite u
     III₀ c = bounded-is-finite fe' i u c

     III₁ : ι u i ＝ ₁ → is-finite u
     III₁ c = 𝟘-elim (¬𝟙ₒ⊲𝟙ₒ (transport (𝟙ₒ ⊲_) (α-is-𝟙ₒ i c) (b , II)))

 main-lemma : is-trichotomous (sup β) → is-decidable (is-finite u)
 main-lemma τ = I (τ y₀ y₁)
  where
   I : (y₀ ≺⟨ sup β ⟩ y₁) + (y₀ ＝ y₁) + (y₁ ≺⟨ sup β ⟩ y₀)
     → is-decidable (is-finite u)
   I (inl l) = inl (𝟙ₒ⊲supα-gives-finite
                     (transport₂ _⊲_
                       lower-set-of-y₀-is-𝟙ₒ
                       lower-set-of-y₁-is-supα
                       (↓-preserves-order (sup β) y₀ y₁ l)))
   I (inr (inl e)) = inr I₁
    where
     I₀ : 𝟙ₒ ＝ sup α
     I₀ = 𝟙ₒ          ＝⟨ lower-set-of-y₀-is-𝟙ₒ ⁻¹ ⟩
          sup β ↓ y₀  ＝⟨ ap (sup β ↓_) e ⟩
          sup β ↓ y₁  ＝⟨ lower-set-of-y₁-is-supα ⟩
          sup α       ∎

     I₁ : ¬ is-finite u
     I₁ φ = ¬𝟙ₒ⊲𝟙ₒ (transport (𝟙ₒ ⊲_) (I₀ ⁻¹) (finite-gives-𝟙ₒ⊲supα φ))
   I (inr (inr l)) = 𝟘-elim (¬supα⊲𝟙ₒ
                              (transport₂ _⊲_
                                lower-set-of-y₁-is-supα
                                lower-set-of-y₀-is-𝟙ₒ
                                (↓-preserves-order (sup β) y₁ y₀ l)))

\end{code}

Ranging over all conatural numbers, this is LPO.

\begin{code}

brouwer-code : ℕ∞ → B
brouwer-code u = L (h u)

trichotomy-of-the-standard-interpretation-gives-LPO
 : ((b : B) → is-trichotomous ⟦ b ⟧₀) → LPO
trichotomy-of-the-standard-interpretation-gives-LPO τ
 = LPO'-gives-LPO (λ u → main-lemma u (τ (brouwer-code u)))

\end{code}
