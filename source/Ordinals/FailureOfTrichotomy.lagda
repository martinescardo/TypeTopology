Martin Escardo, 14th June 2026,
with additions of 7th September and 10th November 2026.

This is a companion to Ordinals.BrouwerCodesInterpretations.

Recall that Brouwer ordinal codes are countably branching trees,
inductively defined by the constructors

  Z : B,
  S : B → B,
  L : (ℕ → B) → B.

The standard interpretation ⟦_⟧₀, given in Ordinals.BrouwerCodesInterpretations,
interprets Z as the ordinal zero, S as successor of ordinals, and L as
supremum of ordinals (least upper bound).  A question we had for some
time was whether the resulting ordinals are trichotomous. Here we
answer this in the negative. More precisely, from the assumption that
the resulting ordinals are trichotomous, we conclude that LPO holds.

To prove this, we exhibit, from any given conatural u, a Brouwer code
such that if the standard interpretation of the code is trichotomous
then the finiteness of u is decidable, which amounts to LPO.

The same codes show that if the resulting ordinals are discrete, then
WLPO holds.

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
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.BrouwerCodes
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.TrichotomousType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Taboos.LPO
open import Taboos.WLPO
open import UF.Base
open import UF.DiscreteAndSeparated

open PropositionalTruncation pt
open suprema pt sr

\end{code}

The standard interpretation of Brouwer ordinal codes is called ⟦_⟧₀.

\begin{code}

open import Ordinals.BrouwerCodesInterpretations ua pt sr using (⟦_⟧₀ ; ⟦_⟧₃)

\end{code}

From a given conatural u : ℕ∞, we construct various Brouwer codes and
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
 h (succ (succ _)) = 𝟎        --<-- It doesn't matter we we choose here.

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

 y₀-equal-to-y₁-gives-not-finite : y₀ ＝ y₁ → ¬ is-finite u
 y₀-equal-to-y₁-gives-not-finite p φ =
  ¬𝟙ₒ⊲𝟙ₒ (transport (𝟙ₒ ⊲_) (I ⁻¹) (finite-gives-𝟙ₒ⊲supα φ))
  where
   I : 𝟙ₒ ＝ sup α
   I = 𝟙ₒ         ＝⟨ lower-set-of-y₀-is-𝟙ₒ ⁻¹ ⟩
       sup β ↓ y₀ ＝⟨ ap (sup β ↓_) p ⟩
       sup β ↓ y₁ ＝⟨ lower-set-of-y₁-is-supα ⟩
       sup α      ∎

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
   I (inr (inl e)) = inr (y₀-equal-to-y₁-gives-not-finite e)
   I (inr (inr l)) = 𝟘-elim (¬supα⊲𝟙ₒ
                              (transport₂ _⊲_
                                lower-set-of-y₁-is-supα
                                lower-set-of-y₀-is-𝟙ₒ
                                (↓-preserves-order (sup β) y₁ y₀ l)))

\end{code}

Ranging over all conatural numbers, this amounts to LPO.

\begin{code}

brouwer-code : ℕ∞ → B
brouwer-code u = L (h u)

trichotomy-of-the-standard-interpretation-gives-LPO
 : ((b : B) → is-trichotomous ⟦ b ⟧₀) → LPO
trichotomy-of-the-standard-interpretation-gives-LPO τ
 = LPO'-gives-LPO (λ u → main-lemma u (τ (brouwer-code u)))

\end{code}

Added 7th September 2026.

If the comparison of the standard interpretation into the
trichotomous interpretation holds for every code, then the standard
interpretation is trichotomous, and so LPO holds.

\begin{code}

comparison₀₃-gives-LPO : ((b : B) → ⟦ b ⟧₀ ⊴ [ ⟦ b ⟧₃ ]) → LPO
comparison₀₃-gives-LPO h = II
 where
  I : (b : B) → is-trichotomous ⟦ b ⟧₀
  I b = simulation-into-trichotomous-gives-trichotomous
         α₀ α₃ f s (3is-trichotomous ⟦ b ⟧₃)
   where
    α₀ α₃ : Ordinal 𝓤₀
    α₀ = ⟦ b ⟧₀
    α₃ = [ ⟦ b ⟧₃ ]

    f : ⟨ α₀ ⟩ → ⟨ α₃ ⟩
    f = [ α₀ , α₃ ]⟨ h b ⟩

    s : is-simulation α₀ α₃ f
    s = [ α₀ , α₃ ]⟨ h b ⟩-is-simulation

  II : LPO
  II = trichotomy-of-the-standard-interpretation-gives-LPO I

\end{code}

Added by Martin Escardo, 10th November 2026.

The same codes show that the discreteness of the standard
interpretation gives WLPO. Discreteness decides whether the points y₀
and y₁ above are equal. If they are, then the point u is not finite,
by Ordinals.FailureOfTrichotomy.y₀-equal-to-y₁-gives-not-finite, and
hence u ＝ ∞. If they are different, then u ≠ ∞, because if u ＝ ∞ then
every ordinal α i is 𝟙ₒ, so that sup α is 𝟙ₒ, by
Ordinals.OrdinalOfOrdinalsSuprema.sup-of-constant-family, and then y₀
and y₁ have the same initial segment.

\begin{code}

∞-gives-sup-α-is-𝟙ₒ : (u : ℕ∞) → u ＝ ∞ → sup (α u) ＝ 𝟙ₒ
∞-gives-sup-α-is-𝟙ₒ u p =
 sup (α u)      ＝⟨ I ⟩
 sup (λ _ → 𝟙ₒ) ＝⟨ II ⟩
 𝟙ₒ             ∎
 where
  α-is-constant : (i : ℕ) → α u i ＝ 𝟙ₒ
  α-is-constant i = α-is-𝟙ₒ u i (ap (λ - → ι - i) p)

  I  = sup-pointwise-equal (α u) (λ _ → 𝟙ₒ) α-is-constant
  II = sup-of-constant-family 𝟙ₒ ∣ 0 ∣

discreteness-lemma : (u : ℕ∞)
                   → is-discrete ⟨ sup (β u) ⟩
                   → is-decidable (u ＝ ∞)
discreteness-lemma u d = I (d (y₀ u) (y₁ u))
 where
  I : is-decidable (y₀ u ＝ y₁ u) → is-decidable (u ＝ ∞)
  I (inl p)  = inl (not-finite-is-∞' fe' II)
   where
    II : ¬ is-finite u
    II = y₀-equal-to-y₁-gives-not-finite u p
  I (inr ne) = inr III
   where
    II : u ＝ ∞ → sup (β u) ↓ y₀ u ＝ sup (β u) ↓ y₁ u
    II q = sup (β u) ↓ y₀ u ＝⟨ lower-set-of-y₀-is-𝟙ₒ u ⟩
           𝟙ₒ               ＝⟨ (∞-gives-sup-α-is-𝟙ₒ u q)⁻¹ ⟩
           sup (α u)        ＝⟨ (lower-set-of-y₁-is-supα u)⁻¹ ⟩
           sup (β u) ↓ y₁ u ∎

    III : u ≠ ∞
    III q = ne (↓-lc (sup (β u)) (y₀ u) (y₁ u) (II q))

discreteness-of-the-standard-interpretation-gives-WLPO
 : ((b : B) → is-discrete ⟨ ⟦ b ⟧₀ ⟩) → WLPO
discreteness-of-the-standard-interpretation-gives-WLPO δ u
 = discreteness-lemma u (δ (brouwer-code u))

\end{code}

The argument gives WLPO, since the second case refutes u ＝ ∞ and
gives no bound for u. Whether the discreteness of the standard
interpretation gives LPO is an open question.
