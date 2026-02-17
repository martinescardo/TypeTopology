Martin Escardo 2012.

The Weak Limited Principle of Omniscience (only somebody called Bishop
could have called it that), or WLPO for short, says that every
infinity binary sequence is either constantly 1 or it isn't.

This is equivalent to saying that every decreasing infinity binary
sequence os either constantly one or not.

The type ℕ∞ of decreasing binary sequences is defined in the module
GenericConvergentSequence. The constantly 1 sequence is called ∞.

WLPO is independent of type theory: it holds in the model of classical
sets, and it fails in recursive models, because it amounts to a
solution of the Halting Problem. But we want to keep it undecided, for
the sake of being compatible with classical mathematics, following the
wishes of Bishop, and perhaps upsetting those of Brouwer who was happy
to accept continuity principles that falsify WLPO. In the words of
Aczel, WLPO is a taboo.  More generally, anything that implies a taboo
is a taboo, and any taboo is undecided. Taboos are boundary
propositions: they are classically true, recursively false, and
constructively, well, taboos!

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Taboos.WLPO where

open import MLTT.Spartan
open import CoNaturals.Type
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import NotionsOfDecidability.Decidable

WLPO : 𝓤₀ ̇
WLPO = (u : ℕ∞) → (u ＝ ∞) + (u ≠ ∞)

\end{code}

If ℕ∞ is discrete, i.e. has decidable equality, then WLPO follows:

\begin{code}

ℕ∞-discrete-gives-WLPO : is-discrete ℕ∞ → WLPO
ℕ∞-discrete-gives-WLPO d u = d u ∞

\end{code}

Added 12 September 2018.

Conversely, assuming function extensionality, WLPO implies that ℕ∞ is
discrete. The proof uses a codistance (or closeness) function
c : ℕ∞ → ℕ∞ → ℕ∞ such that c u v ＝ ∞ ↔ u ＝ v.

\begin{code}

WLPO-gives-ℕ∞-discrete : FunExt → WLPO → is-discrete ℕ∞
WLPO-gives-ℕ∞-discrete fe wlpo u v =
 Cases (wlpo (ℕ∞-closeness u v))
  (λ (p : ℕ∞-closeness u v ＝ ∞)
        → inl (ℕ∞-infinitely-close-are-equal u v p))
  (λ (n : ℕ∞-closeness u v ≠ ∞)
        → inr (contrapositive (λ (q : u ＝ v)
                                    → ℕ∞-equal-are-infinitely-close u v q) n))
 where
  open import TWA.Closeness fe

\end{code}

More discussion about WLPO is included in the modules
TheTopologyOfTheUniverse and FailureOfTotalSeparatedness, among
others.

Notice that weak excluded middle implies WLPO.

\begin{code}

open import UF.ClassicalLogic

WEM-gives-WLPO : funext₀ → typal-WEM 𝓤₀ → WLPO
WEM-gives-WLPO fe wem u = Cases (wem (u ＝ ∞))
                           (λ (p : (u ≠ ∞))
                                 → inr p)
                           (λ (ν : ¬ (u ≠ ∞))
                                 → inl (ℕ∞-is-¬¬-separated fe u ∞ ν))
\end{code}

Added 15th November 2023.

\begin{code}

open import UF.Base

WLPO-traditional : 𝓤₀ ̇
WLPO-traditional = (α : ℕ → 𝟚) → is-decidable ((n : ℕ) → α n ＝ ₁)

open import MLTT.Two-Properties

WLPO-gives-WLPO-traditional : funext 𝓤₀ 𝓤₀ → WLPO → WLPO-traditional
WLPO-gives-WLPO-traditional fe wlpo α = IV
 where
  I : (ℕ→𝟚-to-ℕ∞ α ＝ ∞) + (ℕ→𝟚-to-ℕ∞ α ≠ ∞)
  I = wlpo (ℕ→𝟚-to-ℕ∞ α)

  II :  ℕ→𝟚-to-ℕ∞ α ＝ ∞ → (n : ℕ) → α n ＝ ₁
  II p n = II₂
   where
    II₀ : ℕ∞-to-ℕ→𝟚 (ℕ→𝟚-to-ℕ∞ α) ＝ ℕ∞-to-ℕ→𝟚 ∞
    II₀ = ap ℕ∞-to-ℕ→𝟚 p

    II₁ : force-decreasing α n ＝ ₁
    II₁ = ap (λ - → - n) II₀

    II₂ : α n ＝ ₁
    II₂ = ≤₂-criterion-converse (force-decreasing-is-smaller α n) II₁

  III : ((n : ℕ) → α n ＝ ₁) → ℕ→𝟚-to-ℕ∞ α ＝ ∞
  III ϕ = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe III₁)
   where
    III₀ : (n : ℕ) → force-decreasing α n ＝ α n
    III₀ = force-decreasing-unchanged α
            (λ i → transport₂ _≤₂_
                    ((ϕ (succ i))⁻¹)
                    ((ϕ i)⁻¹)
                    (≤₂-refl {₁}))

    III₁ : ℕ∞-to-ℕ→𝟚 (ℕ→𝟚-to-ℕ∞ α) ∼ ℕ∞-to-ℕ→𝟚 ∞
    III₁ n = ℕ∞-to-ℕ→𝟚 (ℕ→𝟚-to-ℕ∞ α) n ＝⟨refl⟩
             force-decreasing α n      ＝⟨ III₀ n ⟩
             α n                       ＝⟨ ϕ n ⟩
             ₁                         ＝⟨refl⟩
             ℕ∞-to-ℕ→𝟚 ∞ n             ∎

  IV : is-decidable ((n : ℕ) → α n ＝ ₁)
  IV = map-decidable II III I

WLPO-traditional-gives-WLPO : funext₀ → WLPO-traditional → WLPO
WLPO-traditional-gives-WLPO fe wlpot u = IV
 where
  I : is-decidable ((n : ℕ) → ℕ∞-to-ℕ→𝟚 u n ＝ ₁)
  I = wlpot (ℕ∞-to-ℕ→𝟚 u)

  II : ((n : ℕ) → ℕ∞-to-ℕ→𝟚 u n ＝ ₁) → u ＝ ∞
  II ϕ = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe ϕ)

  III :  u ＝ ∞ → (n : ℕ) → ℕ∞-to-ℕ→𝟚 u n ＝ ₁
  III e n = ap (λ - → ℕ∞-to-ℕ→𝟚 - n) e

  IV : (u ＝ ∞) + (u ≠ ∞)
  IV = map-decidable II III I

\end{code}

Added 9th September 2024. WLPO amounts to saying that the constancy of
a binary sequence is decidable.

\begin{code}

WLPO-variation₁ : 𝓤₀ ̇
WLPO-variation₁ = (α : ℕ → 𝟚) → is-decidable ((n : ℕ) → α n ＝ α 0)

WLPO-variation₁-gives-WLPO-traditional
 : WLPO-variation₁
 → WLPO-traditional
WLPO-variation₁-gives-WLPO-traditional wlpov α
 = 𝟚-equality-cases I II
 where
  I : α 0 ＝ ₀ → ((n : ℕ) → α n ＝ ₁) + ¬ ((n : ℕ) → α n ＝ ₁)
  I p = inr (λ (ϕ : (n : ℕ) → α n ＝ ₁)
               → zero-is-not-one
                  (₀   ＝⟨ p ⁻¹ ⟩
                   α 0 ＝⟨ ϕ 0 ⟩
                   ₁   ∎))

  II : α 0 ＝ ₁ → ((n : ℕ) → α n ＝ ₁) + ¬ ((n : ℕ) → α n ＝ ₁)
  II p = map-decidable
          (λ (ϕ : (n : ℕ) → α n ＝ α 0) (n : ℕ)
             → α n ＝⟨ ϕ n ⟩
               α 0 ＝⟨ p ⟩
               ₁   ∎)
          (λ (γ : (n : ℕ) → α n ＝ ₁) (n : ℕ)
             → α n ＝⟨ γ n ⟩
               ₁   ＝⟨ p ⁻¹ ⟩
               α 0 ∎)
          (wlpov α)

\end{code}

TODO. The converse.

Added 1 February 2025 by Tom de Jong.

\begin{code}

WLPO-variation₂ : 𝓤₀ ̇
WLPO-variation₂ = (α : ℕ → 𝟚) → is-decidable (¬ (Σ n ꞉ ℕ , α n ＝ ₀))

WLPO-traditional-gives-WLPO-variation₂ : WLPO-traditional → WLPO-variation₂
WLPO-traditional-gives-WLPO-variation₂ wlpo α = κ (wlpo α)
 where
  κ : is-decidable (Π n ꞉ ℕ , α n ＝ ₁) → is-decidable (¬ (Σ n ꞉ ℕ , α n ＝ ₀))
  κ (inl p) = inl (Π-not-implies-not-Σ I)
   where
    I : (n : ℕ) → α n ≠ ₀
    I n e = zero-is-not-one (e ⁻¹ ∙ p n)
  κ (inr q) = inr (¬¬-functor I (not-Π-implies-not-not-Σ II q))
   where
    I : (Σ n ꞉ ℕ , α n ≠ ₁) → (Σ n ꞉ ℕ , α n ＝ ₀)
    I (n , ν) = n , 𝟚-equality-cases id (λ (e : α n ＝ ₁) → 𝟘-elim (ν e))
    II : (n : ℕ) → ¬¬-stable (α n ＝ ₁)
    II n = 𝟚-is-¬¬-separated (α n) ₁

WLPO-variation₂-gives-traditional-WLPO : WLPO-variation₂ → WLPO-traditional
WLPO-variation₂-gives-traditional-WLPO wlpovar α = κ (wlpovar α)
 where
  κ : is-decidable (¬ (Σ n ꞉ ℕ , α n ＝ ₀)) → is-decidable (Π n ꞉ ℕ , α n ＝ ₁)
  κ (inl p) = inl (λ n → I n (II n))
   where
    I : (n : ℕ) → ¬ (α n ＝ ₀) → (α n ＝ ₁)
    I n ν = 𝟚-equality-cases (λ (e : α n ＝ ₀) → 𝟘-elim (ν e)) id
    II : (n : ℕ) → ¬ (α n ＝ ₀)
    II = not-Σ-implies-Π-not p
  κ (inr q) = inr (contrapositive I q)
   where
    I : (Π n ꞉ ℕ , α n ＝ ₁) → ¬ (Σ n ꞉ ℕ , α n ＝ ₀)
    I h (n , e) = zero-is-not-one (e ⁻¹ ∙ h n)

\end{code}
