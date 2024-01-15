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
open import CoNaturals.GenericConvergentSequence
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
        → inr (contrapositive (λ (q : u ＝ v) → ℕ∞-equal-are-infinitely-close u v q) n))
 where
  open import TWA.Closeness fe

\end{code}

More discussion about WLPO is included in the modules
TheTopologyOfTheUniverse and FailureOfTotalSeparatedness, among
others.

Notice that weak excluded middle implies WLPO.

\begin{code}

open import UF.ExcludedMiddle

WEM-gives-WLPO : funext₀ → WEM 𝓤₀ → WLPO
WEM-gives-WLPO fe wem u = Cases (wem (u ＝ ∞) (ℕ∞-is-set fe))
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

WLPO-gives-WLPO-traditional : Fun-Ext → WLPO → WLPO-traditional
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
    III₁ n = ℕ∞-to-ℕ→𝟚 (ℕ→𝟚-to-ℕ∞ α) n ＝⟨ refl ⟩
             force-decreasing α n      ＝⟨ III₀ n ⟩
             α n                       ＝⟨ ϕ n ⟩
             ₁                         ＝⟨ refl ⟩
             ℕ∞-to-ℕ→𝟚 ∞ n             ∎

  IV : is-decidable ((n : ℕ) → α n ＝ ₁)
  IV = map-is-decidable II III I

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
  IV = map-is-decidable II III I

\end{code}
