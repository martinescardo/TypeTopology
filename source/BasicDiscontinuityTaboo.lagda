Martin Escardo 2012.

The following says that a particular kind of discontinuity for
functions p : ℕ∞ → ₂ is a taboo. Equivalently, it says that the
convergence of the constant sequence ₀ to the number ₁ in the type
of binary numbers is a taboo. A Brouwerian continuity axiom is
that any convergent sequence in the type ₂ of binary numbers must
be eventually constant (which we don't postulate).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

module BasicDiscontinuityTaboo (fe : FunExt) where


open import Two-Properties
open import Plus-Properties
open import GenericConvergentSequence
open import WLPO
open import CanonicalMapNotation

basic-discontinuity : (ℕ∞ → 𝟚) → 𝓤₀ ̇
basic-discontinuity p = ((n : ℕ) → p (ι n) ≡ ₀) × (p ∞ ≡ ₁)

basic-discontinuity-taboo : (p : ℕ∞ → 𝟚) → basic-discontinuity p → WLPO
basic-discontinuity-taboo p (f , r) u = 𝟚-equality-cases lemma₀ lemma₁
 where
  fact₀ : u ≡ ∞ → p u ≡ ₁
  fact₀ t = p u ≡⟨ ap p t ⟩
            p ∞ ≡⟨ r ⟩
            ₁   ∎

  fact₁ : p u ≢ ₁ → u ≢ ∞
  fact₁ = contrapositive fact₀

  fact₂ : p u ≡ ₀ → u ≢ ∞
  fact₂ = fact₁ ∘ equal-₀-different-from-₁

  lemma₀ : p u ≡ ₀ → (u ≡ ∞) + (u ≢ ∞)
  lemma₀ s = inr (fact₂ s)

  fact₃ : p u ≡ ₁ → ((n : ℕ) → u ≢ ι n)
  fact₃ t n s = zero-is-not-one (₀       ≡⟨ (f n)⁻¹ ⟩
                                 p (ι n) ≡⟨ (ap p s)⁻¹ ⟩
                                 p u     ≡⟨ t ⟩
                                 ₁       ∎)

  lemma₁ : p u ≡ ₁ → (u ≡ ∞) + (u ≢ ∞)
  lemma₁ t = inl (not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (fact₃ t))

\end{code}

The converse also holds. It shows that any proof of WLPO is a
discontinuous function, which we use to build a discontinuous function
of type ℕ∞ → 𝟚.

\begin{code}

WLPO-is-discontinuous : WLPO → Σ p ꞉ (ℕ∞ → 𝟚), basic-discontinuity p
WLPO-is-discontinuous f = p , (d , d∞)
 where
  p : ℕ∞ → 𝟚
  p u = equality-cases (f u) case₀ case₁
   where
    case₀ : (r : u ≡ ∞) → f u ≡ inl r → 𝟚
    case₀ r s = ₁

    case₁ : (r : u ≢ ∞) → f u ≡ inr r → 𝟚
    case₁ r s = ₀

  d : (n : ℕ) → p (ι n) ≡ ₀
  d n = equality-cases (f (ι n)) case₀ case₁
   where
    case₀ : (r : ι n ≡ ∞) → f (ι n) ≡ inl r → p (ι n) ≡ ₀
    case₀ r s = 𝟘-elim (∞-is-not-finite n (r ⁻¹))

    case₁ : (g : ι n ≢ ∞) → f (ι n) ≡ inr g → p (ι n) ≡ ₀
    case₁ g = ap (λ - → equality-cases - (λ r s → ₁) (λ r s → ₀))

  d∞ : p ∞ ≡ ₁
  d∞ = equality-cases (f ∞) case₀ case₁
   where
    case₀ : (r : ∞ ≡ ∞) → f ∞ ≡ inl r → p ∞ ≡ ₁
    case₀ r = ap (λ - → equality-cases - (λ r s → ₁) (λ r s → ₀))

    case₁ : (g : ∞ ≢ ∞) → f ∞ ≡ inr g → p ∞ ≡ ₁
    case₁ g = 𝟘-elim (g refl)

\end{code}

If two 𝟚-valued functions defined on ℕ∞ agree at ℕ, they have to agree
at ∞ too, unless WLPO holds:

\begin{code}

disagreement-taboo : (p q : ℕ∞ → 𝟚) → ((n : ℕ) → p (ι n) ≡ q (ι n)) → p ∞ ≢ q ∞ → WLPO
disagreement-taboo p q f g = basic-discontinuity-taboo r (r-lemma , r-lemma∞)
 where
  r : ℕ∞ → 𝟚
  r u = (p u) ⊕ (q u)

  r-lemma : (n : ℕ) → r (ι n) ≡ ₀
  r-lemma n = Lemma[b≡c→b⊕c≡₀] (f n)

  r-lemma∞ : r ∞ ≡ ₁
  r-lemma∞ = Lemma[b≢c→b⊕c≡₁] g

open import DiscreteAndSeparated

agreement-cotaboo :  ¬ WLPO → (p q : ℕ∞ → 𝟚) → ((n : ℕ) → p (ι n) ≡ q (ι n)) → p ∞ ≡ q ∞
agreement-cotaboo φ p q f = 𝟚-is-¬¬-separated (p ∞) (q ∞) (contrapositive (disagreement-taboo p q f) φ)

\end{code}
