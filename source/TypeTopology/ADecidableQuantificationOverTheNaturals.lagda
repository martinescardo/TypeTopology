Chuangjie Xu, 2012.

This is an Agda formalization of Theorem 8.2 of the extended version
of Escardo's paper "Infinite sets that satisfy the principle of
omniscience in all varieties of constructive mathematics", Journal of
Symbolic Logic, volume 78, number 3, September 2013, pages 764-784.

The theorem says that, for any p : ℕ∞ → 𝟚, the proposition
(n : ℕ) → p (ι n) ＝ ₁ is decidable where ι : ℕ → ∞ is the inclusion.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.ADecidableQuantificationOverTheNaturals (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe
open import UF.DiscreteAndSeparated
open import UF.PropTrunc

Lemma-8·1 : (p : ℕ∞ → 𝟚) → (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀))
                         + ((n : ℕ) → p (ι n) ＝ ₁)
Lemma-8·1 p = cases claim₀ claim₁ claim₂
 where
  claim₀ : (Σ y ꞉ ℕ∞ , p y ≠ p (Succ y))
         → (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)) + ((n : ℕ) → p (ι n) ＝ ₁)
  claim₀ e = inl (𝟚-equality-cases case₀ case₁)
   where
    x : ℕ∞
    x = pr₁ e

    ne : p x ≠ p (Succ x)
    ne = pr₂ e

    case₀ : p x ＝ ₀ → Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)
    case₀ r = x , (s , r)
     where
      s : x ≠ ∞
      s t = ne (ap p (t ∙ (Succ-∞-is-∞ fe)⁻¹ ∙ (ap Succ t)⁻¹))

    case₁ : p x ＝ ₁ → Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)
    case₁ r = (Succ x) , (s , s')
     where
      s : Succ x ≠ ∞
      s t = ne (ap p (Succ-lc (t ∙ (Succ-∞-is-∞ fe)⁻¹) ∙ t ⁻¹))

      s' : p (Succ x) ＝ ₀
      s' = different-from-₁-equal-₀ (λ t → ne (r ∙ t ⁻¹))

  claim₁ : ((y : ℕ∞) → p y ＝ p (Succ y)) →
            (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)) + ((n : ℕ) → p (ι n) ＝ ₁)
  claim₁ f = 𝟚-equality-cases case₀ case₁
   where
    case₀ : p Zero ＝ ₀ →
            (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)) + ((n : ℕ) → p (ι n) ＝ ₁)
    case₀ r = inl (Zero , (s , r))
     where
      s : Zero ≠ ∞
      s t = ∞-is-not-finite 0 (t ⁻¹)

    case₁ : p Zero ＝ ₁ →
            (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀)) + ((n : ℕ) → p (ι n) ＝ ₁)
    case₁ r = inr by-induction
     where
      by-induction : (n : ℕ) → p (ι n) ＝ ₁
      by-induction 0 = r
      by-induction (succ n) = (f (ι n))⁻¹ ∙ by-induction n

  claim₂ : (Σ y ꞉ ℕ∞ , p y ≠ p (Succ y)) + ((y : ℕ∞) → p y ＝ p (Succ y))
  claim₂ = g (ℕ∞-compact q)
   where
    fact : (y : ℕ∞) → (p y ≠ p (Succ y)) + ¬ (p y ≠ p (Succ y))
    fact y = ¬-preserves-decidability (𝟚-is-discrete (p y) (p (Succ y)))

    f : Σ q ꞉ (ℕ∞ → 𝟚), ((y : ℕ∞) → (q y ＝ ₀ → p y ≠ p (Succ y))
                                  × (q y ＝ ₁ → ¬ (p y ≠ p (Succ y))))
    f = characteristic-function fact

    q : ℕ∞ → 𝟚
    q = pr₁ f

    g : (Σ y ꞉ ℕ∞ , q y ＝ ₀) + ((y : ℕ∞) → q y ＝ ₁)
     → (Σ y ꞉ ℕ∞ , p y ≠ p (Succ y)) + ((y : ℕ∞) → p y ＝ p (Succ y))
    g (inl (y , r)) = inl (y , (pr₁ (pr₂ f y) r))
    g (inr h ) = inr (λ y → discrete-is-¬¬-separated
                             𝟚-is-discrete
                             (p y) (p (Succ y))
                             (pr₂ (pr₂ f y) (h y)))

abstract
 Theorem-8·2 : (p : ℕ∞ → 𝟚) → is-decidable ((n : ℕ) → p (ι n) ＝ ₁)
 Theorem-8·2 p = cases claim₀ claim₁ (Lemma-8·1 p)
  where
   claim₀ : (Σ x ꞉ ℕ∞ , (x ≠ ∞) × (p x ＝ ₀))
          → is-decidable ((n : ℕ) → p (ι n) ＝ ₁)
   claim₀ e = inr c₁
    where
     x : ℕ∞
     x = pr₁ e

     c₀ : ¬ ((n : ℕ) → x ≠ ι n)
     c₀ = λ g → pr₁ (pr₂ e) (not-finite-is-∞ fe g)

     c₁ : ¬ ((n : ℕ) → p (ι n) ＝ ₁)
     c₁ g = c₀ d
      where
       d : (n : ℕ) → x ≠ ι n
       d n r = equal-₀-different-from-₁ (pr₂ (pr₂ e)) (ap p r ∙ g n)

   claim₁ : ((n : ℕ) → p (ι n) ＝ ₁) → is-decidable ((n : ℕ) → p (ι n) ＝ ₁)
   claim₁ f = inl f

\end{code}

Some examples:

\begin{code}

module examples where

    to-ℕ : {A : 𝓤 ̇ } → is-decidable A → ℕ
    to-ℕ (inl _) = 0
    to-ℕ (inr _) = 1

\end{code}

    0 means that (n : ℕ) → p (ι n) ＝ ₁
    1 means that ¬ ((n : ℕ) → p (ι n) ＝ ₁)

\begin{code}

    eval : (ℕ∞ → 𝟚) → ℕ
    eval p = to-ℕ (Theorem-8·2 p)

    p₀ : ℕ∞ → 𝟚
    p₀ _ = ₀

    p₁ : ℕ∞ → 𝟚
    p₁ _ = ₁

\end{code}

    If the first boolean is less than or equal to the second
    then it has value ₁; otherwise, it has value ₀.

\begin{code}

    _<=_ : 𝟚 → 𝟚 → 𝟚
    ₀ <= y = ₁
    ₁ <= ₀ = ₀
    ₁ <= ₁ = ₁

\end{code}

    If the two booleans are equal then it has value ₁;
    otherwise, it has value ₀.

\begin{code}

    _==_ : 𝟚 → 𝟚 → 𝟚
    ₀ == ₀ = ₁
    ₀ == ₁ = ₀
    ₁ == ₀ = ₀
    ₁ == ₁ = ₁

    p₂ : ℕ∞ → 𝟚
    p₂ (α , _) = α 10 <= α 1

    p₃ : ℕ∞ → 𝟚
    p₃ (α , _) = α 0 <= α 1

    p₄ : ℕ∞ → 𝟚
    p₄ (α , _) = α 5 == α 100

    to-something : (p : ℕ∞ → 𝟚) → is-decidable ((n : ℕ) → p (ι n) ＝ ₁) → (p (ι 17) ＝ ₁) + ℕ
    to-something p (inl f) = inl (f 17)
    to-something p (inr _) = inr 1070

    eval1 : (p : ℕ∞ → 𝟚) → (p (ι 17) ＝ ₁) + ℕ
    eval1 p = to-something p (Theorem-8·2 p)

\end{code}

    Despite the fact that we use function extensionality, eval pi
    evaluates to a numeral for i=0,...,4.
