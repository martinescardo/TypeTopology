Chuangjie Xu, 2012. 

This is an Agda formalization of Theorem 8.2 of the extended version
of Escardo's paper "Infinite sets that satisfy the principle of
omniscience in all varieties of constructive mathematics", Journal of
Symbolic Logic, volume 78, number 3, September 2013, pages 764-784.

The theorem says that, for any p : ℕ∞ → ₂, the proposition
(n : ℕ) → p(under n) ≡ ₁ is decidable. 

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF

module ADecidableQuantificationOverTheNaturals (fe : FunExt U₀ U₀) where

open import Naturals
open import Two 
open import GenericConvergentSequence
open import ConvergentSequenceSearchable (fe)
open import DecidableAndDetachable
open import DiscreteAndSeparated

Lemma-8·1 : (p : ℕ∞ → 𝟚) → 

   (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) + ((n : ℕ) → p(under n) ≡ ₁)

Lemma-8·1 p = cases claim₀ claim₁ claim₂
 where
  claim₀ : (Σ \(y : ℕ∞) → p y ≢ p(Succ y))
          → (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) + ((n : ℕ) → p(under n) ≡ ₁)
  claim₀ e = inl (two-equality-cases case₀ case₁)
   where
    x : ℕ∞
    x = pr₁ e
    ne : p x ≢ p(Succ x)
    ne = pr₂ e
    case₀ : p x ≡ ₀ → Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)
    case₀ r = x , (s , r)
     where 
      s : x ≢ ∞
      s t = ne(ap p (t ∙ (Succ-∞-is-∞ fe)⁻¹ ∙ (ap Succ t)⁻¹))
    case₁ : p x ≡ ₁ → Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)
    case₁ r = (Succ x) , (s , s')
     where 
      s : Succ x ≢ ∞
      s t = ne (ap p (Succ-lc (t ∙ (Succ-∞-is-∞ fe)⁻¹) ∙ t ⁻¹))
      s' : p(Succ x) ≡ ₀
      s' = Lemma[b≢₁→b≡₀] (λ t → ne (r ∙ t ⁻¹))

  claim₁ : ((y : ℕ∞) → p y ≡ p(Succ y)) →
            (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) + ((n : ℕ) → p(under n) ≡ ₁)
  claim₁ f = two-equality-cases case₀ case₁
   where
    case₀ : p Zero ≡ ₀ →
            (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) + ((n : ℕ) → p(under n) ≡ ₁)
    case₀ r = inl(Zero , (s , r))
     where
      s : Zero ≢ ∞
      s t = ∞-is-not-ℕ 0 (t ⁻¹)
    case₁ : p Zero ≡ ₁ →
            (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) + ((n : ℕ) → p(under n) ≡ ₁)
    case₁ r = inr by-induction
     where
      by-induction : (n : ℕ) → p(under n) ≡ ₁
      by-induction 0 = r
      by-induction (succ n) = (f(under n))⁻¹ ∙ by-induction n

  claim₂ : (Σ \(y : ℕ∞) → p y ≢ p(Succ y)) + ((y : ℕ∞) → p y ≡ p(Succ y))
  claim₂ = g(ℕ∞-is-omniscient q)
   where
    fact : (y : ℕ∞) → (p y ≢ p(Succ y)) + ¬(p y ≢ p(Succ y))
    fact y = negation-preserves-decidability(𝟚-discrete (p y) (p(Succ y)))

    f : Σ \(q : ℕ∞ → 𝟚) → (y : ℕ∞) → (q y ≡ ₀ → p y ≢ p(Succ y))
                                × (q y ≡ ₁ → ¬(p y ≢ p(Succ y)))
    f = characteristic-function fact
    q : ℕ∞ → 𝟚
    q = pr₁ f
    g : (Σ \(y : ℕ∞) → q y ≡ ₀) + ((y : ℕ∞) → q y ≡ ₁) 
     → (Σ \(y : ℕ∞) → p y ≢ p(Succ y)) + ((y : ℕ∞) → p y ≡ p(Succ y))
    g(inl(y , r)) = inl(y , (pr₁ (pr₂ f y) r))
    g(inr h ) = inr(λ y → discrete-is-separated 
                           𝟚-discrete 
                           (p y) (p(Succ y)) 
                           (pr₂ (pr₂ f y) (h y)))


Theorem-8·2 : (p : ℕ∞ → 𝟚) → decidable((n : ℕ) → p(under n) ≡ ₁)
Theorem-8·2 p = cases claim₀ claim₁ (Lemma-8·1 p)
 where
  claim₀ : (Σ \(x : ℕ∞) → (x ≢ ∞) × (p x ≡ ₀)) →
            decidable((n : ℕ) → p(under n) ≡ ₁)
  claim₀ e = inr c₁
   where
    x : ℕ∞
    x = pr₁ e
    c₀ : ¬((n : ℕ) → x ≢ under n)
    c₀ = λ g → pr₁(pr₂ e) (not-ℕ-is-∞ fe g)
    c₁ : ¬((n : ℕ) → p(under n) ≡ ₁)
    c₁ g = c₀ d
     where
      d : (n : ℕ) → x ≢ under n
      d n r = Lemma[b≡₀→b≢₁] (pr₂(pr₂ e)) (ap p r ∙ g n)
  claim₁ : ((n : ℕ) → p(under n) ≡ ₁) → decidable((n : ℕ) → p(under n) ≡ ₁)
  claim₁ f = inl f

\end{code}

Some examples:

\begin{code}

to-ℕ : ∀ {U} {A : U ̇} → decidable A → ℕ
to-ℕ (inl _) = 0
to-ℕ (inr _) = 1

-- 0 means that (n : ℕ) → p(under n) ≡ ₁
-- 1 means that ¬((n : ℕ) → p(under n) ≡ ₁)
eval : (ℕ∞ → 𝟚) → ℕ
eval p = to-ℕ (Theorem-8·2 p)

p₀ : ℕ∞ → 𝟚
p₀ _ = ₀

p₁ : ℕ∞ → 𝟚
p₁ _ = ₁

-- If the first boolean is less than or equal to the second#
-- then it returns ₁; otherwise, it returns ₀.
_<=_ : 𝟚 → 𝟚 → 𝟚
₀ <= y = ₁
₁ <= ₀ = ₀
₁ <= ₁ = ₁

{- -- Changed by Martin Escardo 13 September 2017 as this doesn't come from a case split:
₀ <= _ = ₁
_ <= ₁ = ₁
_ <= _ = ₀
-}

-- If the two booleans are equal then it returns ₁;
-- otherwise, it returns ₀.
_==_ : 𝟚 → 𝟚 → 𝟚
₀ == ₀ = ₁
₀ == ₁ = ₀
₁ == ₀ = ₀
₁ == ₁ = ₁

{- -- Changed by Martin Escardo 13 September 2017 as this doesn't come from a case split:
₀ == ₀ = ₁
₁ == ₁ = ₁
_ == _ = ₀
-}

p₂ : ℕ∞ → 𝟚
p₂ (α , _) = α 10 <= α 1

p₃ : ℕ∞ → 𝟚
p₃ (α , _) = α 0 <= α 1

p₄ : ℕ∞ → 𝟚
p₄ (α , _) = α 5 == α 100

to-something : (p : ℕ∞ → 𝟚) → decidable ((n : ℕ) → p(under n) ≡ ₁) → (p(under 17) ≡ ₁) + ℕ
to-something p (inl f) = inl (f 17)
to-something p (inr _) = inr 1070

eval1 : (p : ℕ∞ → 𝟚) → (p(under 17) ≡ ₁) + ℕ
eval1 p = to-something p (Theorem-8·2 p)

\end{code}

Despite the fact that we use function extensionality, eval pi
evaluates to a numeral for i=0,...,4.
