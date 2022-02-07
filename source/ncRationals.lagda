Andrew Sneap - 26th November 2021

In this file I define the free rationals. They are rationals they may not be in the lowest terms, with (a , b) : ℤ × ℕ were ℤ is the numerator, and b represents a denominator of b+1, ruling out the possibility of a zero-denominator.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import DiscreteAndSeparated --TypeTopology
open import NaturalNumbers-Properties --TypeToplogy
open import UF-Base hiding (_≈_)  --TypeTopology
open import UF-FunExt --TypeTopology
open import UF-Miscelanea --TypeTopology
open import UF-Subsingletons --TypeTopology

open import IntegersAbs
open import IntegersB
open import IntegersHCF
open import IntegersMultiplication
open import IntegersOrder
open import HCF
open import NaturalsDivision
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)

module ncRationals where

ℚₙ : 𝓤₀ ̇
ℚₙ = ℤ × ℕ

is-in-lowest-terms : ℚₙ → 𝓤₀ ̇
is-in-lowest-terms (x , y) = coprime (abs x) (succ y)

is-in-lowest-terms-is-prop : Fun-Ext → (q : ℚₙ) → is-prop (is-in-lowest-terms q)
is-in-lowest-terms-is-prop fe (x , y) = coprime-is-prop fe (abs x) (succ y)

ℚₙ-is-discrete : is-discrete ℚₙ
ℚₙ-is-discrete = Σ-is-discrete ℤ-is-discrete λ _ → ℕ-is-discrete

ℚₙ-is-set : is-set ℚₙ
ℚₙ-is-set = discrete-types-are-sets ℚₙ-is-discrete

_≈_ : (p q : ℚₙ) → 𝓤₀ ̇
(x , a) ≈ (y , b) = x * pos (succ b) ≡ y * pos (succ a)

≈-refl : (q : ℚₙ) → q ≈ q
≈-refl q = refl

≈-sym : (p q : ℚₙ) → p ≈ q → q ≈ p
≈-sym p q e = e ⁻¹

≈-trans : (p q r : ℚₙ) → p ≈ q → q ≈ r → p ≈ r
≈-trans (x , a) (y , b) (z , c) e₁ e₂ = conclusion
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)
  
  I : x * b' * c' ≡ y * a' * c'
  I = ap (_* c') e₁

  II : a' * (y * c') ≡ a' * (z * b')
  II = ap (a' *_) e₂

  III : b' * (x * c') ≡ b' * (z * a')
  III = b' * (x * c') ≡⟨ ℤ*-assoc b' x c' ⁻¹ ⟩
        b' * x * c'   ≡⟨ ap (_* c') (ℤ*-comm b' x) ⟩
        x * b' * c'   ≡⟨ I ⟩
        y * a' * c'   ≡⟨ ap (_* c') (ℤ*-comm y a') ⟩
        a' * y * c'   ≡⟨ ℤ*-assoc a' y c'   ⟩
        a' * (y * c') ≡⟨ II ⟩
        a' * (z * b') ≡⟨ ℤ-mult-rearrangement' z b' a' ⟩
        b' * (z * a') ∎
        
  conclusion : (x , a) ≈ (z , c)
  conclusion = ℤ-mult-left-cancellable (x * c') (z * a') (b') (λ z → z) III

equiv-with-lowest-terms-is-equal : (a b : ℚₙ)
                                 → a ≈ b
                                 → is-in-lowest-terms a
                                 → is-in-lowest-terms b
                                 → a ≡ b
equiv-with-lowest-terms-is-equal (x , a) (y , b) e ((m₁ , m₂) , n) ((m₁' , m₂') , n') = to-×-≡ xyequal abequal
 where
  e' : (x * pos (succ b)) ≡ (y * pos (succ a))
  e' = e

  γ : abs (x * pos (succ b)) ≡ abs (y * pos (succ a))
  γ = ap abs e'

  δ : abs x ℕ* succ b ≡ abs y ℕ* succ a
  δ = abs x ℕ* abs (pos (succ b)) ≡⟨ abs-over-mult x (pos (succ b))  ⁻¹ ⟩
      abs (x * pos (succ b))     ≡⟨ γ ⟩
      abs (y * pos (succ a))     ≡⟨ abs-over-mult y (pos (succ a)) ⟩
      abs y ℕ* abs (pos (succ a)) ∎
 
  s : (succ a) ∣ ((abs x) ℕ* (succ b))
  s = (abs y) , I
   where
    I : succ a ℕ* abs y ≡ abs x ℕ* succ b
    I = succ a ℕ* abs y ≡⟨ mult-commutativity (succ a) (abs y) ⟩
        abs y ℕ* succ a ≡⟨ δ ⁻¹ ⟩
        abs x ℕ* succ b ∎

  s' : (succ b) ∣ (abs y) ℕ* (succ a)
  s' = (abs x) , I
   where
    I : succ b ℕ* abs x ≡ abs y ℕ* succ a
    I = succ b ℕ* abs x ≡⟨ mult-commutativity (succ b) (abs x) ⟩
        abs x ℕ* succ b ≡⟨ δ ⟩
        abs y ℕ* succ a ∎

  a-divides-b : (succ a) ∣ (succ b)
  a-divides-b = coprime-with-division (succ a) (abs x) (succ b) ((m₂ , m₁) , λ f' (h₁ , h₂) → n f' (h₂ , h₁)) s

  b-divides-a : (succ b) ∣ (succ a)
  b-divides-a = coprime-with-division (succ b) (abs y) (succ a) ((m₂' , m₁') , λ f (h₁ , h₂) → n' f (h₂ , h₁)) s'

  abequal : a ≡ b
  abequal = succ-lc (∣-anti (succ a) (succ b) a-divides-b b-divides-a)

  e'' : x * pos (succ a) ≡ y * pos (succ a)
  e'' = ap (x *_) (ap pos (ap succ abequal)) ∙ e

  xyequal : x ≡ y
  xyequal = ℤ-mult-right-cancellable x y (pos (succ a)) (λ z → z) e''


\end{code}
