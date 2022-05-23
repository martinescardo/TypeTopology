
 \begin{code}

{-# OPTIONS --without-K --exact-split  --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import CanonicalMapNotation
open import IntegersB
open import IntegersAbs
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersDivision
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import NaturalsAddition
open import NaturalsDivision
open import NaturalsMultiplication
open import NaturalNumbers
open import NaturalNumbers-Properties
open import ncRationals
open import Rationals
open import UF-FunExt

module Todd.RationalsDyadic
  (fe : FunExt)
 where
 
open import Todd.TernaryBoehmRealsPrelude fe

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a *_) ^ b) 1

zero-base : (a : ℕ) → a ℕ^ 0 ≡ 1
zero-base a = refl

infixl 33 _ℕ^_ 

2^ : ℕ → ℕ
2^ = 2 ℕ^_

prod-of-powers : (n a b : ℕ) → n ℕ^ a * n ℕ^ b ≡ n ℕ^ (a + b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a * n ℕ^ succ b ≡ n ℕ^ (a + succ b)
  I = n ℕ^ a * n ℕ^ succ b  ≡⟨ refl ⟩
      n ℕ^ a * (n * n ℕ^ b) ≡⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a * n * n ℕ^ b   ≡⟨ ap (_* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n * n ℕ^ a * n ℕ^ b   ≡⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n * (n ℕ^ a * n ℕ^ b) ≡⟨ ap (n *_) (prod-of-powers n a b) ⟩
      n * n ℕ^ (a + b)      ≡⟨ refl ⟩
      n ℕ^ succ (a + b)     ≡⟨ refl ⟩
      n ℕ^ (a + succ b) ∎

raise-again : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ≡ n ℕ^ (a * b)
raise-again n a zero     = refl
raise-again n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ≡ n ℕ^ (a * b)
  IH = raise-again n a b
  
  I : n ℕ^ a ℕ^ succ b ≡ n ℕ^ (a * succ b)
  I = n ℕ^ a ℕ^ succ b       ≡⟨ refl ⟩
      n ℕ^ a * (n ℕ^ a) ℕ^ b ≡⟨ ap (n ℕ^ a *_) IH ⟩
      n ℕ^ a * n ℕ^ (a * b)  ≡⟨ prod-of-powers n a (a * b) ⟩
      n ℕ^ (a + a * b)       ≡⟨ refl ⟩
      n ℕ^ (a * succ b)      ∎

open import NaturalNumbers-Properties

ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ≡ 0) ∔ ((n ≢ 0) × odd z)

_/2' : ℤ → ℤ
pos x     /2' = pos (x /2)
negsucc x /2' = succℤ (negsucc (succ x /2))

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

-- open import Todd.TernaryBoehmDe

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

open import HCF

ℕ-even ℕ-odd : ℕ → 𝓤₀ ̇
ℕ-odd 0 = 𝟘
ℕ-odd 1 = 𝟙
ℕ-odd (succ (succ n)) = ℕ-odd n
ℕ-even n = ¬ ℕ-odd n

odd→ℕ-odd : (z : ℤ) → odd z → ℕ-odd (abs z)
odd→ℕ-odd (pos (succ 0))            o = ⋆
odd→ℕ-odd (pos (succ (succ x)))     o = odd→ℕ-odd (pos x) o
odd→ℕ-odd (negsucc 0)               o = ⋆
odd→ℕ-odd (negsucc (succ (succ x))) o = odd→ℕ-odd (negsucc x) o

odd-even-gives-hcf-1 : (a b : ℕ) → ℕ-odd a → ℕ-even b → coprime a b
odd-even-gives-hcf-1 a b even-a odd-b = {!!}

positive-powers-of-two-not-zero : (n : ℕ) → ¬ (2^ (succ n) ≡ 0)
positive-powers-of-two-not-zero (succ n) e = positive-powers-of-two-not-zero n (mult-left-cancellable (2^ (succ n)) 0 1 e)

succ-succ-even : (n : ℕ) → ℕ-even n → ℕ-even (2 + n)
succ-succ-even zero even-n ()
succ-succ-even (succ zero) even-n = λ _ → even-n ⋆
succ-succ-even (succ (succ n)) even-n = succ-succ-even n even-n

times-two-even : (n : ℕ) → ℕ-even (2 * n)
times-two-even 0 ()
times-two-even (succ n) = succ-succ-even (2 * n) (times-two-even n)

zero-denom-lt : (x : ℤ) → is-in-lowest-terms (x , 0)
zero-denom-lt x = (1-divides-all (abs x) , 1 , refl) , λ f → pr₂

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((a , 0)      , p)                = (a , 0) , zero-denom-lt a
ℤ[1/2]-to-ℚ ((a , succ n) , inr (nz , odd-a)) = (a , (pred (2^ (succ n)))) , odd-even-gives-hcf-1 (abs a) (succ (pred (2^ (succ n)))) (odd→ℕ-odd a odd-a) even-denom
 where
  even-denom : ℕ-even (succ (pred (2^ (succ n))))
  even-denom = transport (λ - → ℕ-even -) (succ-pred' (2^ (succ n)) (positive-powers-of-two-not-zero n) ⁻¹) (times-two-even (2^ n))

instance
 canonical-map-ℤ[1/2]-to-ℚ : Canonical-Map ℤ[1/2] ℚ
 ι {{canonical-map-ℤ[1/2]-to-ℚ}} = ℤ[1/2]-to-ℚ

\end{code}


