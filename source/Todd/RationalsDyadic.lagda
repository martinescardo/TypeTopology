
 \begin{code}

{-# OPTIONS --without-K --exact-split  --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import CanonicalMapNotation
open import NaturalsMultiplication
open import NaturalNumbers
open import NaturalsAddition
open import ncRationals
open import Rationals
open import IntegersB
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import UF-FunExt

module Todd.RationalsDyadic
  (fe : FunExt)
 where

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
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , is-in-lowest-terms (z , pred (2^ n))

-- normalise (k , n)  = k/2^n
normalise : ℤ × ℤ → ℤ[1/2]

normalise-pos : ℤ → ℕ → ℤ[1/2]
normalise-pos k zero = (k , 0) , {!!} 
normalise-pos k (succ n) = {!!} -- with even-or-odd? k
-- ... | inl even = (k /2 , n) , {!!}
-- ... | inr odd  = (k , succ n) , {!!}

normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-neg k 0 = (k +ℤ k , 0) , {!!}
-- normalise k/2^-1 = 2k/2^0 = 2k
normalise-neg k (succ n) = normalise-neg (k +ℤ k) n
 
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((z , n) , lt) = (z , (pred (2^ n))) , lt

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , ((zero , refl) , 1 , refl) , λ f → pr₂

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , ((1 , refl) , 1 , refl) , λ f → pr₂

-- Following shows it is not feasible to construct arbitrary constants without some machinery to obtain the lowest terms proof easily.
{-
3/2ℤ[1/2] : ℤ[1/2]
3/2ℤ[1/2] = (pos 3 , 1) , ((3 , refl) , 2 , refl) , lt
 where
  lt : (x : ℕ) → (Σ a ꞉ ℕ , x * a ≡ 3) × (Σ b ꞉ ℕ , x * b ≡ succ (pred (2^ 1)))
               → Σ k ꞉ ℕ ,  x * k ≡ 1
  lt x ((a , e₁)  , b , e₂) = {!b - a!} , {!!}
-}
{-
instance
 canonical-map-ℤ[1/2]-to-ℚ : Canonical-Map ℤ[1/2] ℚ
 ι {{canonical-map-ℤ[1/2]-to-ℚ}} = ℤ[1/2]-to-ℚ
-}
\end{code}


