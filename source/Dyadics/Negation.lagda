Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Type
open import Integers.Type
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Parity
open import Naturals.Exponentiation
open import UF.Base hiding (_≈_)
open import UF.Subsingletons

module Dyadics.Negation where

-_ : ℤ[1/2] → ℤ[1/2]
- ((z , n) , _) = normalise-pos (ℤ- z , n)

infix 31 -_

ℤ[1/2]-minus-zero : - 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]-minus-zero = refl

minus-normalise-pos : (p : ℤ) (a : ℕ)
                    → - normalise-pos (p , a) ＝ normalise-pos (ℤ- p , a)
minus-normalise-pos p a = γ
 where
  p' = (pr₁ ∘ pr₁) (normalise-pos (p , a))
  a' = (pr₂ ∘ pr₁) (normalise-pos (p , a))
  α = pr₂ (normalise-pos (p , a))

  I : (p , a) ≈' (p' , a')
  I = ≈'-normalise-pos (p , a)

  II : (ℤ- p' , a') ≈' (ℤ- p , a)
  II = (ℤ- p') * pos (2^ a)  ＝⟨ negation-dist-over-mult' p' (pos (2^ a)) ⟩
        ℤ- p' * pos (2^ a)   ＝⟨ ap ℤ-_ (I ⁻¹) ⟩
        ℤ- p * pos (2^ a')   ＝⟨ negation-dist-over-mult' p (pos (2^ a')) ⁻¹ ⟩
        (ℤ- p) * pos (2^ a') ∎

  γ : - normalise-pos (p , a) ＝ normalise-pos (ℤ- p , a)
  γ = - normalise-pos (p , a)    ＝⟨ refl ⟩
      - ((p' , a') , α)          ＝⟨ refl ⟩
      normalise-pos (ℤ- p' , a') ＝⟨ ≈'-to-＝ (ℤ- p' , a') (ℤ- p , a) II ⟩
      normalise-pos (ℤ- p , a)   ∎

ℤ[1/2]-minus-minus : (p : ℤ[1/2]) → p ＝ - (- p)
ℤ[1/2]-minus-minus ((z , n) , α) = γ
 where
  I : (z , n) , α ≈ normalise-pos (z , n)
  I = ≈-normalise-pos ((z , n) , α)

  γ : (z , n) , α ＝ - (- ((z , n) , α))
  γ = (z , n) , α                   ＝⟨ i    ⟩
      normalise-pos (z , n)         ＝⟨ ii   ⟩
      normalise-pos (ℤ- (ℤ- z) , n) ＝⟨ iii  ⟩
      - normalise-pos (ℤ- z , n)    ＝⟨ refl ⟩
      - (- ((z , n) , α))           ∎
   where
    i   = ≈-to-＝ ((z , n) , α) (normalise-pos (z , n)) I
    ii  = ap (λ - → normalise-pos (- , n)) (minus-minus-is-plus z ⁻¹)
    iii = minus-normalise-pos (ℤ- z) n ⁻¹

\end{code}
