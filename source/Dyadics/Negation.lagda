\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Integers.Type
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Parity
open import Naturals.Exponents
open import UF.Base hiding (_≈_)
open import UF.Subsingletons

module Dyadics.Negation where

-_ : ℤ[1/2] → ℤ[1/2]
- ((z , n) , inl l)        = (ℤ- z , n) , (inl l)
- ((z , n) , inr (l , oz)) = (ℤ- z , n) , (inr (l , ℤodd-neg z oz))

infix 31 -_

ℤ[1/2]-minus-zero : - 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]-minus-zero = refl

normalise-negation : (((z , n) , e) : ℤ[1/2]) → - normalise-pos (z , n) ＝ normalise-pos (ℤ- z , n)
normalise-negation ((z , n) , e) = {!!}

ℤ[1/2]-minus-minus : (z : ℤ[1/2]) → z ＝ (- (- z))
ℤ[1/2]-minus-minus ((z , n) , inl l)        = ≈-to-＝ _ _ (ap (_* pos (2^ n)) (minus-minus-is-plus z ⁻¹))
ℤ[1/2]-minus-minus ((z , n) , inr (l , oz)) = ≈-to-＝ _ _ (ap (_* pos (2^ n)) (minus-minus-is-plus z ⁻¹))


\end{code}
