

\begin{code}

{-# OPTIONS --without-K #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import IntegersB
open import IntegersAddition
open import IntegersOrder

module Todd.TernaryBoehmDef where

 downLeft downMid downRight upLeft upRight : ℤ → ℤ
 
 downLeft  a = a + a
 downMid   a = succℤ (downLeft a)
 downRight a = succℤ (downMid  a)

 _/2 : ℕ → ℕ
 0 /2 = 0
 1 /2 = 1
 succ (succ n) /2 = succ (n /2)

 sign : ℤ → (ℕ → ℤ)
 sign (pos     _) = pos
 sign (negsucc _) = negsucc

 num : ℤ → ℕ
 num (pos     n) = n
 num (negsucc n) = n

 upRight a = sign a (num a /2)
 upLeft  a = upRight (predℤ a)

 _below_ _above_ : ℤ → ℤ → 𝓤₀ ̇ 
 
 a below b = (downLeft b ≤ℤ a) ∔ (a ≤ℤ downRight b)
 -- a below' b = (a ≡ downLeft b) + (a ≡ downMid b) + (a ≡ downRight b)
 -- a below b ↔ a below' b

 a above b = (upLeft b ≤ℤ a) ∔ (a ≤ℤ upRight b)
 -- a above' b = (a ≡ upLeft b) + (a ≡ upRight b)
 -- a above b ↔ a above' b

 -- a below b ↔ b above a

 𝕂 : 𝓤₀ ̇
 𝕂 = Σ x ꞉ (ℤ → ℤ) , ((n : ℤ) → x (succℤ n) below x n)
 -- layer in, brick position out

\end{code}
