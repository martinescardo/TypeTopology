\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication
-- open import Integers.Negation renaming (-_ to ℤ-_)
-- open import Integers.Parity
open import Naturals.Exponents
open import UF.Base hiding (_≈_)
-- open import UF.Subsingletons

module Dyadics.Addition where

_+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
((x , a) , _) + ((y , b) , _) = normalise-pos (x * pos (2^ b) ℤ+ y * pos (2^ a) , a ℕ+ b)

ℤ[1/2]+-comm : (x y : ℤ[1/2]) → x + y ＝ y + x
ℤ[1/2]+-comm ((x , a) , _) ((y , b) , _) = ap normalise-pos (ap₂ _,_ I II)
 where
  I : x * pos (2^ b) ℤ+ y * pos (2^ a) ＝ y * pos (2^ a) ℤ+ x * pos (2^ b)
  I = ℤ+-comm (x * pos (2^ b)) (y * pos (2^ a))
  II : a ℕ+ b ＝ b ℕ+ a
  II = addition-commutativity a b

\end{code}
