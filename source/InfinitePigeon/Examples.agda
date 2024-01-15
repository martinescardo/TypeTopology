-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.Examples where

-- To perform experiments, evaluate "example1" or "example2" to normal
-- form. It is easy to create your own examples.

-- Also, if you wish, choose another implementation of the K-shift in
-- the wrapper module K-Shift following the instructions, and which
-- proof of the infinite pigeonhole theorem is used in the module
-- FinitePigeon, by importing a different module.

open import InfinitePigeon.Cantor
open import InfinitePigeon.DataStructures
open import InfinitePigeon.Naturals
open import InfinitePigeon.PigeonProgram
open import InfinitePigeon.Two

-- Some randomly chosen examples of elements of the Cantor space to
-- play with:

a1 : ₂ℕ
a1 0 = ₁
a1(succ n) = not(a1 n)

a2 : ₂ℕ
a2 = 0 ^ 0 ^ 0 ^ 1 ^ 1 ^ 1 ^ 1 ^ 1 ^ a1

a3 : ₂ℕ
a3 i = not(a2 i)

a4 : ₂ℕ
a4 =  0 ^ 1 ^ 0 ^ 1 ^ 1 ^ 0 ^ 1 ^ 1 ^ 1 ^ a3

a5 : ₂ℕ
a5 =  0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 1 ^ a4

a6 : ₂ℕ
a6 =  0 ^ 1 ^ 1 ^ 0 ^ 0 ^ 0 ^ 1 ^ 0 ^ 1 ^ 0 ^ 0 ^ 0 ^ 0 ^ a5

a7 : ₂ℕ
a7 = 0 ^ 1 ^ 0 ^ 1 ^ 1 ^ 0 ^ 1 ^ 1 ^ 1 ^ λ i → ₀

example1 : ₂ × List ℕ
example1 = pigeon-program a6 2

example2 : ₂ × List ℕ
example2 = pigeon-program a6 3

example3 : ₂ × List ℕ
example3 = pigeon-program a5 6

example4 : ₂ × List ℕ
example4 = pigeon-program a5 7

example5 : ₂ × List ℕ
example5 = pigeon-program (λ i → not(a5 i)) 6

example6 : ₂ × List ℕ
example6 = pigeon-program (λ i → not(a6 i)) 7


-- Alternatively, calculate b and s using the Theorem:

{--
open import InfinitePigeon.FinitePigeon

b : ₂
b = ∃-witness(Theorem a m)

s : smaller(m + 1) → ℕ
s = ∃-witness(∃-elim(Theorem a m))
--}

-- Warning: depending on the example you build, and on the chosen
-- proof term for the K-shift, this module will take a long time to
-- compile (and then to run) when this alternative code is
-- enabled. The term "pigeon-program" defined in the module
-- PigeonProgram avoids the long compilation time.
