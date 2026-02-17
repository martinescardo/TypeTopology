Martin Escardo and Paulo Oliva 2011

\begin{code}

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-Examples where

\end{code}

To perform experiments, evaluate "example1" or "example2" to normal
form. It is easy to create your own examples.

Also, if you wish, choose another implementation of the K-shift in
the wrapper module K-Shift following the instructions, and which
proof of the infinite pigeonhole theorem is used in the module
FinitePigeon, by importing a different module.

\begin{code}

open import InfinitePigeon.J-PigeonProgram
open import InfinitePigeon.Naturals
open import InfinitePigeon.Two
open import InfinitePigeon.Cantor
open import InfinitePigeon.DataStructures

\end{code}

Some randomly chosen examples of elements of the Cantor space to
play with:

\begin{code}

α¹ : ₂ℕ
α¹ 0 = ₁
α¹(succ n) = not(α¹ n)

α² : ₂ℕ
α² = 0 ^ 0 ^ 0 ^ 1 ^ 1 ^ 1 ^ 1 ^ 1 ^ α¹

α³ : ₂ℕ
α³ i = not(α² i)

α⁴ : ₂ℕ
α⁴ =  0 ^ 1 ^ 0 ^ 1 ^ 1 ^ 0 ^ 1 ^ 1 ^ 1 ^ α³

α⁵ : ₂ℕ
α⁵ =  0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 0 ^ 1 ^ α⁴

α⁶ : ₂ℕ
α⁶ =  0 ^ 1 ^ 1 ^ 0 ^ 0 ^ 0 ^ 1 ^ 0 ^ 1 ^ 0 ^ 0 ^ 0 ^ 0 ^ α⁵

\end{code}

To run an experiment, normalize the term "pigeon-program α m" for
suitable α and m:

\begin{code}

example1 : ₂ × List ℕ
example1 = pigeon-program α⁵ 6

example2 : ₂ × List ℕ
example2 = pigeon-program α⁵ 12

\end{code}

Alternatively, calculate b and s using the Theorem:

\begin{code}
{--
open import InfinitePigeon.FinitePigeon

b : ₂
b = ∃-witness(Theorem α m)

s : smaller(m + 1) → ℕ
s = ∃-witness(∃-elim(Theorem α m))
--}
\end{code}

Warning: depending on the example you build, and on the chosen
proof term for the K-shift, this module will take a long time to
compile (and then to run) when this alternative code is
enabled. The term "pigeon-program" defined in the module
PigeonProgram avoids the long compilation time.
