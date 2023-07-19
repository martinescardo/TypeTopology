```agda
{-# OPTIONS --without-K --exact-split #-}

open import UF.FunExt
open import UF.Subsingletons
open import Integers.Type
open import MLTT.Spartan
open import Unsafe.Haskell
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter2.Vectors

module TWA.Thesis.Chapter6.Main where

postulate fe : FunExt
postulate pe : PropExt

open import TWA.Thesis.Chapter6.SignedDigitExamples fe pe

𝟚ᴺ = ℕ → 𝟚

𝟛-to-ℤ : 𝟛 → ℤ
𝟛-to-ℤ −1 = negsucc 0
𝟛-to-ℤ  O = pos 0
𝟛-to-ℤ +1 = pos 1

show𝟛 : 𝟛 → String
show𝟛 = showℤ ∘ 𝟛-to-ℤ

show𝟚ᴺ-prefix : (ℕ → 𝟚) → ℕ → String
show𝟚ᴺ-prefix x 0 = ""
show𝟚ᴺ-prefix x (succ n)
 = show𝟛 (𝟚→𝟛 (x 0)) +++ "," +++ show𝟚ᴺ-prefix (x ∘ succ) n

show𝟛ᴺ-prefix : 𝟛ᴺ → ℕ → String
show𝟛ᴺ-prefix x 0 = ""
show𝟛ᴺ-prefix x (succ n)
 = show𝟛 (x 0) +++ "," +++ show𝟛ᴺ-prefix (x ∘ succ) n

show𝟛ᴺ×𝟛ᴺ-prefix : 𝟛ᴺ × 𝟛ᴺ → ℕ → String
show𝟛ᴺ×𝟛ᴺ-prefix (x , y) n
 = show𝟛ᴺ-prefix x n +++ " ;\n" +++ show𝟛ᴺ-prefix y n

show𝟚ᴺ×𝟚ᴺ-prefix : 𝟚ᴺ × 𝟚ᴺ → ℕ → String
show𝟚ᴺ×𝟚ᴺ-prefix (x , y) n
 = show𝟚ᴺ-prefix x n +++ " ;\n" +++ show𝟚ᴺ-prefix y n


open Regression-Example2

main : IO Unit
main = putStrLn (show𝟚ᴺ×𝟚ᴺ-prefix (reg𝓞 5) 30
         -- +++ "\n" +++ show𝟚ᴺ-prefix (example' 4) 30
       --   +++ "\n" +++ show𝟚ᴺ-prefix (example' 5) 30
           )
            --  ++ show𝟚ᴺ-prefix (example2 



-- putStrLn (show𝟛ᴺ-prefix (preg-test-eq fe 6 (1/3 fe)) 50)

```
