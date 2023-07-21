[⇐ Index](../html/TWA.Thesis.index.html)

# Main

```agda
{-# OPTIONS --without-K --exact-split #-}

open import UF.FunExt
open import UF.Subsingletons
open import Integers.Type
open import MLTT.Spartan
open import Unsafe.Haskell

open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter5.SignedDigit

module TWA.Thesis.Chapter6.Main where

postulate fe : FunExt
postulate pe : PropExt

open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe
open import TWA.Thesis.Chapter6.SignedDigitExamples fe pe

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
```

Open the Example module here from SignedDigitExamples.lagda.md

```
open Regression-Example2
```

Write the particular example run here, i.e. one of:
 * search-test-tb / search-test / search-test-tb' / serach-test'
 * opt-test / opt-test'
 * reg𝓞 / regΨ𝓞 / opt𝓞 / optΨ𝓞

```
test = reg𝓞
```

Write the correct printer here, i.e. one of:
 * show𝟛ᴺ-prefix
 * show𝟚ᴺ-prefix
 * show𝟛ᴺ×𝟛ᴺ-prefix
 * show𝟚ᴺ×𝟚ᴺ-prefix

```
print = show𝟚ᴺ×𝟚ᴺ-prefix
```

Write the requested precision here, i.e. a natural number.

```
prec = 5
```

```
main : IO Unit
main = putStrLn (print (test 5) 30)
```

[⇐ Index](../html/TWA.Thesis.index.html)
