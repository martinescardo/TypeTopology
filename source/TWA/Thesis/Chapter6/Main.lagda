\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import UF.FunExt
open import UF.Subsingletons
open import Integers.Type
open import MLTT.Spartan
open import Unsafe.Haskell
open import TWA.Thesis.Chapter5.SignedDigit

module TWA.Thesis.Chapter6.Main where

postulate fe : FunExt
postulate pe : PropExt

open import TWA.Thesis.Chapter6.SignedDigitSearch fe pe

𝟛-to-ℤ : 𝟛 → ℤ
𝟛-to-ℤ −1 = negsucc 0
𝟛-to-ℤ  O = pos 0
𝟛-to-ℤ +1 = pos 1

show𝟛 : 𝟛 → String
show𝟛 = showℤ ∘ 𝟛-to-ℤ

show𝟛ᴺ-prefix : 𝟛ᴺ → ℕ → String
show𝟛ᴺ-prefix x 0 = ""
show𝟛ᴺ-prefix x (succ n)
 = show𝟛 (x 0) +++ "," +++ show𝟛ᴺ-prefix (x ∘ succ) n

show𝟛ᴺ×𝟛ᴺ-prefix : 𝟛ᴺ × 𝟛ᴺ → ℕ → String
show𝟛ᴺ×𝟛ᴺ-prefix (x , y) n
 = show𝟛ᴺ-prefix x n +++ " ; " +++ show𝟛ᴺ-prefix y n

module _ where

 open Search-Example3

 search-example-ty : ℕ → 𝟛ᴺ × 𝟛ᴺ
 search-example-ty = search-test₂

main : IO Unit
main = putStrLn (show𝟛ᴺ×𝟛ᴺ-prefix
             (search-example-ty 10)
             30)




-- putStrLn (show𝟛ᴺ-prefix (preg-test-eq fe 6 (1/3 fe)) 50)

\end{code}

Optimisation example 1 : Minimise neg to 8 degrees of precision
More complex examples get stack overflow or take too long :(

Search example 1 : Find x such that (-x/2) ≼ⁿ 1/4 (precisions 0,1,5,50,etc)
Search example 2 : Find x : ℕ → X such that x = bigMid O

For regression examples: first apply the regressed function
                         to points [-1, -2/3, -1/3, O, 1/3, 2/3, 1]
                         then check the parameters

Regression example 1  : Regress id using model (λ y x → neg y ⊕ x)
 [Global opt]
 
Regression example 2' : Regress (λ x → 1/3 ⊕ x) using the model (λ y x → y ⊕ x)
                        and pseudocloseness function from points [-1,O,1]
                        Precision level 8 worked well
 [Perfect]
Regression example 2  : Regress (λ x → 1/3 ⊕ x²) using the model (λ y x → y ⊕ x²)
                        and pseudocloseness function from points [-1,O,1]

Regression example 3  : Line of best fit the points (-1,-1), (O,O), (1,-1)
 [Interpolated]

Regression example 4  : 

