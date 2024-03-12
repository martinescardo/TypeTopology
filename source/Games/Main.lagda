Martin Escardo and Paulo Oliva, 19th March 2023.

Compile with

 $ Agda --compile --ghc-flag=-O2 Main.lagda

from TypeTopology/source/Games

To run, change to TypeTopology/source and do

 $ ./Main

The Haskell code is generated in TypeTopology/source/MAlonzo.

\begin{code}

{-# OPTIONS --without-K #-}

module Games.Main where

open import MLTT.Athenian
open import MLTT.Spartan
open import Unsafe.Haskell


{-
open import Games.TicTacToe0
open import Fin.Type renaming (Fin to Fin')

Fin-to-ℕ : {n : ℕ} → Fin' n → ℕ
Fin-to-ℕ {succ n} (inl x) = Fin-to-ℕ x
Fin-to-ℕ {succ n} (inr x) = 0

main : IO ⊤
main = putStrLn (showℕ (Fin-to-ℕ r))
-}

open import Games.alpha-beta

main₀ : IO Unit
main₀ = putStrLn (showListℕ test⋆)


main₁ : IO Unit
main₁ = putStrLn (showListℕ (test† fe))
 where
  open import UF.FunExt
  postulate fe : Fun-Ext

main₂ : IO Unit
main₂ = putStrLn (showListℕ testo)

main₃ : IO Unit
main₃ = putStrLn (showℕ test)

main = main₁

\end{code}
