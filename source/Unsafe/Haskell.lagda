Martin Escardo, March 2023

Adapted from the standard library, to be able to compile Agda via
Haskell and print within compiled programs.

\begin{code}

{-# OPTIONS --without-K #-}

module Unsafe.Haskell where

open import MLTT.Spartan
open import MLTT.Athenian
open import Integers.Type

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → Bool

record builtin-Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor pair
  field
    fst : A
    snd : B fst

open builtin-Σ public

{-# BUILTIN SIGMA builtin-Σ #-}

primitive
  primStringUncons   : String → Maybe (builtin-Σ Char (λ _ → String))
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowChar       : Char → String
  primShowString     : String → String
  primShowNat        : ℕ → String

postulate IO : ∀ {a} → Set a → Set a
{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

record Unit : Set where
  instance constructor tt

{-# BUILTIN UNIT Unit #-}
{-# COMPILE GHC Unit = data () (()) #-}

postulate
  putStrLn : String → IO Unit

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

primitive primShowInteger : ℤ → String

showℤ : ℤ → String
showℤ = primShowInteger

showℕ : ℕ → String
showℕ = primShowNat

_+++_ : String → String → String
_+++_ = primStringAppend

infixr 9 _+++_

showListℕ : List ℕ → String
showListℕ [] = ""
showListℕ (x ∷ xs) = showℕ x +++ " , " +++ showListℕ xs

showListℕ×ℕ : List (ℕ × ℕ) → String
showListℕ×ℕ [] = ""
showListℕ×ℕ ((i , j) ∷ xs) = "(" +++ showℕ i +++ "," +++ showℕ j +++ ")" +++ showListℕ×ℕ xs

\end{code}
