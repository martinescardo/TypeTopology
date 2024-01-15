
Martin Escardo, Paulo Oliva, 2-27 July 2021

Examples of type trees.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.Examples where

open import MLTT.Spartan hiding (J)
open import MLTT.Fin
open import Games.TypeTrees
open import Games.J
open import Games.K

module permutations where

 open import MLTT.Athenian

 no-repetitions : ℕ → Type → 𝑻
 no-repetitions 0        X = []
 no-repetitions (succ n) X = X ∷ λ (x : X) → no-repetitions n (Σ y ꞉ X , y ≠ x)

 Permutations : ℕ → Type
 Permutations n = Path (no-repetitions n (Fin n))

 example-permutation2 : Permutations 2
 example-permutation2 = 𝟎 :: ((𝟏 , (λ ())) :: ⟨⟩)

 example-permutation3 : Permutations 3
 example-permutation3 = 𝟐 :: ((𝟏 :: (λ ())) :: (((𝟎 , (λ ())) , (λ ())) :: ⟨⟩))

\end{code}

\begin{code}

open import UF.FunExt

module search (fe : Fun-Ext) where

 open import MLTT.Athenian
 open import Games.FiniteHistoryDependent Bool

 open J-definitions Bool

 ε₂ : J Bool
 ε₂ p = p true

 h : ℕ → 𝑻
 h 0        = []
 h (succ n) = Bool ∷ λ _ → h n

 εs : (n : ℕ) → 𝓙 (h n)
 εs 0        = ⟨⟩
 εs (succ n) = ε₂ :: λ _ → εs n

 ε : (n : ℕ) → J (Path (h n))
 ε n = sequenceᴶ (εs n)

 qq : (n : ℕ) → Path (h n) → Bool
 qq 0        ⟨⟩        = true
 qq (succ n) (x :: xs) = not x && qq n xs

 test : (n : ℕ) → Path (h n)
 test n = ε n (qq n)

\end{code}

\begin{code}

module another-game-representation (R : Type) where

 open import Games.FiniteHistoryDependent R

 open K-definitions R

 data GameK : Type₁ where
  leaf   : R → GameK
  branch : (X : Type) (Xf : X → GameK) (ϕ : K X) → GameK

\end{code}

TODO. GameK ≃ Game and we have a map GameJ → GameK.

TODO. Define game isomorphism (and possibly homomorphism more generally).

\begin{code}

 data 𝑻' (X : Type) : Type₁ where
  []  : 𝑻' X
  _∷_ : (A : X → Type) (Xf : (x : X) → A x → 𝑻' X) → 𝑻' X

 record Game⁻ : Type₁ where
  constructor game⁻
  field
   Xt  : 𝑻
   q   : Path Xt → R

\end{code}

TODO. Game⁻ ≃ (Σ R : Type, 𝑻' R). In Game⁻, we know how to play the
game, but we don't know what the objective of the game is.
