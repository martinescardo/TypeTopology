Martin Escardo, Paulo Oliva, 2-27 July 2021

This module has functions to build games.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt

module Games.Constructor
        (R : Type)
        (fe : Fun-Ext)
       where

open import Games.TypeTrees
open import Games.FiniteHistoryDependent R fe

\end{code}

We use the type GameJ to present games equipped with selection
functions, as in some examples, such as tic-tac-toe this is easier
than to give a game directly.

\begin{code}

data GameJ : Type₁ where
  leaf   : R → GameJ
  branch : (X : Type) (Xf : X → GameJ) (ε : J X) → GameJ

dtt : GameJ → 𝕋
dtt (leaf x)        = []
dtt (branch X Xf ε) = X ∷ λ x → dtt (Xf x)

predicate : (Γ : GameJ) → Path (dtt Γ) → R
predicate (leaf r)        ⟨⟩        = r
predicate (branch X Xf ε) (x :: xs) = predicate (Xf x) xs

selections : (Γ : GameJ) → 𝓙 (dtt Γ)
selections (leaf r)        = ⟨⟩
selections (branch X Xf ε) = ε :: (λ x → selections (Xf x))

quantifiers : (Γ : GameJ) → 𝓚 (dtt Γ)
quantifiers (leaf r)        = ⟨⟩
quantifiers (branch X Xf ε) = overline ε :: (λ x → quantifiers (Xf x))

Game-from-GameJ : GameJ → Game
Game-from-GameJ Γ = game (dtt Γ) (predicate Γ) (quantifiers Γ)

strategyJ : (Γ : GameJ) → Strategy (dtt Γ)
strategyJ Γ = selection-strategy (selections Γ) (predicate Γ)

Selection-Strategy-TheoremJ : (Γ : GameJ)
                            → is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
Selection-Strategy-TheoremJ Γ = γ
 where
  δ : (Γ : GameJ) → (selections Γ) are-selections-of (quantifiers Γ)
  δ (leaf r)        = ⟨⟩
  δ (branch X Xf ε) = (λ p → refl) , (λ x → δ (Xf x))

  γ : is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
  γ = Selection-Strategy-Theorem (Game-from-GameJ Γ) (selections Γ) (δ Γ)

\end{code}

The following is used in conjunction with GameJ to build certain games
in a convenient way.

\begin{code}

build-GameJ : (draw       : R)
              (Board      : Type)
              (transition : Board → R + (Σ M ꞉ Type , (M → Board) × J M))
              (n          : ℕ)
              (b          : Board)
            → GameJ
build-GameJ draw Board transition n b = h n b
 where
  h : ℕ → Board → GameJ
  h 0        b = leaf draw
  h (succ n) b = g (transition b) refl
   where
    g : (f : R + (Σ M ꞉ Type , (M → Board) × J M)) → transition b ＝ f → GameJ
    g (inl r)              p = leaf r
    g (inr (M , play , ε)) p = branch M Xf ε
     where
      Xf : M → GameJ
      Xf m = h n (play m)

build-Game : (draw       : R)
             (Board      : Type)
             (transition : Board → R + (Σ M ꞉ Type , (M → Board) × J M))
             (n          : ℕ)
             (b          : Board)
           → Game
build-Game draw Board transition n b = Game-from-GameJ (build-GameJ draw Board transition n b)

\end{code}

-- More tests.

-- \begin{code}

-- module test where

--  open import MLTT.NonSpartanMLTTTypes

--  ε₂ : J Bool Bool
--  ε₂ p = p true

--  h : ℕ → 𝕋
--  h 0        = []
--  h (succ n) = Bool ∷ λ _ → h n

--  εs : (n : ℕ) → 𝓙 Bool (h n)
--  εs 0        = ⟨⟩
--  εs (succ n) = ε₂ :: λ _ → εs n

--  ε : (n : ℕ) → J Bool (Path (h n))
--  ε n = J-sequence (εs n)

--  qq : (n : ℕ) → Path (h n) → Bool
--  qq 0        ⟨⟩        = true
--  qq (succ n) (x :: xs) = not x && qq n xs

--  test : (n : ℕ) → Path (h n)
--  test n = ε n (qq n)

-- \end{code}

-- TODO. Generalize the above to multi-valued quantifiers, as in [1], using monads.

-- \begin{code}

-- data GameK (R : Type) : Type₁ where
--   leaf   : R → GameK
--   branch : (X : Type) (Xf : X → GameK) (ϕ : K X) → GameK

-- \end{code}

-- TODO. GameK ≃ Game and we have a map GameJ → GameK.

-- TODO. Define game isomorphism (and possibly homomorphism more generally).

-- \begin{code}

-- data 𝕋' (X : Type) : Type₁ where
--   []  : 𝕋' X
--   _∷_ : (A : X → Type) (Xf : (x : X) → A x → 𝕋' X) → 𝕋' X

-- record Game⁻ : Type₁ where
--  constructor game⁻
--  field
--   Xt  : 𝕋
--   R   : Type
--   q   : Path Xt → R

-- \end{code}

-- TODO. Game⁻ ≃ (Σ R : Type, D𝕋 R) for a suitable definition of
-- D𝕋. Idea: In Game⁻, we know how to play the game, but we don't know
-- what the objective of the game is.
