Martin Escardo, 2014.

See also the file Fin-Properties.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Fin where

open import SpartanMLTT
open import UF-Subsingletons renaming (⊤Ω to ⊤)
open import Plus-Properties

Fin : ℕ → 𝓤₀ ̇
Fin 0        = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

fzero : {n : ℕ} → Fin (succ n)
fzero = inr ⋆

fsucc : {n : ℕ} → Fin n → Fin (succ n)
fsucc = inl

suc-lc : {n : ℕ} {j k : Fin n} → fsucc j ≡ fsucc k → j ≡ k
suc-lc = inl-lc

\end{code}

But it will more convenient to have them as patterns, for the sake of
clarity in definitions by pattern matching:

\begin{code}

pattern 𝟎     = inr ⋆
pattern 𝟏     = inl (inr ⋆)
pattern 𝟐     = inl (inl (inr ⋆))
pattern suc i = inl i

\end{code}

The induction principle for Fin is proved by induction on ℕ:

\begin{code}

Fin-induction : (P : (n : ℕ) → Fin n → 𝓤 ̇ )
              → ((n : ℕ) → P (succ n) 𝟎)
              → ((n : ℕ) (i : Fin n) → P n i → P (succ n) (suc i))
              →  (n : ℕ) (i : Fin n) → P n i

Fin-induction P β σ 0        i       = 𝟘-elim i
Fin-induction P β σ (succ n) 𝟎       = β n
Fin-induction P β σ (succ n) (suc i) = σ n i (Fin-induction P β σ n i)

\end{code}

We will not use this induction principle explicitly. Instead, we will
use the above pattern for similar definitions by induction.
