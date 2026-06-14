Martin Escardo

Brouwer ordinal codes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.BrouwerCodes where

open import MLTT.Spartan

data B : 𝓤₀ ̇ where
 Z : B
 S : B → B
 L : (ℕ → B) → B

B-rec : {X : 𝓤 ̇ } → X → (X → X) → ((ℕ → X) → X) → B → X
B-rec {𝓤} {X} z s l = h
 where
  h : B → X
  h Z      = z
  h (S b)  = s (h b)
  h (L bs) = l (λ i → h (bs i))

B-induction : {P : B → 𝓤 ̇ }
            → P Z
            → ((b : B) → P b → P (S b))
            → ((bs : ℕ → B) → ((i : ℕ) → P (bs i)) → P (L bs))
            → ((b : B) → P b)
B-induction {𝓤} {P} z s l = h
 where
  h : (b : B) → P b
  h Z      = z
  h (S b)  = s b (h b)
  h (L bs) = l bs (λ i → h (bs i))

\end{code}
