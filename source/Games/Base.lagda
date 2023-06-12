Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Games.Base where

open import MLTT.Spartan hiding (J)

sub : {R X : Type} {Y : X → Type} → (Σ Y → R) → (x : X) → Y x → R
sub q x xs = q (x , xs)

\end{code}
