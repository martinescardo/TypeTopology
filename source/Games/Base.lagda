Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Games.Base where

open import MLTT.Spartan hiding (J)

sub : {R X : Type} {Y : X → Type} → (Σ Y → R) → (x : X) → Y x → R
sub q x xs = q (x , xs)

\end{code}
