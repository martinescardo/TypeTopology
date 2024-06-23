The disjoint sum X + Y of two types X and Y.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Plus where

open import MLTT.Plus-Type renaming (_+_ to infixr 1 _+_) public

dep-cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X + Y → 𝓦 ̇ }
          → ((x : X) → A (inl x))
          → ((y : Y) → A (inr y))
          → ((z : X + Y) → A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X + Y → A
cases = dep-cases

\end{code}

Sometimes it is useful to have the arguments in a different order:

\begin{code}

Cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → X + Y → (X → A) → (Y → A) → A
Cases z f g = cases f g z

dep-Cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
          → (z : X + Y)
          → ((x : X) → A (inl x))
          → ((y : Y) → A (inr y))
          → A z
dep-Cases {𝓤} {𝓥} {𝓦} {X} {Y} A z f g = dep-cases {𝓤} {𝓥} {𝓦} {X} {Y} {A} f g z

\end{code}

Added 4 March 2020 by Tom de Jong.

\begin{code}

dep-cases₃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : X + Y + Z → 𝓣 ̇ }
           → ((x : X) → A (inl x))
           → ((y : Y) → A (inr (inl y)))
           → ((z : Z) → A (inr (inr z)))
           → ((p : X + Y + Z) → A p)
dep-cases₃ f g h (inl x)       = f x
dep-cases₃ f g h (inr (inl y)) = g y
dep-cases₃ f g h (inr (inr z)) = h z

cases₃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
       → (X → A) → (Y → A) → (Z → A) → X + Y + Z → A
cases₃ = dep-cases₃

\end{code}

Added on 2024-06-23 by Ayberk Tosun.

\begin{code}

dep-cases₄ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓦'  ̇} {A : X + Y + Z + W → 𝓣 ̇ }
           → ((x : X) → A (inl x))
           → ((y : Y) → A (inr (inl y)))
           → ((z : Z) → A (inr (inr (inl z))))
           → ((w : W) → A (inr (inr (inr w))))
           → ((p : X + Y + Z + W) → A p)
dep-cases₄ f g h u (inl x)       = f x
dep-cases₄ f g h u (inr (inl y)) = g y
dep-cases₄ f g h u (inr (inr (inl z))) = h z
dep-cases₄ f g h u (inr (inr (inr w))) = u w

cases₄ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓦'  ̇} {A : 𝓣  ̇}
       → (X → A) → (Y → A) → (Z → A) → (W → A) → X + Y + Z + W → A
cases₄ = dep-cases₄

\end{code}
