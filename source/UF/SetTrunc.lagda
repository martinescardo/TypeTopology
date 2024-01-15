Jon Sterling, 25 March 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SetTrunc where

open import MLTT.Spartan
open import UF.Sets
open import UF.Subsingletons

\end{code}

We use the existence of propositional truncations as an
assumption. The following type collects the data that constitutes this
assumption.

\begin{code}

record set-truncations-exist : 𝓤ω where
 field
  set-trunc : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  set-trunc-is-set : {𝓤 : Universe} {X : 𝓤 ̇ } → is-set (set-trunc X)
  set-trunc-in : {𝓤 : Universe} {X : 𝓤 ̇ } → X → (set-trunc X)
  set-trunc-ind
   : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (Y : set-trunc X → 𝓥 ̇ )
   → ((x : set-trunc X ) → is-set (Y x))
   → ((x : X) → Y (set-trunc-in x))
   → (x : set-trunc X)
   → Y x
  set-trunc-ind-β
   : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (Y : set-trunc X → 𝓥 ̇ )
   → (Y-set : (x : set-trunc X ) → is-set (Y x))
   → (h : (x : X) → Y (set-trunc-in x))
   → (x : X)
   → set-trunc-ind Y Y-set h (set-trunc-in x) ＝ h x



 set-trunc-rec
  : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (Y : 𝓥 ̇ )
  → is-set Y
  → (X → Y)
  → set-trunc X
  → Y
 set-trunc-rec _ Y-set =
  set-trunc-ind _ (λ _ → Y-set)
