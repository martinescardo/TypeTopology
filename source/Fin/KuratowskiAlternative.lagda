---
title: Alternative Definition of Kuratowski-finiteness
author: Ayberk Tosun
date-started: 2023-12-03
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt

module Fin.KuratowskiAlternative (pt : propositional-truncations-exist)
                                 (fe : Fun-Ext) where

open import MLTT.List
open import MLTT.Spartan
open import UF.Logic
open import Fin.Kuratowski

open PropositionalTruncation pt

\end{code}

An alternative way to state the notion of Kuratowski-finiteness for a type `X`
is `X` being _listed_.

\begin{code}

is-Kuratowski-finite₀ : 𝓤₀  ̇ → 𝓤₀  ̇
is-Kuratowski-finite₀ X = ∥ listed X ∥

\end{code}

\section{Alternative implies original}

\begin{code}

kuratowski-finite₀-implies-kuratowski-finite : (X : 𝓤₀  ̇)
                                             → is-Kuratowski-finite₀ X
                                             → is-Kuratowski-finite  X
kuratowski-finite₀-implies-kuratowski-finite X φ = ∥∥-rec ∃-is-prop † φ
 where
  † : Σ xs ꞉ List X , ((x : X) → (member₀ x xs) holds) → ∃ (λ n → Fin n ↠ X)
  † (xs , ψ) = ∣ length xs , nth xs , ψ ∣

\end{code}
