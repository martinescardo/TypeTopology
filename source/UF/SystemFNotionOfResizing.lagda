--------------------------------------------------------------------------------
title:   System F Resizing considered as an axiom
authors: ["Sam Speight", "Ayberk Tosun"]
date-started: 2024-05-15
--------------------------------------------------------------------------------

This module contains some notes from various discussions with Sam Speight.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.SystemFNotionOfResizing (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Size
open import UF.Logic
open import UF.Equiv

open Universal fe

\end{code}

\begin{code}

System-F-Resizing : 𝓤₂  ̇
System-F-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Π x ꞉ A , B x) is 𝓤₀ small

\end{code}
