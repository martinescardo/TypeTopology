--------------------------------------------------------------------------------
title:        System F Resizing considered as an axiom
authors:      ["Sam Speight", "Ayberk Tosun"]
date-started: 2024-05-15
--------------------------------------------------------------------------------

This module contains some notes from various discussions with Sam Speight.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module UF.SystemFNotionOfResizing (fe : Fun-Ext) (pt : propositional-truncations-exist) where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Logic
open import UF.Size
open import UF.Subsingletons
open import UF.SubtypeClassifier

open Universal fe
open Existential pt

\end{code}

\begin{code}

System-F-Resizing : 𝓤₂  ̇
System-F-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Π x ꞉ A , B x) is 𝓤₀ small

\end{code}

One could also consider propositional System F resizing.

\begin{code}

Propositional-System-F-Resizing : 𝓤₂  ̇
Propositional-System-F-Resizing =
 (A : 𝓤₁  ̇) →
  (P : A → Ω 𝓤₀) →
   (Ɐ x ꞉ A , P x) holds is 𝓤₀ small

\end{code}

This propositional form is of course trivially implied by propositional
resizing.

\begin{code}

prop-resizing-implies-prop-f-resizing
 : propositional-resizing 𝓤₁ 𝓤₀
 → Propositional-System-F-Resizing
prop-resizing-implies-prop-f-resizing 𝕣 A P = 𝕣 (Π x ꞉ A , P x holds) †
 where
  † : is-prop (Π x ꞉ A , P x holds)
  † = holds-is-prop (Ɐ x ꞉ A , P x)

\end{code}

We could also consider Σ-resizing.

\begin{code}

Σ-Resizing : 𝓤₂  ̇
Σ-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Σ x ꞉ A , B x) is 𝓤₀ small

\end{code}

Similarly, ∃-resizing.

\begin{code}

∃-Resizing : 𝓤₂  ̇
∃-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Ǝ x ꞉ A , B x) holds is 𝓤₀ small

\end{code}

\begin{code}

prop-resizing-implies-∃-resizing : propositional-resizing 𝓤₁ 𝓤₀ → ∃-Resizing
prop-resizing-implies-∃-resizing 𝕣 A B =
 𝕣 ((Ǝ x ꞉ A , B x) holds) (holds-is-prop (Ǝ x ꞉ A , B x))

\end{code}
