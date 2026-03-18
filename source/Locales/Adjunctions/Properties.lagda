---
title:        Properties of posetal adjunctions
author:       Ayberk Tosun
date-started: 2024-05-20
---

Many facts about posetal adjunctions have previously been recorded in modules

  - `Locales.PosetalAdjunction`, and
  - `Locales.AdjointFunctorTheoremForFrames`.

This is a new module in which I will be factoring out some of these facts and
organizing them in a more careful way. One motivation for this is that some of
these constructions and theorems have been formulated for frames, even though
they apply to the much more general setting of arbitrary posets. Now that I want
to apply them to distributive lattices, generalizing them has become necessary.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Locales.Adjunctions.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.PosetalAdjunction pt fe
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We work in a module parameterized by two posets `P` and `Q`.

\begin{code}

module Some-Properties-Of-Posetal-Adjunctions
        (P : Poset 𝓤  𝓥)
        (Q : Poset 𝓤' 𝓥')
       where

 open PosetalAdjunctionBetween P Q

\end{code}

The two adjunction laws.

\begin{code}

 adjunction-law₁ : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                  → (𝒻 ⊣ ℊ) holds
                 → {x : ∣ P ∣ₚ} {y : ∣ Q ∣ₚ}
                 → (f x ≤[ Q ] y ⇒ x ≤[ P ] g y) holds
 adjunction-law₁ 𝒻 ℊ adj {x} {y} = pr₁ (adj x y)

 adjunction-law₂ : (𝒻@(f , _) : P ─m→ Q) (ℊ@(g , _) : Q ─m→ P)
                 → (𝒻 ⊣ ℊ) holds
                 → {x : ∣ P ∣ₚ} {y : ∣ Q ∣ₚ}
                 → (x ≤[ P ] g y ⇒ f x ≤[ Q ] y) holds
 adjunction-law₂ 𝒻 ℊ adj {x} {y} = pr₂ (adj x y)

\end{code}

Monotone equivalences are adjoints.

\begin{code}

 monotone-equivalences-are-adjoint : (sₘ@(s , _) : P ─m→ Q) (rₘ@(r , _) : Q ─m→ P)
                                   → s ∘ r ∼ id
                                   → r ∘ s ∼ id
                                   → (sₘ ⊣ rₘ) holds
 monotone-equivalences-are-adjoint (s , 𝓂₁) (r , 𝓂₂) φ ψ x y = † , ‡
  where
   open PosetReasoning Q

   † : (s x ≤[ Q ] y ⇒ x ≤[ P ] r y) holds
   † p = sections-are-order-embeddings P Q s r 𝓂₂ ψ ※
    where
     Ⅰ = p
     Ⅱ = φ y ⁻¹

     ※ : (s x ≤[ Q ] s (r y)) holds
     ※ = s x      ≤⟨ Ⅰ ⟩
         y        ＝⟨ Ⅱ ⟩ₚ
         s (r y)  ■

   ‡ : (x ≤[ P ] r y ⇒ s x ≤[ Q ] y) holds
   ‡ p = s x      ≤⟨ Ⅰ ⟩
         s (r y)  ＝⟨ Ⅱ ⟩ₚ
         y        ■
          where
           Ⅰ = 𝓂₁ (x , r y) p
           Ⅱ = φ y

\end{code}
