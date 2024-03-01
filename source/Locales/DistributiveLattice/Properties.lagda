---
title:       Distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Locales.DistributiveLattice.Properties
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import UF.Powerset-MultiUniverse
open import MLTT.List
open import MLTT.Spartan
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic
open import UF.Equiv hiding (_■)

open AllCombinators pt fe hiding (_∨_; _∧_)

\end{code}

\begin{code}

module _ (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L

\end{code}

𝟎 is an annihilator for _∧_.

\begin{code}

 ∧-annihilator : (x : ∣ L ∣ᵈ) → x ∧ 𝟎 ＝ 𝟎
 ∧-annihilator x = only-𝟎-is-below-𝟎ᵈ L (x ∧ 𝟎) †
  where
   ‡ : orderᵈ-∨ L (x ∧ 𝟎) 𝟎 holds
   ‡ = ∨-absorptive₃ 𝟎 x

   † : ((x ∧ 𝟎) ≤ᵈ[ L ] 𝟎) holds
   † = orderᵈ-∨-implies-orderᵈ L ‡

\end{code}

\begin{code}

 join-listᵈ : List ∣ L ∣ᵈ → ∣ L ∣ᵈ
 join-listᵈ []       = 𝟎
 join-listᵈ (x ∷ xs) = x ∨ join-listᵈ xs

 join-list-maps-∨-to-++ : (xs ys : List ∣ L ∣ᵈ)
                        → join-listᵈ xs ∨ join-listᵈ ys ＝ join-listᵈ (xs ++ ys)
 join-list-maps-∨-to-++ []        ys = ∨-unit₁ (join-listᵈ ys)
 join-list-maps-∨-to-++ (x₀ ∷ xs) ys =
  join-listᵈ (x₀ ∷ xs) ∨ join-listᵈ ys   ＝⟨ refl ⟩
  (x₀ ∨ join-listᵈ xs) ∨ join-listᵈ ys   ＝⟨ Ⅰ    ⟩
  x₀ ∨ (join-listᵈ xs ∨ join-listᵈ ys)   ＝⟨ Ⅱ    ⟩
  x₀ ∨ (join-listᵈ (xs ++ ys))           ＝⟨ refl ⟩
  join-listᵈ (x₀ ∷ xs ++ ys)             ∎
   where
    Ⅰ = ∨-associative x₀ (join-listᵈ xs) (join-listᵈ ys) ⁻¹
    Ⅱ = ap (x₀ ∨_) (join-list-maps-∨-to-++ xs ys)


 finite-distributivity : (xs : List ∣ L ∣ᵈ) (y : ∣ L ∣ᵈ)
                       → y ∧ join-listᵈ xs ＝ join-listᵈ (map (y ∧_) xs)
 finite-distributivity []       y = ∧-annihilator y
 finite-distributivity (x ∷ xs) y =
  y ∧ join-listᵈ (x ∷ xs)            ＝⟨ refl ⟩
  y ∧ (x ∨ join-listᵈ xs)            ＝⟨ Ⅰ    ⟩
  (y ∧ x) ∨ (y ∧ join-listᵈ xs)      ＝⟨ Ⅱ    ⟩
  join-listᵈ (map (y ∧_) (x ∷ xs))   ∎
   where
    Ⅰ = distributivityᵈ y x (join-listᵈ xs)
    Ⅱ = ap ((y ∧ x) ∨_) (finite-distributivity xs y)

\end{code}
