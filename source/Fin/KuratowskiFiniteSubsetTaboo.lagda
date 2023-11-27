---
author: Ayberk Tosun
date-started: 2023-11-27
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt

module Fin.KuratowskiFiniteSubsetTaboo (pt : propositional-truncations-exist)
                                       (fe : Fun-Ext) where

open import Fin.Kuratowski pt
open import MLTT.Spartan
open import MLTT.Negation
open import Naturals.Order
open import UF.Sets
open import Fin.Type
open import UF.Powerset
open import UF.Powerset-Fin pt
open import UF.SubtypeClassifier
open import UF.Logic
open import UF.DiscreteAndSeparated
open import UF.ImageAndSurjection pt
open import UF.Subsingletons
open import UF.SubtypeClassifier-Properties using (Ω-is-set)
open PropositionalSubsetInclusionNotation fe

open AllCombinators pt fe

open PropositionalTruncation pt

\end{code}

Let us first define a propositional version of `is-Kuratowski-finite-subset` for
the sake of convenience.

\begin{code}

is-Kuratowski-finite-subsetₚ : {X : 𝓤  ̇} → 𝓟 X → Ω 𝓤
is-Kuratowski-finite-subsetₚ P =
 is-Kuratowski-finite-subset P , being-Kuratowski-finite-is-prop

\end{code}

We now define a predicate expressing the taboo we are interested in: given a
type `X`, `subsets-of-finite-are-finite X` expresses that for every
Kuratowski-finite subset `F ⊆ X`, any further subset of `S ⊆ F` is also
Kuratowski-finite.

\begin{code}

subsets-of-finite-sets-are-finite : (X : 𝓤  ̇) → Ω (𝓤 ⁺)
subsets-of-finite-sets-are-finite X =
 Ɐ F ꞉ 𝓟 X ,
  Ɐ S ꞉ 𝓟 X ,
  (S ⊆ₚ F) ⇒ is-Kuratowski-finite-subsetₚ F ⇒ is-Kuratowski-finite-subsetₚ S

\end{code}

The result that we prove in this module is the following

```
  subsets-of-finite-sets-are-finite X → ∀ x y : X , ∥ is-decidable (x ＝ y) ∥
```

We now prove two easy lemmas we proceed to the proof of the main result of interest.

Lemma 1.

\begin{code}

having-empty-enumeration-means-empty : (X : 𝓤  ̇)
                                     → (e : 𝟘 {𝓤₀} → X)
                                     → is-surjection e
                                     → ¬ X
having-empty-enumeration-means-empty X e σ x =
 ∥∥-rec 𝟘-is-prop (λ { (() , _) }) (σ x)

\end{code}

\begin{code}

having-nonempty-enumeration-entails-being-inhabited : (X : 𝓤  ̇) (n : ℕ)
                                                    → 0 <ℕ n
                                                    → (e : Fin n → X)
                                                    → is-surjection e
                                                    → X
having-nonempty-enumeration-entails-being-inhabited X (succ n) p e σ = e 𝟎

\end{code}

Satisfying the finite subset property gives decidable equality.

\begin{code}

subsets-of-finite-subsets-being-finite-gives-decidable-equality
 : (X : 𝓤  ̇)
 → is-set X
 → subsets-of-finite-sets-are-finite X holds
 → (x y : X) → ∥ (x ＝ y) + ¬ (x ＝ y) ∥
subsets-of-finite-subsets-being-finite-gives-decidable-equality X 𝕤 ϡ x y =
 ∥∥-rec ∥∥-is-prop † (ϡ F S ι φ)
  where
   F : 𝓟 X
   F z = ∥ (z ＝ x) + (z ＝ y) ∥Ω

   e : Fin 2 → 𝕋 F
   e 𝟎 = x , ∣ inl refl ∣
   e 𝟏 = y , ∣ inr refl ∣

   σ : is-surjection e
   σ (z , p) = ∥∥-rec ∃-is-prop † p
    where
     † : (z ＝ x) + (z ＝ y) → ∃ i ꞉ Fin 2 , e i ＝ (z , p)
     † (inl refl) = ∣ 𝟎 , to-subtype-＝ (holds-is-prop ∘ F) refl ∣
     † (inr refl) = ∣ 𝟏 , to-subtype-＝ (holds-is-prop ∘ F) refl  ∣

   φ : is-Kuratowski-finite-subset F
   φ = ∣ 2 , e , σ ∣

   S : 𝓟 X
   S z = F z ∧ ((x ＝ y) , 𝕤)

   ι : S ⊆ F
   ι z (p , q) = ∥∥-rec (holds-is-prop (F z)) † p
    where
     † : (z ＝ x) + (z ＝ y) → F z holds
     † (inl refl) = p
     † (inr refl) = p

   † : Σ n ꞉ ℕ , Fin n ↠ 𝕋 S → ∥ (x ＝ y) + ¬ (x ＝ y) ∥
   † (zero   , eˢ) = let
                      ν : ¬ 𝕋 S
                      ν = uncurry (having-empty-enumeration-means-empty (𝕋 S)) eˢ
                     in
                      ∣ inr (λ p → ν (x , (∣ suc refl ∣ , p))) ∣
   † (succ n , eˢ) = ∣ inl p ∣
    where
     τ : 𝕋 S
     τ = uncurry
          (having-nonempty-enumeration-entails-being-inhabited (𝕋 S) (succ n) ⋆)
          eˢ

     p : x ＝ y
     p = pr₂ (pr₂ τ)

\end{code}

From this result, the following corollary follows:

    if every subset of a Kuratowski-finite subset of `Ω` is finite, then
    the law of excluded middle holds.

\begin{code}

lem-from-the-finite-subset-property : (𝓤 : Universe)
                                    → propext 𝓤
                                    → subsets-of-finite-sets-are-finite (Ω 𝓤) holds
                                    → (P : Ω 𝓤) → ∥ P holds + (¬ₚ P) holds ∥
lem-from-the-finite-subset-property 𝓤 pe ϡ P = ∥∥-rec ∥∥-is-prop † (ζ P ⊤)
 where
  ζ : (P Q : Ω 𝓤) → ∥ (P ＝ Q) + ¬ (P ＝ Q) ∥
  ζ = subsets-of-finite-subsets-being-finite-gives-decidable-equality
       (Ω 𝓤)
       (Ω-is-set fe pe)
       ϡ

  † : (P ＝ ⊤) + ¬ (P ＝ ⊤) → ∥ (P holds) + (¬ₚ P) holds ∥
  † (inl p) = ∣ inl (equal-⊤-gives-holds P p) ∣
  † (inr ν) = ∣ inr (λ p → 𝟘-elim (ν (holds-gives-equal-⊤ pe fe P p))) ∣

\end{code}
