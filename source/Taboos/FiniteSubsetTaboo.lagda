---
title:        Kuratowski-finite Subset Taboo
author:       Ayberk Tosun
date-started: 2023-11-27
---

Based on a proof that I learned from Martín Escardó on 2023-11-21, though the
proof I ended up writing here ended up being a bit different.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Taboos.FiniteSubsetTaboo (pt : propositional-truncations-exist)
                                (fe : Fun-Ext) where

open import Fin.Kuratowski pt
open import Fin.Type
open import MLTT.Negation
open import MLTT.Spartan
open import Naturals.Order
open import UF.DiscreteAndSeparated
open import UF.ExcludedMiddle
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset
open import UF.Powerset-Fin pt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties using (Ω-is-set)

open AllCombinators pt fe
open PropositionalSubsetInclusionNotation fe
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
type `X`, `has-finite-subset-property X` expresses that for every
Kuratowski-finite subset `F ⊆ X`, any further subset of `S ⊆ F` is also
Kuratowski-finite.

\begin{code}

Kuratowski-finiteness-is-hereditary :
 (X : 𝓤  ̇) → Ω (𝓤 ⁺)
Kuratowski-finiteness-is-hereditary X =
 Ɐ F ꞉ 𝓟 X , Ɐ S ꞉ 𝓟 X ,
  S ⊆ₚ F ⇒ is-Kuratowski-finite-subsetₚ F ⇒ is-Kuratowski-finite-subsetₚ S

\end{code}

The result that we prove in this module is the following

```
  finite-subset-property X → is-discrete X
```

We now prove two easy lemmas before we proceed to the proof of the main result
of interest.

Lemma 1:

\begin{code}

having-empty-enumeration-entails-emptiness :
 (X : 𝓤  ̇) → (e : 𝟘 {𝓤₀} → X) → is-surjection e → ¬ X
having-empty-enumeration-entails-emptiness X e σ x =
 ∥∥-rec 𝟘-is-prop (𝟘-elim ∘ pr₁) (σ x)

\end{code}

\begin{code}

having-nonempty-enumeration-entails-inhabitedness :
 (X : 𝓤  ̇) (n : ℕ) → 0 <ℕ n → (e : Fin n → X) → is-surjection e → X
having-nonempty-enumeration-entails-inhabitedness X (succ n) p e σ = e 𝟎

\end{code}

Satisfying the finite subset property gives decidable equality.

\begin{code}

finite-subset-property-gives-discreteness
 : (X : 𝓤  ̇)
 → is-set X
 → Kuratowski-finiteness-is-hereditary X holds
 → is-discrete X
finite-subset-property-gives-discreteness {𝓤} X 𝕤 ϡ x y =
 ∥∥-rec (decidability-of-prop-is-prop fe 𝕤) † (ϡ F S ι φ)
  where
   _＝ₚ_ : X → X → Ω 𝓤
   _＝ₚ_ x₁ x₂ = (x₁ ＝ x₂) , 𝕤

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

   † : Σ n ꞉ ℕ , Fin n ↠ 𝕋 S → (x ＝ y) + ¬ (x ＝ y)
   † (zero   , eˢ) = let
                      ν : ¬ 𝕋 S
                      ν = uncurry (having-empty-enumeration-entails-emptiness (𝕋 S)) eˢ
                     in
                      inr (λ p → ν (x , (∣ suc refl ∣ , p)))
   † (succ n , eˢ) = inl p
    where
     τ : 𝕋 S
     τ = uncurry
          (having-nonempty-enumeration-entails-inhabitedness (𝕋 S) (succ n) ⋆)
          eˢ

     p : x ＝ y
     p = pr₂ (pr₂ τ)

\end{code}

From this result, the following corollary follows:

    if every subset of a Kuratowski-finite subset of `Ω` is finite, then
    the law of excluded middle holds.

\begin{code}

finite-subset-property-for-Ω-gives-EM :
   {𝓤 : Universe}
 → propext 𝓤
 → Kuratowski-finiteness-is-hereditary (Ω 𝓤) holds
 → EM 𝓤
finite-subset-property-for-Ω-gives-EM {𝓤} pe ϡ = Ω-discrete-gives-EM fe pe †
 where
  † : is-discrete (Ω 𝓤)
  † = finite-subset-property-gives-discreteness (Ω 𝓤) (Ω-is-set fe pe) ϡ

\end{code}

Combining the two, we get:

\begin{code}

finite-subset-property-gives-EM :
   (𝓤 : Universe)
 → (pe : propext 𝓤)
 → ((X : 𝓤 ⁺  ̇) → Kuratowski-finiteness-is-hereditary X holds)
 → EM 𝓤
finite-subset-property-gives-EM 𝓤 pe ϡ =
 finite-subset-property-for-Ω-gives-EM pe (ϡ (Ω 𝓤))

\end{code}

TODO: prove the converse direction of `is-discrete X` implies
`finite-subset-property X`.
