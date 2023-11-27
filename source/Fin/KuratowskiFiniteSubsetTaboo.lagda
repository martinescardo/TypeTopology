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

open AllCombinators pt fe

open PropositionalTruncation pt

\end{code}

The propositional version of `is-Kuratowski-finite-subset`:

\begin{code}

is-Kuratowski-finite-subsetₚ : {X : 𝓤  ̇} → 𝓟 X → Ω 𝓤
is-Kuratowski-finite-subsetₚ P =
 is-Kuratowski-finite-subset P , being-Kuratowski-finite-is-prop

\end{code}

\begin{code}

subsets-of-finite-sets-are-finite : (X : 𝓤  ̇) → Ω (𝓤 ⁺)
subsets-of-finite-sets-are-finite X =
 let
  open PropositionalSubsetInclusionNotation fe
 in
  Ɐ F ꞉ 𝓟 X ,
   Ɐ S ꞉ 𝓟 X ,
    (S ⊆ₚ F) ⇒ is-Kuratowski-finite-subsetₚ F ⇒ is-Kuratowski-finite-subsetₚ S

\end{code}

\begin{code}

having-empty-enumeration-means-empty : (X : 𝓤  ̇)
                                     → (e : 𝟘 {𝓤₀} → X)
                                     → is-surjection e
                                     → ¬ X
having-empty-enumeration-means-empty X e σ x =
 ∥∥-rec 𝟘-is-prop (λ { (() , _) }) (σ x)

having-nonempty-enumeration-entails-being-inhabited : (X : 𝓤  ̇) (n : ℕ)
                                                    → 0 <ℕ n
                                                    → (e : Fin n → X)
                                                    → is-surjection e
                                                    → X
having-nonempty-enumeration-entails-being-inhabited X (succ n) p e σ = e 𝟎

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
                     ν = having-empty-enumeration-means-empty (𝕋 S) (eˢ .pr₁) (eˢ .pr₂)
                    in
                     ∣ inr (λ p → ν (x , (∣ suc refl ∣ , p))) ∣
  † (succ n , eˢ) =
   let
    ϑ : 𝕋 S
    ϑ = having-nonempty-enumeration-entails-being-inhabited (𝕋 S) (succ n) ⋆ (eˢ .pr₁) (eˢ .pr₂)
   in
    ∣ inl (pr₂ (pr₂ ϑ)) ∣

\end{code}
