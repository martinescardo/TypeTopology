Created by Ayberk Tosun, August 2024.

In this module, we collect properties of lists.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

module MLTT.List-Properties where

open import Fin.Type
open import MLTT.List
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.PropTrunc
open import UF.Subsingletons

\end{code}

The empty list has no members.

\begin{code}

not-in-empty-list : {A : 𝓤 ̇ } {x : A} → ¬ member x []
not-in-empty-list ()

\end{code}

We define the list indexing function `nth` below and prove that it is a
surjection.

\begin{code}

module list-indexing (pt : propositional-truncations-exist) {X : 𝓤 ̇ } where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 nth : (xs : List X) → Fin (length xs) → Σ x ꞉ X , ∥ member x xs ∥
 nth (x ∷ _)  (inr ⋆) = x , ∣ in-head ∣
 nth (_ ∷ xs) (inl n) = x , ∥∥-functor in-tail (pr₂ IH)
  where
   IH : Σ x ꞉ X , ∥ member x xs ∥
   IH = nth xs n

   x : X
   x = pr₁ IH

 nth-is-surjection : (xs : List X) → is-surjection (nth xs)
 nth-is-surjection []       (y , μ) = ∥∥-rec ∃-is-prop (λ ()) μ
 nth-is-surjection (x ∷ xs) (y , μ) = ∥∥-rec ∃-is-prop † μ
  where
   † : member y (x ∷ xs) → ∃ i ꞉ Fin (length (x ∷ xs)) , (nth (x ∷ xs) i ＝ y , μ)
   † in-head     = ∣ inr ⋆ , to-subtype-＝ (λ _ → ∥∥-is-prop) refl ∣
   † (in-tail p) = ∥∥-rec ∃-is-prop ‡ IH
    where
     IH : (y , ∣ p ∣) ∈image nth xs
     IH = nth-is-surjection xs (y , ∣ p ∣)

     ‡ : Σ i ꞉ Fin (length xs) , (nth xs i ＝ y , ∣ p ∣)
       → ∃ i ꞉ Fin (length (x ∷ xs)) , (nth (x ∷ xs) i ＝ y , μ)
     ‡ (i , q) = ∣ inl i , to-subtype-＝ (λ _ → ∥∥-is-prop) (pr₁ (from-Σ-＝ q)) ∣

\end{code}

Added by Fredrik Nordvall Forsberg 14 May 2025

\begin{code}

map-equiv : {A B : 𝓤 ̇ } → {f : A → B} → is-equiv f → is-equiv (map f)
map-equiv {A = A} {B} {f} e = qinvs-are-equivs (map f) (map f⁻¹ , η , ε)
 where
  f⁻¹ = inverse f e

  η : (l : List A) → map f⁻¹ (map f l) ＝ l
  η [] = refl
  η (a ∷ l) = ap₂ _∷_ (inverses-are-retractions f e a) (η l)

  ε : (l : List B) → map f (map f⁻¹ l) ＝ l
  ε [] = refl
  ε (b ∷ l) = ap₂ _∷_ (inverses-are-sections f e b) (ε l)

\end{code}
