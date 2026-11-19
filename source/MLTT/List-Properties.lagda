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
not-in-empty-list {𝓤} {A} {x} = empty-list-has-no-members x

\end{code}

We define the list indexing function `nth` below and prove that it is a
surjection.

\begin{code}

module list-indexing (pt : propositional-truncations-exist) {X : 𝓤 ̇ } where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 nth : (xs : List X) → Fin (length xs) → Σ x ꞉ X , ∥ member x xs ∥
 nth []       i       = 𝟘-elim i
 nth (x ∷ _)  (inr ⋆) = x , ∣ in-head ∣
 nth (_ ∷ xs) (inl n) = x , ∥∥-functor in-tail (pr₂ IH)
  where
   IH : Σ x ꞉ X , ∥ member x xs ∥
   IH = nth xs n

   x : X
   x = pr₁ IH

 nth-is-surjection : (xs : List X) → is-surjection (nth xs)
 nth-is-surjection []       (y , μ) =
  ∥∥-rec ∃-is-prop (λ m → 𝟘-elim (not-in-empty-list m)) μ
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

Added by Martin Escardo and Paulo Oliva 17th November 2026.

\begin{code}

All-map : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {Q : A → 𝓦 ̇ } {as : List A}
        → ((a : A) → P a → Q a) → All P as → All Q as
All-map f []       = []
All-map f (b ∷ bs) = f _ b ∷ All-map f bs

module _ {A : 𝓤 ̇ } (P : A → 𝓥 ̇ ) (d : (a : A) → is-decidable (P a)) where

 take-until : List A → List A
 take-until []       = []
 take-until (a ∷ as) = a ∷ Cases (d a) (λ _ → []) (λ _ → take-until as)

 take-until-is-non-empty : (as : List A)
                         → is-non-empty as
                         → is-non-empty (take-until as)
 take-until-is-non-empty []       ν = 𝟘-elim ν
 take-until-is-non-empty (a ∷ as) _ = cons-is-non-empty

 take-until-preserves : (Q : A → 𝓦 ̇ ) (as : List A)
                      → All Q as → All Q (take-until as)
 take-until-preserves Q []       []       = []
 take-until-preserves Q (a ∷ as) (b ∷ bs) = b ∷ I (d a)
  where
   I : (e : is-decidable (P a))
     → All Q (Cases e (λ _ → []) (λ _ → take-until as))
   I (inl _) = []
   I (inr _) = take-until-preserves Q as bs

\end{code}

End of addition.
