Theo Hepburn, started March 2025

Provides examples of some decsion problems
that are in the complexity class P.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.PExamples (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition
 renaming (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec) hiding (head)
open import MLTT.Fin
open import MLTT.List
open import MLTT.Bool
open import UF.Base
open import TGH.Thunk
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.ComplexityDefinitionsResults fe
open import TGH.P fe
open import TGH.LastTimeListValueIndependent fe
open import TGH.LastLinearTimeEager fe

first-true : List Bool → Bool
first-true [] = true
first-true (b ∷ _) = b

last-true : List Bool → Bool
last-true [] = true
last-true (b ∷ []) = b
last-true (_ ∷ bs@(_ ∷ _)) = last-true bs

list-head-first-true : (xs : List Bool)
                     → nat-to-bool (list-head (map bool-to-nat xs))
                     ＝ first-true xs
list-head-first-true [] = refl
list-head-first-true (x ∷ _) = bool-nat-inverse x

list-last-last-true : (xs : List Bool)
                    → nat-to-bool (last' (map bool-to-nat xs))
                    ＝ last-true xs
list-last-last-true [] = refl
list-last-last-true (x ∷ []) = bool-nat-inverse x
list-last-last-true (x ∷ y ∷ xs) = list-last-last-true (y ∷ xs)

head-is-first-true : {n : ℕ} {Γ : Ctx n}
                  → (env : Env Γ)
                  → (xs : List Bool)
                  → nat-to-bool ((env [ head ]ₑ) (map bool-to-nat xs))
                  ＝ first-true xs
head-is-first-true env xs
 = nat-to-bool ((env [ head ]ₑ) (map bool-to-nat xs)) ＝⟨ ap nat-to-bool
   (head-correctness (map bool-to-nat xs)) ⟩
   nat-to-bool (list-head (map bool-to-nat xs)) ＝⟨ list-head-first-true xs ⟩
   first-true xs ∎

last-is-last-true : {n : ℕ} {Γ : Ctx n}
                 → (env : Env Γ)
                 → (xs : List Bool)
                 → nat-to-bool ((env [ last ]ₑ) (map bool-to-nat xs))
                 ＝ last-true xs
last-is-last-true env xs
 = nat-to-bool ((env [ last ]ₑ) (map bool-to-nat xs))
   ＝⟨ ap nat-to-bool (last-correctness (map bool-to-nat xs)) ⟩
   nat-to-bool (last' (map bool-to-nat xs)) ＝⟨ list-last-last-true xs ⟩
   last-true xs ∎

first-true∈P : first-true ∈P
first-true∈P _ _ = head-comp , head-is-first-true , (1 , eager-head-linear-time')

not-first-true∈P : (not ∘ first-true) ∈P
not-first-true∈P = P-closure₁ first-true first-true∈P

last-true∈P : last-true ∈P
last-true∈P _ _ = last-comp , last-is-last-true , (1 , last-linear-time)

not-last-true∈P : (not ∘ last-true) ∈P
not-last-true∈P = P-closure₁ last-true last-true∈P

first-or-last-true∈P : (λ bs → (first-true bs || last-true bs)) ∈P
first-or-last-true∈P = P-closure₂ first-true last-true first-true∈P last-true∈P

first-and-last-true∈P : (λ bs → (first-true bs && last-true bs)) ∈P
first-and-last-true∈P = P-closure₃ first-true last-true first-true∈P last-true∈P

\end{code}
