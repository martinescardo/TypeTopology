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
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec) hiding (head)
open import MLTT.Fin
open import MLTT.List
open import MLTT.Bool
open import UF.Base
open import TGH.Thunk
open import TGH.NatOrder
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.ComplexityDefinitionsResults fe
open import TGH.P fe
open import TGH.LastTimeListValueIndependent fe
open import TGH.LastLinearTimeEager fe

firstTrue : List Bool → Bool
firstTrue [] = true
firstTrue (b ∷ _) = b

lastTrue : List Bool → Bool
lastTrue [] = true
lastTrue (b ∷ []) = b
lastTrue (_ ∷ bs@(_ ∷ _)) = lastTrue bs

list-head-first-true : (xs : List Bool)
                     → nat-to-bool (list-head (map bool-to-nat xs))
                     ＝ firstTrue xs
list-head-first-true [] = refl
list-head-first-true (x ∷ _) = bool-nat-inverse x

list-last-last-true : (xs : List Bool)
                    → nat-to-bool (last' (map bool-to-nat xs))
                    ＝ lastTrue xs
list-last-last-true [] = refl
list-last-last-true (x ∷ []) = bool-nat-inverse x
list-last-last-true (x ∷ y ∷ xs) = list-last-last-true (y ∷ xs)

head-is-firstTrue : {n : ℕ} {Γ : Ctx n}
                  → (env : Env Γ)
                  → (xs : List Bool)
                  → nat-to-bool ((env [ head ]ₑ) (map bool-to-nat xs))
                  ＝ firstTrue xs
head-is-firstTrue env xs
 = nat-to-bool ((env [ head ]ₑ) (map bool-to-nat xs)) ＝⟨ ap nat-to-bool
   (head-correctness (map bool-to-nat xs)) ⟩
   nat-to-bool (list-head (map bool-to-nat xs)) ＝⟨ list-head-first-true xs ⟩
   firstTrue xs ∎

last-is-lastTrue : {n : ℕ} {Γ : Ctx n}
                 → (env : Env Γ)
                 → (xs : List Bool)
                 → nat-to-bool ((env [ last ]ₑ) (map bool-to-nat xs))
                 ＝ lastTrue xs
last-is-lastTrue env xs
 = nat-to-bool ((env [ last ]ₑ) (map bool-to-nat xs))
   ＝⟨ ap nat-to-bool (last-correctness (map bool-to-nat xs)) ⟩
   nat-to-bool (last' (map bool-to-nat xs)) ＝⟨ list-last-last-true xs ⟩
   lastTrue xs ∎

firstTrue∈P : firstTrue ∈P
firstTrue∈P _ _ = head-comp , head-is-firstTrue , (1 , eager-head-linear-time')

notFirstTrue∈P : (not ∘ firstTrue) ∈P
notFirstTrue∈P = P-closure₁ firstTrue firstTrue∈P

lastTrue∈P : lastTrue ∈P
lastTrue∈P _ _ = last-comp , last-is-lastTrue , (1 , last-linear-time)

notLastTrue∈P : (not ∘ lastTrue) ∈P
notLastTrue∈P = P-closure₁ lastTrue lastTrue∈P

firstOrLastTrue∈P : (λ bs → (firstTrue bs || lastTrue bs)) ∈P
firstOrLastTrue∈P = P-closure₂ firstTrue lastTrue firstTrue∈P lastTrue∈P

firstAndLastTrue∈P : (λ bs → (firstTrue bs && lastTrue bs)) ∈P
firstAndLastTrue∈P = P-closure₃ firstTrue lastTrue firstTrue∈P lastTrue∈P

\end{code}
