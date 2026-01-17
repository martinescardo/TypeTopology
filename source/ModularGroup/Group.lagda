Lane Biocini 17 October 2023

𝓜 is a group

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ModularGroup.Group where

open import MLTT.Spartan
open import Groups.Type renaming (_≅_ to _≅𝓖_)
open import UF.Equiv
open import UF.Retracts

open import ModularGroup.Type
open import ModularGroup.Composition
open import ModularGroup.Properties

𝓜-has-monoid-structure : monoid-structure 𝓜
𝓜-has-monoid-structure = _•_ , E

𝓜-is-monoid : monoid-axioms 𝓜 𝓜-has-monoid-structure
𝓜-is-monoid = 𝓜-is-set , (λ x → refl)
            , compose-right-neutral
            , compose-associative

𝓜-has-group-structure : group-structure 𝓜
𝓜-has-group-structure = _•_

𝓜-is-group : group-axioms 𝓜 (_•_)
𝓜-is-group = 𝓜-is-set
           , compose-associative
           , E
           , (λ x → refl)
           , compose-right-neutral
           , 𝓜-invertible

PSL₂ℤ : Group 𝓤₀
PSL₂ℤ = 𝓜 , _•_ , 𝓜-is-group

\end{code}
