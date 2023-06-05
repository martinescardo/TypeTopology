Martin Escardo, 19th March 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Fin.Omega where

open import UF.Subsingletons renaming (⊤Ω to ⊤)

open import Fin.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.Embeddings
open import UF.FunExt
open import UF.Subsingletons-FunExt

having-three-distinct-points-covariant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                       → X ↪ Y
                                       → has-three-distinct-points X
                                       → has-three-distinct-points Y
having-three-distinct-points-covariant (f , f-is-emb) ((x , y , z) , u , v , w) = γ
 where
  l : left-cancellable f
  l = embeddings-are-lc f f-is-emb

  γ : has-three-distinct-points (codomain f)
  γ = ((f x , f y , f z) , (λ p → u (l p)) , (λ q → v (l q)) , (λ r → w (l r)))

finite-type-with-three-distict-points : (k : ℕ)
                                      → k ≥ 3
                                      → has-three-distinct-points (Fin k)
finite-type-with-three-distict-points (succ (succ (succ k))) * =
 ((𝟎 , 𝟏 , 𝟐) , +disjoint' , (λ a → +disjoint' (inl-lc a)) , +disjoint)

finite-subsets-of-Ω-have-at-most-2-elements : funext 𝓤 𝓤
                                            → propext 𝓤
                                            → (k : ℕ)
                                            → Fin k ↪ Ω 𝓤
                                            → k ≤ 2
finite-subsets-of-Ω-have-at-most-2-elements {𝓤} fe pe k e = γ
 where
  α : k ≥ 3 → has-three-distinct-points (Ω 𝓤)
  α g = having-three-distinct-points-covariant e (finite-type-with-three-distict-points k g)

  β : ¬ (k ≥ 3)
  β = contrapositive α (no-three-distinct-propositions fe pe)

  γ : k ≤ 2
  γ = not-less-bigger-or-equal k 2 β

\end{code}
