---
title:        Dependently typed tensors
author:       [Stefano Gogioso, Ayberk Tosun]
date-started: 2025-02-19
---

Summary of a discussion (2025-02-13) with Stefano Gogioso on encoding tensors
using dependent types. This observation was made independently by both of us.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module gist.DependentlyTypedTensors (fe : Fun-Ext) where

open import MLTT.Fin
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv

\end{code}

We work in a module parameterized by a type `R`. This can be thought of as the
carrier of a ring, but we are not interested in the ring structure in this gist.

\begin{code}

module Tensor (R : 𝓤₀ ̇ ) where

\end{code}

A vector of length `n` over `R` is a function `Fin n → R`

\begin{code}

 Vector : ℕ → 𝓤₀ ̇
 Vector n = Fin n → R

\end{code}

An `m` by `n` matrix over `R` is a function `Fin m × Fin n → R`. It has `m`
rows and `n` columns.

\begin{code}

 Matrix : ℕ → ℕ → 𝓤₀ ̇
 Matrix m n = (Fin m × Fin n) → R

\end{code}

This readily generalizes to a rank-`r` tensor over `R`.

\begin{code}

 Rank-[_]-Tensor : (r : ℕ) → (Fin r → ℕ) → 𝓤₀ ̇
 Rank-[_]-Tensor r d = ((i : Fin r) → Fin (d i)) → R

\end{code}

Vectors are just rank-1 tensors.

\begin{code}

 vector-is-rank-1-tensor : (n : ℕ) → Vector n ≃ Rank-[ 1 ]-Tensor (λ _ → n)
 vector-is-rank-1-tensor n = s , qinvs-are-equivs s (r , sec , ret)
  where
   s : Vector n → Rank-[ 1 ]-Tensor (λ _ → n)
   s v i = v (i 𝟎)

   r : Rank-[ 1 ]-Tensor (λ _ → n) → Vector n
   r ϑ i = ϑ (λ _ → i)

   sec : r ∘ s ∼ id
   sec = λ _ → refl

   ret : s ∘ r ∼ id
   ret ϑ = dfunext fe †
    where
     † : (i : Fin 1 → Fin n) → s (r ϑ) i ＝ ϑ i
     † i = s (r ϑ) i      ＝⟨refl⟩
           r ϑ (i 𝟎)      ＝⟨refl⟩
           ϑ (λ _ → i 𝟎)  ＝⟨ ‡    ⟩
           ϑ i            ∎
            where
             ‡ : ϑ (λ _ → i 𝟎) ＝ ϑ i
             ‡ = ap ϑ (dfunext fe λ { 𝟎 → refl })

\end{code}

Matrices are rank-2 tensors.

\begin{code}

 _by_ : {X : 𝓥 ̇ } → X → X → Fin 2 → X
 _by_ x y 𝟎 = x
 _by_ x y 𝟏 = y

 matrix-is-rank-2-tensor : (m n : ℕ)
                         → Matrix m n ≃ Rank-[ 2 ]-Tensor (m by n)
 matrix-is-rank-2-tensor m n = s , qinvs-are-equivs s (r , sec , ret)
  where
   s : Matrix m n → Rank-[ 2 ]-Tensor (m by n)
   s φ ν = φ (ν 𝟎 , ν 𝟏)

   doubleton′ : Fin m → Fin n → (k : Fin 2) → Fin ((m by n) k)
   doubleton′ i j 𝟎 = i
   doubleton′ i j 𝟏 = j

   r : Rank-[ 2 ]-Tensor (m by n) → Matrix m n
   r ϑ (i , j) = ϑ (doubleton′ i j)

   sec : r ∘ s ∼ id
   sec = λ _ → refl

   ret : s ∘ r ∼ id
   ret ϑ = dfunext fe †
    where
     † : (s ∘ r) ϑ ∼ id ϑ
     † ν = s (r ϑ) ν                    ＝⟨refl⟩
           r ϑ (ν 𝟎 , ν 𝟏)              ＝⟨refl⟩
           ϑ (doubleton′ (ν 𝟎) (ν 𝟏))   ＝⟨ ‡    ⟩
           ϑ ν                          ∎
            where
             ξ : doubleton′ (ν 𝟎) (ν 𝟏) ∼ ν
             ξ 𝟎 = refl
             ξ 𝟏 = refl

             ‡ = ap ϑ (dfunext fe ξ)

\end{code}

We now generalize tensors as to be able to consider arbitrary index types.
Previously, we had a function `d : Fin r → ℕ`, whose product
`Π i : Fin r , Fin (d i)` gave us the _shape_ of the tensor in consideration.
We now work with a generalized shape function `S : I → 𝓥 ̇`.

\begin{code}

 Shape-[_]-Tensor : {I : 𝓤₀ ̇ } → (I → 𝓤₀ ̇ ) → 𝓤₀ ̇
 Shape-[_]-Tensor {I} S = ((i : I) → S i) → R

\end{code}

The previous notion of `Rank-[ r ]-Tensor d` can now be reconstructed as a
special case.

\begin{code}

 finite-shape : (r : ℕ) (d : Fin r → ℕ)
              → Rank-[ r ]-Tensor d ＝ Shape-[_]-Tensor (Fin ∘ d)
 finite-shape _ _ = refl

\end{code}
