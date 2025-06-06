Martin Escardo and Tom de Jong 7th - 21st November 2024.

We improve the universe levels of Lemma 14 of [1], which corresponds
to `embedding-retract` from InjectiveTypes/Blackboard.

We use this to remove resizing assumption of Theorem 51 of [1], which
characterizes the algebraically injective types as the retracts of the
algebras of the lifiting monad (also known as the partial-map
classifier monad.

[1] M.H. Escardó. Injective type in univalent mathematics.
    https://doi.org/10.1017/S0960129520000225

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.CharacterizationViaLifting (fe : FunExt) where

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.OverSmallMaps fe
open import MLTT.Spartan
open import UF.Equiv
open import UF.Size
open import UF.Subsingletons

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

We first improve the universe levels of Blackboard.ainjectivity-of-Lifting.

\begin{code}

open import UF.Univalence

module ainjectivity-of-Lifting'
        (𝓣 : Universe)
        (ua : is-univalent 𝓣)
       where

 private
  pe : propext 𝓣
  pe = univalence-gives-propext ua

 open ainjectivity-of-Lifting 𝓣

 open import Lifting.UnivalentWildCategory 𝓣
 open import UF.Retracts

 η-is-small-map : {X : 𝓤 ̇ } → (η ∶ (X → 𝓛 X)) is 𝓣 small-map
 η-is-small-map {𝓤} {X} l = is-defined l ,
                            ≃-sym (η-fiber-same-as-is-defined X pe fe' fe' fe' l)

\end{code}

The following improves the universe levels of Lemma 50 of [1].

\begin{code}

 ainjective-is-retract-of-free-𝓛-algebra' : ({𝓤} 𝓥 {𝓦} : Universe)
                                            (D : 𝓤 ̇ )
                                          → ainjective-type D (𝓣 ⊔ 𝓥) 𝓦
                                          → retract D of (𝓛 D)
 ainjective-is-retract-of-free-𝓛-algebra' {𝓤} 𝓥 D =
  embedding-retract' 𝓥 D (𝓛 D) η
   (η-is-embedding' 𝓤 D ua fe')
   η-is-small-map

 ainjectives-in-terms-of-free-𝓛-algebras'
  : (D : 𝓤 ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X))
 ainjectives-in-terms-of-free-𝓛-algebras' {𝓤} D = a , b
  where
   a : ainjective-type D 𝓣 𝓣 → Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)
   a i = D , ainjective-is-retract-of-free-𝓛-algebra' 𝓣 D i

   b : (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)) → ainjective-type D 𝓣 𝓣
   b (X , r) = retract-of-ainjective D (𝓛 X) (free-𝓛-algebra-ainjective ua X) r

\end{code}

A particular case of interest that arises in practice is the following.

\begin{code}

 ainjectives-in-terms-of-free-𝓛-algebras⁺
  : (D : 𝓣 ⁺ ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ X ꞉ 𝓣 ⁺ ̇ , retract D of (𝓛 X))
 ainjectives-in-terms-of-free-𝓛-algebras⁺
  = ainjectives-in-terms-of-free-𝓛-algebras'

 _ : {X : 𝓣 ⁺ ̇ } → type-of (𝓛 X) ＝ 𝓣 ⁺ ̇
 _ = refl

\end{code}

The following removes the resizing assumption of Theorem 51 of [1].

\begin{code}

 ainjectives-in-terms-of-𝓛-algebras
  : (D : 𝓤 ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ A ꞉ 𝓣 ⁺ ⊔ 𝓤 ̇ , 𝓛-alg A × retract D of A)
 ainjectives-in-terms-of-𝓛-algebras {𝓤} D = a , b
  where
   a : ainjective-type D 𝓣 𝓣 → (Σ A ꞉ 𝓣 ⁺ ⊔ 𝓤 ̇ , 𝓛-alg A × retract D of A)
   a i = 𝓛 D ,
         𝓛-algebra-gives-alg (free-𝓛-algebra ua D) ,
         ainjective-is-retract-of-free-𝓛-algebra' 𝓣 D i

   b : (Σ A ꞉ 𝓣 ⁺ ⊔ 𝓤 ̇ , 𝓛-alg A × retract D of A) → ainjective-type D 𝓣 𝓣
   b (A , α , ρ) = retract-of-ainjective D A (𝓛-alg-ainjective pe A α) ρ

\end{code}

Particular case of interest:

\begin{code}

 ainjectives-in-terms-of-𝓛-algebras⁺
  : (D : 𝓣 ⁺ ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ A ꞉ 𝓣 ⁺ ̇ , 𝓛-alg A × retract D of A)
 ainjectives-in-terms-of-𝓛-algebras⁺ = ainjectives-in-terms-of-𝓛-algebras

\end{code}
