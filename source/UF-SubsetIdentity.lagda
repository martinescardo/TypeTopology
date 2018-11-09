Martin Escardo, 5th September 2018.

Univalence gives the usual mathematical notion of equality for the
subsets of a type: two subsets of a type are equal precisely when they
have the same elements, like in ZF(C). And *not* when they are
isomorphic, for any reasonable notion of isomorphism between subsets
of a given type.

A subset of a type X in a universe U is an embedding of some given
type into X, or, equivalently, a map of X into the subtype classifier
Ω U of the universe U (see the module UF-Classifiers).

\begin{code}

open import SpartanMLTT
open import UF-FunExt
open import UF-Univalence

module UF-SubsetIdentity
        (U : Universe)
        (ua : is-univalent U)
        (ua' : is-univalent (U ⁺))
       where

open import UF-Base
open import UF-Subsingletons
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt

fe : funext U U
fe = funext-from-univalence ua

fe' : funext U (U ⁺)
fe' = funext-from-univalence' U (U ⁺) ua ua'

pe : propext U
pe = UA-gives-propext ua

powerset : U ̇ → U ⁺ ̇
powerset X = X → Ω U

_∈_ : {X : U ̇} → X → powerset X → U ̇
x ∈ A = A x holds

_⊆_ : {X : U ̇} → powerset X → powerset X → U ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

⊆-refl : {X : U ̇} (A : powerset X) → A ⊆ A
⊆-refl A x = id

⊆-refl-consequence : {X : U ̇} (A B : powerset X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence {X} A .A refl = ⊆-refl A , ⊆-refl A

subset-extensionality : {X : U ̇} (A B : powerset X)
                     → A ⊆ B → B ⊆ A → A ≡ B
subset-extensionality {X} A B h k = dfunext fe' φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-Σ-≡ (pe (holds-is-prop (A x)) (holds-is-prop (B x)) (h x) (k x) ,
                being-a-prop-is-a-prop fe (holds-is-prop _) (holds-is-prop _))

\end{code}

So univalence gives the usual mathematical notion of equality for
*subsets* of types, despite the fact that it may give a surprising notion
of equality for *types*.
