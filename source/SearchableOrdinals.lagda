Martin Escardo, December 2012, based on earlier work, circa 2010.

Searchable ordinals via squashed sums (without using the Cantor space).

We can define plenty of searchable sets by transfinitely iterating
squashed sums. These are countable sums with an added limit point at
infinity (see the module SquashedSum).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module SearchableOrdinals (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import SquashedSum fe
open import SearchableTypes
open import TotallySeparated
open import UF-Retracts
open import UF-Embedding
open import DiscreteAndSeparated

fe₀ : funext U₀ U₀
fe₀ = fe U₀ U₀

\end{code}

We use ordinal encodings, or ordinal expressions, that are slightly
different from the traditional "Brouwer ordinals".

\begin{code}

data OE : U₀ ̇ where
 One  : OE
 Add  : OE → OE → OE
 Mul  : OE → OE → OE
 Sum1 : (ℕ → OE) → OE

\end{code}

The empty ordinal is excluded because it is not searchable. It is
merely exhaustible or omniscient (see the module Searchable for a
partial discussion of this). The reason why including the empty
ordinal causes insurmountable problems is discussed in research papers.

The interpretation function is the following, with values on topped
ordinals, where an ordinal is a type equipped with a
subsingleton-valued, well-founded, transitive and extensional relation
(and such a type is automatically a set). "Topped" means that there is
a top element in the order

This version of the function is from 1st July 2018 (the original
version considered only the underlying set of the ordinal and didn't
construct the order as this was work in progress):

\begin{code}

open import Ordinals fe

ord : OE → Ordᵀ
ord      One  = 𝟙º
ord (Add α β) = ord α +º ord β
ord (Mul α β) = ord α ×º  ord β
ord (Sum1 α)  = ∑¹ \(i : ℕ) → ord(α i)

\end{code}

The underlying sets  of such ordinals are searchable:

\begin{code}

sord : (α : OE) → searchable ⟪ ord α ⟫
sord       One = 𝟙-usearchable
sord (Add α β) = +º-usearchable (ord α) (ord β) (sord α) (sord β)
sord (Mul α β) = ×º-usearchable (ord α) (ord β) (sord α) (sord β)
sord (Sum1 α)  = ∑¹-usearchable (ord ∘ α) (λ n → sord (α n))

\end{code}

Completed 20th July 2018:
They are retracts of the Cantor type (ℕ → 𝟚):

\begin{code}

cord : (α : OE) → retract  ⟪ ord α ⟫ of (ℕ → 𝟚)
cord       One = 𝟙-Cantor-retract
cord (Add α β) = +º-Cantor-retract (ord α) (ord β) (cord α) (cord β)
cord (Mul α β) = ×º-Cantor-retract (ord α) (ord β) (cord α) (cord β)
cord (Sum1 α)  = ∑¹-Cantor-retract (ord ∘ α) (λ n → cord (α n))

\end{code}

And hence they are totally separated:

\begin{code}

tsord : (α : OE) → totally-separated ⟪ ord α ⟫
tsord α = retract-totally-separated (cord α) (Cantor-totally-separated fe₀)

\end{code}

Without total separatedness (enough functions into the type 𝟚 of
booleans), searchability wouldn't be an interesting property. It is
not possible to prove total separated directly, because this property
is not closed under Σ, which is used to define +º, ×º and Σ₁, as shown
in the module FailureOfTotalSeparatedness.

Classically, the squashed sum is the ordinal sum plus 1, and we have a
semantics with this interpretation, which gives ordinals with discrete
underlying sets. Moreover, there is a function maps the underlying set
of the discrete version to the underlying set of the above version.

\begin{code}

ord' : OE → Ordᵀ
ord'        One = 𝟙º
ord' (Add α β) = ord' α +º ord' β
ord' (Mul α β) = ord' α ×º  ord' β
ord' (Sum1 α)  = ∑₁ \(i : ℕ) → ord'(α i)

dord' : (α : OE) → discrete ⟪ ord' α ⟫
dord'      One  = 𝟙-udiscrete
dord' (Add α β) = +udiscrete (ord' α) (ord' β) (dord' α) (dord' β)
dord' (Mul α β) = ×udiscrete (ord' α) (ord' β) (dord' α) (dord' β)
dord' (Sum1 α)  = ∑₁-udiscrete (ord' ∘ α) (λ n → dord' (α n))

{- TODO
ord'-ord : (α : OE) → ⟪ ord' α ⟫ → ⟪ ord α ⟫
ord'-ord One = id
ord'-ord (Add α β) = {!!}
ord'-ord (Mul α β) = pair-fun (ord'-ord α) (λ _ → ord'-ord β)
ord'-ord (Sum1 α) = {!!}

ord-embedding : (α : OE) → is-embedding (ord'-ord α)
ord-embedding One = id-is-embedding
ord-embedding (Add α β) = {!!}
ord-embedding (Mul α β) = pair-fun-embedding _ _ (ord-embedding α) (λ _ → ord-embedding β)
ord-embedding (Sum1 α) = {!!}
-}

\end{code}

Brouwer ordinal codes can be mapped to searchable ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal, because sums dominate suprema.

\begin{code}

open import OrdinalCodes

brouwer-to-oe : B → OE
brouwer-to-oe    Z  = One
brouwer-to-oe (S α) = Add One (brouwer-to-oe α)
brouwer-to-oe (L α) = Sum1(λ i → brouwer-to-oe(α i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal ε₀ (because sums dominate suprema):

\begin{code}

ε₀-upper-bound : Ordᵀ
ε₀-upper-bound = ord(brouwer-to-oe B-ε₀)

searchable-ε₀-ub : usearchable ε₀-upper-bound
searchable-ε₀-ub = sord(brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of many people, including Hancock
and Setzer.
