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

sord : (α : OE) → usearchable(ord α)
sord       One = 𝟙-usearchable
sord (Add α β) = +usearchable (ord α) (ord β) (sord α) (sord β)
sord (Mul α β) = ×usearchable (ord α) (ord β) (sord α) (sord β) 
sord (Sum1 α)  = ∑¹-usearchable (ord ∘ α) (λ n → sord (α n))

\end{code}

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

dord' : (α : OE) → udiscrete(ord' α)
dord'      One  = 𝟙-udiscrete
dord' (Add α β) = +udiscrete (ord' α) (ord' β) (dord' α) (dord' β)
dord' (Mul α β) = ×udiscrete (ord' α) (ord' β) (dord' α) (dord' β) 
dord' (Sum1 α)  = ∑₁-udiscrete (ord' ∘ α) (λ n → dord' (α n))

{-
ord'-ord : (α : OE) → ⟪ ord' α ⟫ → ⟪ ord α ⟫
ord'-ord One = id
ord'-ord (Add α β) c = {!!}
ord'-ord (Mul α β) = {!!}
ord'-ord (Sum-plus-One α) = {!!} 
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
