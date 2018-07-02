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
open import SquashedSum (fe)
open import SearchableTypes

\end{code}

We use ordinal encodings, or ordinal expressions, that are slightly
different from the traditional "Brouwer ordinals".

\begin{code}

data OE : U₀ ̇ where
  One           : OE 
  Add           : OE → OE → OE
  Mul           : OE → OE → OE
  Sum-plus-One  : (ℕ → OE) → OE 

\end{code}

The above are searchable-ordinal codes or expressions.

(The empty ordinal is excluded because it is not searchable. It is
merely exhaustible or omniscient (see the module Searchable for a
partial discussion of this). The reason why including the empty
ordinal causes insurmountable problems is discussed in research papers.)

The decoding function (or semantic interpretation, or evaluation
function) is this, with valued on topped ordinals, where an ordinal is
a type equipped with a proposition-valued, well-founded, transitive
and extensional relation (and such a type is automatically a
set). "Topped" means that there is a top element in the order

This version of the function is from 1st July 2018 (the original
version considered only the underlying set of the ordinal and didn't
construct the order as this was work in progress):

\begin{code}

open import Ordinals fe

ord : OE → TOrd
ord           One    = 𝟙º
ord      (Add α β)   = ord α +º ord β 
ord      (Mul α β)   = ord α ×º  ord β 
ord (Sum-plus-One α) = ∑¹ \(i : ℕ) → ord(α i)

usearchable-ord : (α : OE) → usearchable(ord α)
usearchable-ord           One  = 𝟙-usearchable
usearchable-ord      (Add α β) = +usearchable (ord α) (ord β)
                                   (usearchable-ord α)
                                   (usearchable-ord β)
usearchable-ord      (Mul α β) = ×usearchable (ord α) (ord β)
                                   (usearchable-ord α)
                                   (usearchable-ord β) 
usearchable-ord (Sum-plus-One α) = ∑¹-usearchable
                                       (λ i → ord (α i))
                                       (λ i → usearchable-ord(α i))

\end{code}

Classically, the squashed sum is the ordinal sum plus 1, and we have a
semantics with this interpretation, which gives ordinals with discrete
underlying sets. Moreover, there a function maps the underlying set of
the discrete version to the underlying set of the above version.

\begin{code}

{- TODO. Requires more work in other modules.
ord' : OE → TOrd
ord'           One    = 𝟙º
ord'      (Add α β)   = ord' α +º ord' β 
ord'      (Mul α β)   = ord' α ×º  ord' β 
ord' (Sum-plus-One α) = {!!} -- ∑₁ (λ i → ord'(α i')

udiscrete-ord' : (α : OE) → udiscrete(ord' α)
udiscrete-ord'           One  = 𝟙-udiscrete
udiscrete-ord'      (Add α β) = +udiscrete (ord' α) (ord' β) (udiscrete-ord' α) (udiscrete-ord' β)
udiscrete-ord'      (Mul α β) = ×udiscrete (ord' α) (ord' β) (udiscrete-ord' α) (udiscrete-ord' β) 
udiscrete-ord' (Sum-plus-One α) = {!!} -- ∑₁-udiscrete (λ i → ord (α i)) (λ i → udiscrete-ord'(α i))

ord'-ord : (α : OE) → ⟪ ord' α ⟫ → ⟪ ord α ⟫
ord'-ord One = id
ord'-ord (Add α β) c = {!!}
ord'-ord (Mul α β) = {!!}
ord'-ord (Sum-plus-One α) = {!!} 
-}

\end{code}

Brouwer ordinal codes can be mapped to searchable ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal.

\begin{code}

open import OrdinalCodes

brouwer-to-oe : B → OE
brouwer-to-oe    Z  = One
brouwer-to-oe (S α) = Add One (brouwer-to-oe α)
brouwer-to-oe (L α) = Sum-plus-One(λ i → brouwer-to-oe(α i))

\end{code}

Relatively "small" example: a type which amounts to the ordinal ε₀ in set theory:

\begin{code}

ε₀-ordinal : TOrd
ε₀-ordinal = ord(brouwer-to-oe B-ε₀)

searchable-ε₀-ordinal : usearchable ε₀-ordinal
searchable-ε₀-ordinal = usearchable-ord(brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of many people, including Hancock
and Setzer.

To do: prove that these searchable types are really ordinals in the
sense of the paper "Infinite sets that satisfy the principle of
omniscience in all varieties of constructive mathematics".

That is: they are linearly ordered (in a suitable constructive sense),
and every decidable inhabited subset as a least element (found using
the selection function that exists by searchability). This is proved
in that paper for subsets of the Cantor space. This file constructs
the same ordinals but without having them inside the Cantor space, but
the proof (omitted here for the moment) is essentially the same.
