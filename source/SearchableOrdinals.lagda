Martin Escardo, December 2012, based on earlier work, circa 2010.

Searchable ordinals via squashed sums (without using the Cantor space). 

We can define plenty of searchable sets by transfinitely iterating
squashed sums. These are countable sums with an added limit point at
infinity (see the module SquashedSum).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} 

open import UF

module SearchableOrdinals (fe : ∀ U V → FunExt U V) where

open import AlternativeCoproduct
open import Naturals
open import SquashedSum (fe)
open import SearchableTypes

\end{code}

We use ordinal encodings that are slightly different from those
considered in the module "Ordinals" (Church & Brouwer):

\begin{code}

data SO : U₀ ̇ where
  One         : SO 
  Add         : SO → SO → SO
  Mul         : SO → SO → SO
  SumPlusOne  : (ℕ → SO) → SO 

\end{code}

The above are searchable ordinals codes. 

(The empty ordinal is excluded because it is not searchable. It is
merely exhaustible or omniscient (see the module Searchable for a
partial discussion of this). The reason why including the empty
ordinal causes insurmountable problems is discussed in research papers.)

The decoding function (or semantic interpretation, or evaluation
function) is this:

\begin{code}

ordinal : SO → U₀ ̇
ordinal           One  = 𝟙
ordinal      (Add α β) = ordinal α +' ordinal β 
ordinal      (Mul α β) = ordinal α ×  ordinal β 
ordinal (SumPlusOne α) = Σ¹ \(i : ℕ) → ordinal(α i)

\end{code}

All sets in the image of the function ordinal are searchable:

\begin{code}

searchable-ordinals : (α : SO) → searchable(ordinal α)
searchable-ordinals           One  = one-searchable
searchable-ordinals      (Add α β) = binary-sums-preserve-searchability(searchable-ordinals α)(searchable-ordinals β)
searchable-ordinals      (Mul α β) = binary-Tychonoff(searchable-ordinals α)(searchable-ordinals β)
searchable-ordinals (SumPlusOne α) = squashed-sum-searchable (λ i → searchable-ordinals(α i))

\end{code}

Classically, the squashed sum is the ordinal sum plus 1. 

Brouwer ordinal codes can be mapped to searchable ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal.

\begin{code}

open import OrdinalCodes

brouwer-to-searchable-code : B → SO
brouwer-to-searchable-code    Z  = One
brouwer-to-searchable-code (S α) = Add One (brouwer-to-searchable-code α)
brouwer-to-searchable-code (L α) = SumPlusOne(λ i → brouwer-to-searchable-code(α i))

\end{code}

Relatively "small" example: a type which amounts to the ordinal ε₀ in set theory:

\begin{code}

ε₀-ordinal : U₀ ̇
ε₀-ordinal = ordinal(brouwer-to-searchable-code B-ε₀)

searchable-ε₀-ordinal : searchable ε₀-ordinal
searchable-ε₀-ordinal = searchable-ordinals(brouwer-to-searchable-code B-ε₀)

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
