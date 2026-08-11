Martin Escardo
15 February 2021, updated September 2023.

In collaboration with Marc Bezem, Thierry Coquand and Peter Dybjer.

Given any large, locally small set, we show that there is a large group.

Here a type is said to be large, relative to a universe 𝓤, if it lives
in the successor 𝓤⁺ and doesn't have an equivalent copy in 𝓤.

Notice that if P is a proposition the unique map P → 𝟙 is an
embedding, but P may be large while 𝟙 is small. Hence it is not the
case in general that for an embedding X → Y, if Y is small then X is
small. This is the case, however, if the embedding has small fibers
(in which case we say that it is small).

Most of the work for the conclusions of this file is done, and
explained, in the module Groups.Free.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Groups.Large
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Groups.Free
open import Groups.Type
open import UF.Sets
open import UF.Size

\end{code}

Given any large, locally small set A, we can construct a large group
with no small copy.

\begin{code}

large-group-with-no-small-copy : (Σ A ꞉ 𝓤 ⁺ ̇ , is-set A
                                              × is-large A
                                              × is-locally-small A)
                               → Σ 𝓕 ꞉ Group (𝓤 ⁺) , ((𝓖 : Group 𝓤) → ¬ (𝓖 ≅ 𝓕))

large-group-with-no-small-copy {𝓤} (A , A-is-set , A-is-large , A-ls) = 𝓕 , γ
 where
  g : good-freely-generated-group-exists A (𝓤 ⁺) 𝓤
  g = Theorem₂[free-groups-of-large-locally-small-types] pt fe pe A A-ls

  open good-freely-generated-group-exists g

  free-group-small-gives-generating-set-small : ⟨ 𝓕 ⟩ is 𝓤 small
                                              → A is 𝓤 small
  free-group-small-gives-generating-set-small =
   size-contravariance η (η-is-small A-is-set)

  γ : (𝓖 : Group 𝓤) → ¬ (𝓖 ≅ 𝓕)
  γ 𝓖 (g , g-is-equiv , g-is-hom) = α
     where
      h : ⟨ 𝓕 ⟩ is 𝓤 small
      h = ⟨ 𝓖 ⟩ , g , g-is-equiv

      α : 𝟘
      α = A-is-large (free-group-small-gives-generating-set-small h)

\end{code}

In the module Ordinals.BuraliForti we instantiate A to the set of ordinals,
which is large and locally small, to construct a large group with no
small copy.

Remarks.

1. What can we choose for the large, locally small set?

 * Our choice is the type of ordinals.

 * One may wonder whether there are simpler choices such as

    (i)   The function type 𝓤 → 𝟚.
    (ii)  The function type 𝓤 → Ω 𝓤.
    (iii) The set truncation of 𝓤.

   The candidate (i) doesn't work in the absence of classical logic,
   because there is a non-constant function 𝓤 → 𝟚 if and only if de
   Morgan Law holds (which is equivalent to excluded middle for
   negative propositions). https://doi.org/10.1016/j.apal.2016.04.010

   The candidates (ii-iii) may work, but so far we haven't succeeded.

 * Another question is whether there is a large, discrete set, as this
   would considerably simplify the construction of the free group. One
   of us conjectures that there isn't, in general, such a set.

2. Notice that if the axiom of choice is available, we don't need to
   use free groups as above, because the axiom of choice is equivalent
   to the statement that any non-empty set has some group
   structure. Although we don't get an explicit group with this
   construction, its existence is enough in order to prove that the
   type of groups in universe 𝓤 is not (canonically) equivalent to the
   type of groups in the next universe 𝓤⁺.
