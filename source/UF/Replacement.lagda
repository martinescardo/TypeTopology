Ian Ray, 17th August 2025.

The type theoretic axiom of replacement (reference) is a statement about the
size of the image of a function with certain smallness assumptions made about
the domain and codomain. The nomenclature is derived from the axiom of
replacement from (ZFC) set theory. We will simply call this statement
'type replacement' because it may be assumed or it may be proven depending on
the context.

The statement of type replacement follows:
The image of a map f : A → X, from a small type A to a locally smally type X,
is itself small.

Type replacement is provable in the presence of a certain class of higher
inductive types (HITs). In particular, "The Join Construction" by Egbert Rijke
(https://arxiv.org/abs/1701.07538.) provides a construction that permits a proof
of type replacement in the presence of 'graph quotients'. More conservativly one
can carry out the construction merely with pushouts (in fact one only requires
the join of maps and sequential colimits). This route is activly being explored
in other TypeTopology files.

It is worth noting that the status of type replacement in the hierarchy of HIT
strength is not completely understood (afaik) but it appears to be weaker than
the assumption that pushouts exist. For this reason we feel it is reasonable to
explore type replacement as an explicit assumption and derive variations for
future use.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module UF.Replacement (fe : Fun-Ext)
                      (pt : propositional-truncations-exist)
                       where

open import MLTT.Spartan
open import UF.ImageAndSurjection pt
open import UF.Size

\end{code}

We begin by giving a precise statement of type replacement.

\begin{code}

module _ {𝓤 𝓥  𝓦 : Universe} where

 Replacement : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ̇
 Replacement = {A : 𝓤 ̇ } {X : 𝓦 ̇ } {f : A → X}
             → A is 𝓥 small
             → X is-locally 𝓥 small
             → image f is 𝓥 small

\end{code}

We can also give a variation of this statement when f is surjective.

\begin{code}

 Replacement' : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ̇
 Replacement' = {A : 𝓤 ̇ } {X : 𝓦 ̇ } {f : A → X}
              → A is 𝓥 small
              → X is-locally 𝓥 small
              → is-surjection f
              → X is 𝓥 small

\end{code}

Of course the two statements are inter-derivable.

\begin{code}

 Replacement-to-Replacement' : Replacement → Replacement' 
 Replacement-to-Replacement' = {!!}

\end{code}
