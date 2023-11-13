Martin Escardo, 3rd September 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Dedekind where

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv

is-Dedekind-finite : 𝓤 ̇ → 𝓤 ̇
is-Dedekind-finite X = (f : X → X) → is-embedding f → is-equiv f

\end{code}

Notice that we replace the conclusion is-equiv f by is-surjection f to
get an equivalent definition, because if an embedding is a surjection
iff it is an equivalence, but this requires assuming propositional
truncations.

Example. The type Ω 𝓤 of propositions is Dedekind finite.

\begin{code}

open import UF.FunExt
open import UF.HiggsInvolutionTheorem
open import UF.Subsingletons
open import UF.SubtypeClassifier

Ω-is-Dedekind-finite : Fun-Ext → Prop-Ext → is-Dedekind-finite (Ω 𝓤)
Ω-is-Dedekind-finite fe pe = autoembeddings-of-Ω-are-equivs fe pe

\end{code}

Example. A weakly connected type (a type that is (1-)connected if it
is inhabited), is Dedekind finite, so, for instance, the circle S¹ is
Dedekind finite.

\begin{code}

open import CantorSchroederBernstein.CSB
open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open import UF.Connected pt

 wconnected-types-are-Dedekind-finite : {X : 𝓤 ̇ }
                                      → is-wconnected X
                                      → is-Dedekind-finite X
 wconnected-types-are-Dedekind-finite =
  CSB-for-connected-types-without-EM.wconnected-types-are-Dedekind-finite pt

\end{code}

TODO. Relate this to the other notions of finiteness.
