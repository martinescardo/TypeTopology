Ian Ray, 17th August 2025.

The type theoretic axiom of replacement (section 24.5 of Introduction to
Homotopy Type Theory by Egbert Rijke:
https://ulrikbuchholtz.dk/hott1920/hott-intro.pdf)
is a statement about the size of the image of a function when certain smallness
assumptions are imposed on the domain and codomain. The nomenclature is derived
from the set theoretic axiom of replacement, where the set vs class distinction
provides a notion of size. In type theory, this statement may be assumed or
proven depending on the context. We also mention that the file UF/Size.lagda
defines 'set replacement' which restricts type replacement to those maps whose
codomain is a set (in the sense of univalent foundations). We will drop the word
'axiom' and write 'type replacement', or simply 'replacement' when there is no 
risk of confusion with set replacement.

The statement of type replacement is as follows:
The image of a map f : A → X, from a small type A to a locally small type X, is
itself small.

Note: some authors use the term 'essentially small' for what the TypeTopology
library refers to as simply 'small'. Additionally, we often wish to consider
size relative to an explicit universe.

Type replacement is provable in the presence of a certain class of higher
inductive types (HITs). In particular, "The Join Construction" by Egbert Rijke
(https://arxiv.org/abs/1701.07538.) uses 'graph quotients' to give an
alternative construction of the image where type replacement can be proven.
More conservatively one may carry out this construction merely with pushouts
(in fact, one only requires the join of maps and sequential colimits, which are
instances of pushouts). This route is actively being explored in other
TypeTopology files.

It is worth noting that the status of type replacement's strength relative to
the strength of adding certain HITs is not completely understood, but it
appears to be weaker than the assumption that pushouts exist (this observation
will follow from a forthcoming write up by Reid Barton). In light of this, it
is reasonable to explore type replacement and use it as an independent
assumption when neccesary.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module UF.Replacement (pt : propositional-truncations-exist)
                       where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.Size
open import UF.SmallnessProperties

open propositional-truncations-exist pt

\end{code}

We begin by giving a precise statement of type replacement.

\begin{code}

module _ {𝓥 : Universe} where

 Replacement : {𝓤 𝓦 : Universe} → (𝓥 ⊔ 𝓤 ⊔ 𝓦)⁺ ̇
 Replacement {𝓤} {𝓦} = {A : 𝓤 ̇ } {X : 𝓦 ̇ } (f : A → X)
                     → A is 𝓥 small
                     → X is-locally 𝓥 small
                     → image f is 𝓥 small

\end{code}

We can also give a variation of this statement when f is surjective.

\begin{code}

 Replacement' : {𝓤 𝓦 : Universe} → (𝓥 ⊔ 𝓤 ⊔ 𝓦)⁺ ̇
 Replacement' {𝓤} {𝓦} = {A : 𝓤 ̇ } {X : 𝓦 ̇ } (f : A → X)
                      → A is 𝓥 small
                      → X is-locally 𝓥 small
                      → is-surjection f
                      → X is 𝓥 small

\end{code}

Of course the two statements are inter-derivable.

\begin{code}

 Replacement-to-Replacement' : {𝓤 𝓦 : Universe}
                             → Replacement {𝓤} {𝓦} → Replacement' {𝓤} {𝓦}
 Replacement-to-Replacement' 𝓡 {_} {X} f A-small X-loc-small f-surj
  = smallness-closed-under-≃ I II
  where
   I : image f is 𝓥 small
   I = 𝓡 f A-small X-loc-small
   II : image f ≃ X
   II = surjection-≃-image f f-surj

 Replacement'-to-Replacement : {𝓤 𝓦 : Universe}
                             → Replacement' {𝓤} {𝓤 ⊔ 𝓦} → Replacement {𝓤} {𝓦}
 Replacement'-to-Replacement 𝓡' {A} {X} f A-small X-loc-small
  = 𝓡' (corestriction f) A-small I II
  where
   I : image f is-locally 𝓥 small
   I = subtype-is-locally-small' X-loc-small (λ - → ∥∥-is-prop)
   II : is-surjection (corestriction f)
   II = corestrictions-are-surjections f

\end{code}
