Ian Ray, 17th August 2025.

The type theoretic axiom of replacement (see section 2.19 of Symmetry:
chrome-extension://efaidnbmnnnibpcajpcglclefindmkaj/https://unimath.github.io/SymmetryBook/book.pdf) is a statement about the size of the image of a function when certain
smallness assumptions are made about the domain and codomain. The nomenclature
is derived from the axiom of replacement from axiomatic set theory. In type
theory, this statement may be assumed or proven depending on the context. Thus,
we will call it 'type replacement' or simply 'replacement' (when there is no
risk of confusion with set replacement).

The statement of type replacement is as follows:
The image of a map f : A → X, from a small type A to a locally small type X, is
itself small.

Type replacement is provable in the presence of a certain class of higher
inductive types (HITs). In particular, "The Join Construction" by Egbert Rijke
(https://arxiv.org/abs/1701.07538.) provides a construction that allows a proof
of type replacement in the presence of 'graph quotients'. More conservativly one
may carry out this construction merely with pushouts (in fact, one only requires
the join of maps and sequential colimits). This route is actively being explored
in other TypeTopology files.

It is worth noting that the status of type replacement in the hierarchy of HIT
strength is not completely understood (afaik), but it appears to be weaker than
the assumption that pushouts exist. For this reason, we feel it is reasonable to
explore type replacement as an explicit assumption and derive variations for
future use.

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

\end{code}

We begin by giving a precise statement of type replacement.

\begin{code}

module _ {𝓥 : Universe} where

 Replacement : {𝓤 𝓦 : Universe} → (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ̇
 Replacement {𝓤} {𝓦} = {A : 𝓤 ̇ } {X : 𝓦 ̇ } (f : A → X)
             → A is 𝓥 small
             → X is-locally 𝓥 small
             → image f is 𝓥 small

\end{code}

We can also give a variation of this statement when f is surjective.

\begin{code}

 Replacement' : {𝓤 𝓦 : Universe} → (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺) ̇
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

 open propositional-truncations-exist pt

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
