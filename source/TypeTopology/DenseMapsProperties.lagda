Fredrik Bakke 26–27 March 2025

We formalize a series of properties of dense maps.

- We construct the unique double negation image factorization.
- We show compact types are closed under dense covers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.DenseMapsProperties where

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import TypeTopology.CompactTypes
open import TypeTopology.Density
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.LeftCancellable
open import UF.PropTrunc
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Double negation image factorization.

Every function can be factored essentially uniquely into a dense map followed by
a double negation stable embedding through its "double negation image". We only
appeal to a relaxation of the function extensionality axiom: that negations are
propositions.

\begin{code}

is-¬¬-stable-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-¬¬-stable-map {𝓤} {𝓥} {X} {Y} f = each-fiber-of f ¬¬-stable

_∈¬¬-image_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y) → 𝓤 ⊔ 𝓥 ̇
y ∈¬¬-image f = ¬¬ (fiber f y)

being-in-the-¬¬-image-is-prop : negations-are-props-statement (𝓤 ⊔ 𝓥)
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) (f : X → Y)
                              → is-prop (y ∈¬¬-image f)
being-in-the-¬¬-image-is-prop negations-are-props y f = negations-are-props

¬¬-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
¬¬-image f = Σ y ꞉ codomain f , y ∈¬¬-image f

¬¬-restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → ¬¬-image f → Y
¬¬-restriction f (y , _) = y

¬¬-corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 → X → ¬¬-image f
¬¬-corestriction f x = (f x , ¬¬-intro (x , refl))

¬¬-image-factorization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → f ∼ ¬¬-restriction f ∘ ¬¬-corestriction f
¬¬-image-factorization f x = refl

¬¬-corestrictions-are-dense : negations-are-props-statement (𝓤 ⊔ 𝓥)
                            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-dense (¬¬-corestriction f)
¬¬-corestrictions-are-dense negations-are-props f ((y , nnp) , nq) =
  nnp (λ (x , p) → nq (x , to-Σ-＝ (p , negations-are-props _ nnp)))

¬¬-restrictions-are-embeddings : negations-are-props-statement (𝓤 ⊔ 𝓥)
                               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                               → is-embedding (¬¬-restriction f)
¬¬-restrictions-are-embeddings negations-are-props f = pr₁-is-embedding
                                                        (λ y →
                                                         negations-are-props)

¬¬-restrictions-are-left-cancellable : negations-are-props-statement (𝓤 ⊔ 𝓥)
                                     → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     → left-cancellable (¬¬-restriction f)
¬¬-restrictions-are-left-cancellable negations-are-props f =
 embeddings-are-lc (¬¬-restriction f)
  (¬¬-restrictions-are-embeddings negations-are-props f)

¬¬-restrictions-are-¬¬-stable : negations-are-props-statement (𝓤 ⊔ 𝓥)
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-¬¬-stable-map (¬¬-restriction f)
¬¬-restrictions-are-¬¬-stable negations-are-props f y nnip = ((y , a) , refl)
 where
  a : y ∈¬¬-image f
  a np = nnip b
   where
    b : ¬ (fiber (¬¬-restriction f) y)
    b (v , p) = ¬¬-corestrictions-are-dense negations-are-props f c
     where
      c : Σ v ꞉ ¬¬-image f , ¬ (fiber (¬¬-corestriction f) v)
      c = (v , d)
       where
        d : ¬ (fiber (¬¬-corestriction f) v)
        d (x , q) = np (x , (ap (¬¬-restriction f) q ∙ p))

\end{code}

Double negation stability is a form of split support and lets us conclude from
left cancellability that a map is an embedding.

\begin{code}

¬¬-stable-left-cancellable-maps-are-embeddings
 : negations-are-props-statement (𝓤 ⊔ 𝓥)
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (f : X → Y)
 → left-cancellable f
 → is-¬¬-stable-map f
 → is-embedding f
¬¬-stable-left-cancellable-maps-are-embeddings negations-are-props f lc s = f-is-embedding
 where
  ¬¬-corestriction-f-is-split-surjective : (u : ¬¬-image f)
                                         → fiber (¬¬-corestriction f) u
  ¬¬-corestriction-f-is-split-surjective (y , nnp) =
   let
    (x , p) = s y nnp
   in
   ( x , ¬¬-restrictions-are-left-cancellable negations-are-props f p)

  ¬¬-corestriction-f-is-equiv : is-equiv (¬¬-corestriction f)
  ¬¬-corestriction-f-is-equiv =
   lc-split-surjections-are-equivs
    (¬¬-corestriction f)
    (factor-is-lc (¬¬-corestriction f) (¬¬-restriction f) lc)
    (¬¬-corestriction-f-is-split-surjective)

  ¬¬-corestriction-f-is-embedding : is-embedding (¬¬-corestriction f)
  ¬¬-corestriction-f-is-embedding = equivs-are-embeddings
                                     (¬¬-corestriction f)
                                     (¬¬-corestriction-f-is-equiv)

  f-is-embedding : is-embedding f
  f-is-embedding = ∘-is-embedding
                    (¬¬-corestriction-f-is-embedding)
                    (¬¬-restrictions-are-embeddings negations-are-props f)

complemented-maps-are-¬¬-stable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             → (f : X → Y)
                             → is-complemented-map f
                             → is-¬¬-stable-map f
complemented-maps-are-¬¬-stable f d x = ¬¬-stable-if-decidable (fiber f x) (d x)

complemented-left-cancellable-maps-are-embeddings
 : negations-are-props-statement (𝓤 ⊔ 𝓥)
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (f : X → Y)
 → left-cancellable f
 → is-complemented-map f
 → is-embedding f
complemented-left-cancellable-maps-are-embeddings negations-are-props f lc d =
 ¬¬-stable-left-cancellable-maps-are-embeddings negations-are-props f lc
  (complemented-maps-are-¬¬-stable f d)

\end{code}

Compact types are closed under dense covers.

We give a generalization of the fact that compact types are closed under covers
that also avoids function extensionality and propositional truncations.

\begin{code}

dense-map-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  → is-dense f
                  → is-Compact X {𝓦}
                  → is-Compact Y {𝓦}
dense-map-Compact f i c A δ = +functor positive-case negative-case d
 where
  positive-case : Σ (A ∘ f) → Σ A
  positive-case (x , p) = (f x , p)

  negative-case : ¬  Σ (A ∘ f) → ¬ Σ A
  negative-case nf (y , p) = i (y , λ (x , r) → nf (x , transport A (r ⁻¹) p))

  d : is-decidable (Σ (A ∘ f))
  d = c (A ∘ f) (δ ∘ f)

dense-map-Π-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-dense f
                    → is-Π-Compact X {𝓦}
                    → is-Π-Compact Y {𝓦}
dense-map-Π-Compact {𝓤} {𝓥} {𝓦} {X} {Y} f i c A δ = claim
 where
  positive-case : Π (A ∘ f) → Π A
  positive-case g y = Cases (δ y) id negative-positive-case
   where
    negative-positive-case : ¬ A y → A y
    negative-positive-case np =
     𝟘-elim (i (y , λ (x , r) → np (transport A r (g x))))

  negative-case : ¬ Π (A ∘ f) → ¬ Π A
  negative-case nph p = nph (p ∘ f)

  claim : is-decidable (Π A)
  claim = +functor positive-case negative-case (c (A ∘ f) (δ ∘ f))

\end{code}

As a corollary compact types are closed under covers. This proof improves on
the previous by avoiding function extensionality.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt
 open import UF.ImageAndSurjection pt

 surjections-are-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → is-surjection f
                       → is-dense f
 surjections-are-dense f s (y , q) = ∥∥-rec 𝟘-is-prop q (s y)

 surjection-Compact' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-surjection f
                     → is-Compact X {𝓦}
                     → is-Compact Y {𝓦}
 surjection-Compact' f i = dense-map-Compact f (surjections-are-dense f i)

 image-Compact' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-Compact X {𝓦}
                → is-Compact (image f) {𝓦}
 image-Compact' f = surjection-Compact' (corestriction f)
                     (corestrictions-are-surjections f)

 surjection-Π-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-surjection f
                      → is-Π-Compact X {𝓦}
                      → is-Π-Compact Y {𝓦}
 surjection-Π-Compact f i = dense-map-Π-Compact f (surjections-are-dense f i)

 image-Π-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 → is-Π-Compact X {𝓦}
                 → is-Π-Compact (image f) {𝓦}
 image-Π-Compact f c = surjection-Π-Compact (corestriction f)
                        (corestrictions-are-surjections f) c

\end{code}
