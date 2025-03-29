Fredrik Bakke 26–27 March 2025

We formalize a series of properties of dense maps.

- We construct the unique dense image factorization.
- We show compact types are closed under dense covers.
- We give a negative formulation of Lawvere's fixed point theorem leading to a
  Cantor's theorem for dense maps.
.
\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.Density where

open import MLTT.Spartan
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.LeftCancellable
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Every function can be factored essentially uniquely into a dense map followed by
a double negation stable embedding through its "double negation image". We
appeal to a relaxation of the function extensionality axiom: that negations are
propositions.

\begin{code}

is-¬¬-stable-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-¬¬-stable-map {𝓤} {𝓥} {X} {Y} f = each-fiber-of f ¬¬-stable

\begin{code}

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

decidable-maps-are-¬¬-stable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             → (f : X → Y)
                             → is-decidable-map f
                             → is-¬¬-stable-map f
decidable-maps-are-¬¬-stable f d x = ¬¬-stable-if-decidable (fiber f x) (d x)

decidable-left-cancellable-maps-are-embeddings
 : negations-are-props-statement (𝓤 ⊔ 𝓥)
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (f : X → Y)
 → left-cancellable f
 → is-decidable-map f
 → is-embedding f
decidable-left-cancellable-maps-are-embeddings negations-are-props f lc d =
 ¬¬-stable-left-cancellable-maps-are-embeddings negations-are-props f lc
  (decidable-maps-are-¬¬-stable f d)

\end{code}
