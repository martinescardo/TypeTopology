Martin Escardo, 21th December 2020 - 18th February 2021.

In collaboration with  Marc Bezem, Thierry Coquand, Peter Dybjer.

The Burali-Forti argument in HoTT/UF with applications to the type of groups in a universe
------------------------------------------------------------------------------------------

Abstract. We use the Burali-Forti argument to show that, in HoTT/UF,
the embedding

    𝓤 → 𝓤⁺.

of a universe 𝓤 into its successor 𝓤⁺ is not equivalence.

Similarly, the embedding hSet 𝓤 → hSet 𝓤⁺ of the type of sets of 𝓤
into that of 𝓤⁺ in not an equivalence either.  We also establish this
for the types of magmas, monoids and groups, where the case of groups
requires considerable more work (invoked here but performed in the
modules FreeGroup.lagda and FreeGroupOfLargeLocallySmallSet.lagda).

We work with ordinals as defined in the HoTT book for that purpose.
https://homotopytypetheory.org/book/

Introduction
------------

Univalence is used three times (at least):

    1. to know that the type of ordinals is a 0-type and hence all
       ordinals in a universe form an ordinal in the next universe,

    2. to develop the Burali-Forti argument that no ordinal in the
       universe 𝓤 is equivalent to the ordinal of ordinals in 𝓤.

    3. to resize down the values of the order relation of the ordinal
       of ordinals, to conclude that the ordinal of ordinals is large.

There are also a number of uses of univalence via functional and
propositional extensionality.

Propositional resizing is not needed, thanks to (3).

An ordinal in a universe 𝓤 is a type X : 𝓤 equipped with a relation

    _≺_ : X → X → 𝓤

required to be

    1. proposition-valued,

    2. transitive,

    3. extensional (any two points with same lower set are the same),

    4. well founded (every element is accessible, or, equivalently,
       the principle of transfinite induction holds).

The HoTT book additionally requires X to be a set, but this follows
automatically from the above requirements for the order.

We denote by

    Ordinal 𝓤

the type of ordinals in a universe 𝓤.

The underlying type of an ordinal α is denoted by ⟨ α ⟩ and its order
relation is denoted by _≺⟨ α ⟩_.

Equivalence of ordinals,

    _≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥,

means that that there is an equivalence of the underlying types that
preserves and reflects order.

For ordinals α and β in the *same* universe, their identity type α ＝ β
is canonically equivalent to the ordinal-equivalence type α ≃ₒ β,
by univalence.

The lower set of a point x : ⟨ α ⟩ is written α ↓ x, and is itself an
ordinal under the inherited order. The ordinals in a universe 𝓤 form
an ordinal in the successor universe 𝓤⁺, denoted by

    OrdinalOfOrdinals 𝓤 : Ordinal 𝓤⁺.

Its order relation is denoted by _⊲_ and is defined by

    α ⊲ β = Σ b ꞉ ⟨ β ⟩ , α ＝ (β ↓ b).

This order has type

    _⊲_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤⁺,

as required for it to make the type Ordinal 𝓤 into an ordinal in the
next universe.

But, by univalence, it is pointwise equivalent to the "resized down"
order

    _⊲⁻_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤

defined by

    α ⊲⁻ β = Σ b ꞉ ⟨ β ⟩ , α ≃₀ (β ↓ b).

The existence of such a resized-down order is crucial for the
corollaries of Burali-Forti, but not for Burali-Forti itself.

Agda formulation of the Burali-Forti argument and its corollaries
-----------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

\end{code}

As discussed above, we assume univalence as a hypothesis:

\begin{code}

open import UF.Univalence

module Ordinals.BuraliForti
       (ua : Univalence)
       where

open import UF.Base
open import UF.Subsingletons
open import UF.Retracts
open import UF.Equiv hiding (_≅_)
open import UF.EquivalenceExamples
open import UF.UniverseEmbedding
open import UF.UA-FunExt
open import UF.FunExt
open import UF.Size

private

 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' = Univalence-gives-Fun-Ext ua

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import MLTT.Spartan

open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.WellOrderTransport

\end{code}

Our version of Burali-Forti says that there is no ordinal in the
universe 𝓤 equivalent to the ordinal of all ordinals in the universe 𝓤.

\begin{code}

Burali-Forti : ¬ (Σ α ꞉ Ordinal 𝓤 , α ≃ₒ OO 𝓤)
Burali-Forti {𝓤} (α , 𝕗) = γ
 where
  a : OO 𝓤 ≃ₒ α
  a = ≃ₒ-sym α (OO 𝓤) 𝕗

  b : α ≃ₒ (OO 𝓤 ↓ α)
  b = ordinals-in-OO-are-lowersets-of-OO α

  c : OO 𝓤 ≃ₒ (OO 𝓤 ↓ α)
  c = ≃ₒ-trans (OO 𝓤) α (OO 𝓤 ↓ α) a b

  d : OO 𝓤 ＝ (OO 𝓤 ↓ α)
  d = eqtoidₒ (ua (𝓤 ⁺)) fe' (OO 𝓤) (OO 𝓤 ↓ α) c

  e : OO 𝓤 ⊲ OO 𝓤
  e = α , d

  γ : 𝟘
  γ = irreflexive _⊲_ (OO 𝓤) (⊲-is-well-founded (OO 𝓤)) e

\end{code}

Some corollaries follow.

The main work is in the first one, which says that the type of all
ordinals is large, happens in the function transfer-structure, which
is developed in the module OrdinalsWellOrderTransport, where the
difficulties are explained.

As discussed above, the type OO 𝓤 of ordinals in the
universe 𝓤 lives in the next universe 𝓤⁺. We say that a type in the
universe 𝓤⁺ is small if it is equivalent to some type in 𝓤, and large
otherwise. This is defined in the module UF.Size.

Our first corollary of Burali-Forti is that the type of ordinals is
large, as expected:

\begin{code}

the-type-of-ordinals-is-large : is-large (Ordinal 𝓤)
the-type-of-ordinals-is-large {𝓤} (X , 𝕗) = γ
 where
  δ : Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ OO 𝓤
  δ = transfer-structure fe {𝓤} {𝓤 ⁺} X (OO 𝓤)
       𝕗 (_⊲⁻_ , ⊲-is-equivalent-to-⊲⁻)

  γ : 𝟘
  γ = Burali-Forti ((X , pr₁ δ) , pr₂ δ)

\end{code}

It is crucial in the above proof, in order to be able to transfer the
ordinal structure of the ordinal of ordinals to the type X along the
hypothetical equivalence 𝕗 : X ≃ Ordinal 𝓤, that the order _⊲_ has a
resized-down version _⊲⁻_ , as mentioned above.

By a *universe embedding* we mean a map

    f : 𝓤 → 𝓥

of universes such that

    f X ≃ X.

Of course, any two universe embeddings are equal, by univalence, so
that there is at most one universe embedding.

Moreover, universe embeddings are automatically type embeddings
(meaning that they have subsingleton fibers), as shown in the module
UF.UniverseEmbeddings.

So the following says that the universe 𝓤⁺ is strictly larger than the
universe 𝓤:

\begin{code}

successive-universe-embeddings-dont-have-sections : (f : 𝓤 ̇ → 𝓤 ⁺ ̇ )
                                                  → is-universe-embedding f
                                                  → ¬ has-section f
successive-universe-embeddings-dont-have-sections {𝓤} f i (s , η) = γ
 where
  X : 𝓤 ̇
  X = s (Ordinal 𝓤)

  p : f X ＝ Ordinal 𝓤
  p = η (Ordinal 𝓤)

  e : X ≃ Ordinal 𝓤
  e = transport (X ≃_) p (≃-sym (i X))

  γ : 𝟘
  γ = the-type-of-ordinals-is-large (X , e)


successive-universe-embeddings-are-not-equivs : (f : 𝓤 ̇ → 𝓤 ⁺ ̇ )
                                              → is-universe-embedding f
                                              → ¬ is-equiv f
successive-universe-embeddings-are-not-equivs f i j =
  successive-universe-embeddings-dont-have-sections f i
   (equivs-have-sections f j)

\end{code}

In particular, we have the following, where

  Lift {𝓤} (𝓤 ⁺) : 𝓤 → 𝓤⁺

is the canonical embedding of the universe 𝓤 into the successor
universe 𝓤⁺, defined in the module UF.UniverseEmbedding:

\begin{code}

Lift-doesnt-have-section : ¬ has-section (Lift {𝓤} (𝓤 ⁺))
Lift-doesnt-have-section {𝓤} h =
  successive-universe-embeddings-dont-have-sections
   (Lift (𝓤 ⁺)) (λ X → Lift-is-universe-embedding (𝓤 ⁺) X) h

Lift-is-not-equiv : ¬ is-equiv (Lift {𝓤} (𝓤 ⁺))
Lift-is-not-equiv {𝓤} e = Lift-doesnt-have-section
                           (equivs-have-sections (Lift (𝓤 ⁺)) e)
\end{code}

For a universe 𝓤, we define the type

    hSet 𝓤 : 𝓤⁺

of sets in the universe 𝓤 by

    hSet 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A.

By an *hSet embedding* we mean a map

    f : hSet 𝓤 → hSet 𝓥

such that the underlying type of f 𝕏 is equivalent to the
underlying type of 𝕏, that is,

    pr₁ (f 𝕏) ≃ pr₁ 𝕏,

for all 𝕏 : hSet 𝓤.

Any hSet-embedding is a type embedding, and any two hSet-embeddings
are equal by univalence. The map

    Lift-hSet {𝓤} 𝓥 : hSet 𝓤 → hSet (𝓤 ⊔ 𝓥)

is the unique hSet embedding, given by

    Lift-hSet 𝓥 (X , i) = Lift 𝓥 X , Lift-is-set X i)

where

    Lift-is-set X i : is-set (Lift 𝓥 X)

is derived from the fact that Lift 𝓥 X ≃ X using i : is-set X.

\begin{code}

open import UF.Sets

Lift-hSet-doesnt-have-section : ¬ has-section (Lift-hSet {𝓤} (𝓤 ⁺))
Lift-hSet-doesnt-have-section {𝓤} (s , η) = γ
 where
  𝕐 : hSet (𝓤 ⁺)
  𝕐 = (Ordinal 𝓤 , (the-type-of-ordinals-is-a-set (ua 𝓤) fe'))

  𝕏 : hSet 𝓤
  𝕏 = s 𝕐

  X : 𝓤 ̇
  X = pr₁ 𝕏

  have : (Lift (𝓤 ⁺) X , _) ＝ 𝕐
  have = η 𝕐

  p : Lift (𝓤 ⁺) X ＝ Ordinal 𝓤
  p = ap pr₁ (η 𝕐)

  d : X ≃ Lift (𝓤 ⁺) X
  d = ≃-sym (Lift-is-universe-embedding (𝓤 ⁺) X)

  e : X ≃ Ordinal 𝓤
  e = transport (X ≃_) p d

  γ : 𝟘
  γ = the-type-of-ordinals-is-large (X , e)

\end{code}

Finally, the following says that the type of sets in 𝓤⁺ is strictly
larger than that of sets in 𝓤, as we wanted to show:

\begin{code}

Lift-hSet-is-not-equiv : ¬ is-equiv (Lift-hSet {𝓤} (𝓤 ⁺))
Lift-hSet-is-not-equiv {𝓤} e = Lift-hSet-doesnt-have-section
                                (equivs-have-sections (Lift-hSet (𝓤 ⁺)) e)
\end{code}

This doesn't show that ¬ (hSet 𝓤 ≃ hSet 𝓤⁺), as in principle there may
be an equivalence that is not an hSet embedding in the sense defined
above, which we leave as an open problem. Notice that excluded middle,
which is not assumed but is consistent, implies that there is an
automorphism of hSet 𝓤 that swaps the empty set 𝟘 and the one-point
set 𝟙 and leaves all the other sets unchanged, so that potentially
there are automorphisms of hSet 𝓤 that are not hSet embeddings. We
don't know whether such a rogue equivalence hSet 𝓤 ≃ hSet 𝓤⁺ exists,
but this shouldn't be the case, of course.

Similarly, the above also doesn't show that ¬ (𝓤 ≃ 𝓤⁺), but we know
that this is the case by a different argument, which generalizes
Thierry Coquand's "paradox of trees", developed in the module
LawvereFPT.

We also wish to know that e.g. the types of groups in the universes 𝓤
and 𝓤⁺ are not equivalent.

Marc Bezem conjectures that ¬ (Σ A : 𝓤 ̇ , A ≃ ∥ 𝓤 ̇ ∥₀), that is, there
is no type in 𝓤 equivalent to the set truncation of 𝓤.

Added 18th January 2021. The following generalizes
Lift-hSet-is-not-equiv.

In the following, A generalizes is-set, and A-lifts generalizes the
fact that the lift of a set is a set.

\begin{code}

module _ (A : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ )
         (A-lifts : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } → A X → A (Lift 𝓥 X))
         (type-of-ordinals-is-A : {𝓤 : Universe} → A (Ordinal 𝓤))
       where

 𝓐 : (𝓤 : Universe) → 𝓤 ⁺ ̇
 𝓐 𝓤 = Σ X ꞉ 𝓤 ̇ , A X

 Lift-𝓐 : ∀ {𝓤} 𝓥 → 𝓐 𝓤 → 𝓐 (𝓤 ⊔ 𝓥)
 Lift-𝓐 {𝓤} 𝓥 (X , a) = Lift 𝓥 X , A-lifts 𝓥 a

 Lift-𝓐-doesnt-have-section : ¬ has-section (Lift-𝓐 {𝓤} (𝓤 ⁺))
 Lift-𝓐-doesnt-have-section {𝓤} (s , η) = γ
  where
   𝕐 : 𝓐 (𝓤 ⁺)
   𝕐 = (Ordinal 𝓤 , type-of-ordinals-is-A)

   𝕏 : 𝓐 𝓤
   𝕏 = s 𝕐

   X : 𝓤 ̇
   X = pr₁ 𝕏

   have : (Lift (𝓤 ⁺) X , _) ＝ 𝕐
   have = η 𝕐

   p : Lift (𝓤 ⁺) X ＝ Ordinal 𝓤
   p = ap pr₁ (η 𝕐)

   d : X ≃ Lift (𝓤 ⁺) X
   d = ≃-sym (Lift-is-universe-embedding (𝓤 ⁺) X)

   e : X ≃ Ordinal 𝓤
   e = transport (X ≃_) p d

   γ : 𝟘
   γ = the-type-of-ordinals-is-large (X , e)

 Lift-𝓐-is-not-equiv : ¬ is-equiv (Lift-𝓐 {𝓤} (𝓤 ⁺))
 Lift-𝓐-is-not-equiv {𝓤} e = Lift-𝓐-doesnt-have-section
                               (equivs-have-sections (Lift-𝓐 (𝓤 ⁺)) e)
\end{code}

Examples of the above situation include hSets, pointed types,
∞-magmas, magmas and monoids:

\begin{code}

module examples where

\end{code}

hSet again:

\begin{code}

 Lift-hSet-is-not-equiv-bis : ¬ is-equiv (Lift-hSet {𝓤} (𝓤 ⁺))
 Lift-hSet-is-not-equiv-bis {𝓤} = Lift-𝓐-is-not-equiv
                                    is-set
                                    (λ 𝓥 {X} → Lift-is-set 𝓥 X)
                                    (the-type-of-ordinals-is-a-set (ua _) fe')
\end{code}

Pointed types:

\begin{code}

 PointedType : (𝓤 : Universe) → 𝓤 ⁺ ̇
 PointedType 𝓤 = Σ X ꞉ 𝓤 ̇ , X

 Lift-PointedType : ∀ {𝓤} 𝓥 → PointedType 𝓤 → PointedType (𝓤 ⊔ 𝓥)
 Lift-PointedType {𝓤} 𝓥 (X , x) = Lift 𝓥 X , lift 𝓥 x

\end{code}

In the following, A is the identity function, and to prove that the
ordinal or ordinals is pointed, we choose the ordinal zero:

\begin{code}

 Lift-PointedType-is-not-equiv : ¬ is-equiv (Lift-PointedType {𝓤} (𝓤 ⁺))
 Lift-PointedType-is-not-equiv {𝓤} = Lift-𝓐-is-not-equiv id lift 𝟘ₒ

\end{code}

∞-magmas.

In the following, A is magma structure:

\begin{code}

 ∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-Magma-structure X = X → X → X

 ∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 ∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , ∞-Magma-structure X

 lift-∞-Magma-structure : ∀ 𝓥 {X : 𝓤 ̇ }
                        → ∞-Magma-structure X
                        → ∞-Magma-structure (Lift 𝓥 X)
 lift-∞-Magma-structure 𝓥 _·_ x y = lift 𝓥 (lower x · lower y)

 Lift-∞-Magma : ∀ {𝓤} 𝓥 → ∞-Magma 𝓤 → ∞-Magma (𝓤 ⊔ 𝓥)
 Lift-∞-Magma {𝓤} 𝓥 (X , _·_) = Lift 𝓥 X , lift-∞-Magma-structure 𝓥 _·_

 Lift-∞-Magma-is-not-equiv : ¬ is-equiv (Lift-∞-Magma {𝓤} (𝓤 ⁺))
 Lift-∞-Magma-is-not-equiv {𝓤} = Lift-𝓐-is-not-equiv
                                   ∞-Magma-structure
                                   lift-∞-Magma-structure
                                   _+ₒ_
\end{code}

Magmas:

\begin{code}

 Magma-structure : 𝓤 ̇ → 𝓤 ̇
 Magma-structure X = is-set X × (X → X → X)

 Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , Magma-structure X

 lift-Magma-structure : ∀ 𝓥 {X : 𝓤 ̇ }
                        → Magma-structure X
                        → Magma-structure (Lift 𝓥 X)
 lift-Magma-structure 𝓥 {X} (X-is-set , _·_) = Lift-is-set 𝓥 X X-is-set ,
                                               λ x y → lift 𝓥 (lower x · lower y)

 Lift-Magma : ∀ {𝓤} 𝓥 → Magma 𝓤 → Magma (𝓤 ⊔ 𝓥)
 Lift-Magma {𝓤} 𝓥 (X , _·_) = Lift 𝓥 X , lift-Magma-structure 𝓥 _·_

 Lift-Magma-structure-is-not-equiv : ¬ is-equiv (Lift-Magma {𝓤} (𝓤 ⁺))
 Lift-Magma-structure-is-not-equiv {𝓤} =
  Lift-𝓐-is-not-equiv
    Magma-structure
    lift-Magma-structure
    (the-type-of-ordinals-is-a-set (ua _) fe' , _+ₒ_)

\end{code}

Monoids:

\begin{code}

 open import Ordinals.ArithmeticProperties ua

 monoid-structure : 𝓤 ̇ → 𝓤 ̇
 monoid-structure X = (X → X → X) × X

 monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 monoid-axioms X (_·_ , e) = is-set X
                           × left-neutral  e _·_
                           × right-neutral e _·_
                           × associative     _·_

\end{code}

We will consider A = Monoid-structure (with capital M), and
𝓐 = Monoid.

\begin{code}

 Monoid-structure : 𝓤 ̇ → 𝓤 ̇
 Monoid-structure X = Σ s ꞉ monoid-structure X , monoid-axioms X s

 Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Monoid 𝓤 = Σ X ꞉ 𝓤 ̇ , Monoid-structure X

 lift-Monoid-structure : ∀ 𝓥 {X : 𝓤 ̇ }
                       → Monoid-structure X
                       → Monoid-structure (Lift 𝓥 X)
 lift-Monoid-structure 𝓥 {X} ((_·_ , e) , X-is-set , l , r , a) = γ
  where
   X' = Lift 𝓥 X

   _·'_ : X' → X' → X'
   x' ·' y' = lift 𝓥 (lower x' · lower y')

   e' : X'
   e' = lift 𝓥 e

   l' : left-neutral e' _·'_
   l' x' = ap (lift 𝓥) (l (lower x'))

   r' : right-neutral e' _·'_
   r' x' = ap (lift 𝓥) (r (lower x'))

   a' : associative _·'_
   a' x' y' z' = ap (lift 𝓥) (a (lower x') (lower y') (lower z'))

   γ : Monoid-structure (Lift 𝓥 X)
   γ = (_·'_ , e') , Lift-is-set 𝓥 X X-is-set , l' , r' , a'

 Lift-Monoid : ∀ {𝓤} 𝓥 → Monoid 𝓤 → Monoid (𝓤 ⊔ 𝓥)
 Lift-Monoid {𝓤} 𝓥 (X , _·_) = Lift 𝓥 X , lift-Monoid-structure 𝓥 _·_

 type-of-ordinals-has-Monoid-structure : {𝓤 : Universe} → Monoid-structure (Ordinal 𝓤)
 type-of-ordinals-has-Monoid-structure {𝓤} = (_+ₒ_ , 𝟘ₒ) ,
                                             (the-type-of-ordinals-is-a-set (ua 𝓤) fe'),
                                             𝟘ₒ-left-neutral ,
                                             𝟘ₒ-right-neutral ,
                                             +ₒ-assoc

 Lift-Monoid-structure-is-not-equiv : ¬ is-equiv (Lift-Monoid {𝓤} (𝓤 ⁺))
 Lift-Monoid-structure-is-not-equiv {𝓤} = Lift-𝓐-is-not-equiv
                                            Monoid-structure
                                            lift-Monoid-structure
                                            type-of-ordinals-has-Monoid-structure
\end{code}

Added 18 Feb 2021. The same is true for groups, using the following
fact and a fact proved in the module FreeGroupOfLargeLocallySmallSet.
We need to assume that propositional truncations exist.

\begin{code}

open import Groups.Type
open import Groups.Large
open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 there-is-a-large-group : Σ F ꞉ Group (𝓤 ⁺) , ((G : Group 𝓤) → ¬ (G ≅ F))
 there-is-a-large-group {𝓤} = large-group-with-no-small-copy fe' pe pt
                               (Ordinal 𝓤 ,
                                (the-type-of-ordinals-is-a-set (ua 𝓤) fe') ,
                                the-type-of-ordinals-is-large ,
                                the-type-of-ordinals-is-locally-small (ua 𝓤) fe')
\end{code}

And from this it of course follows that the embedding of the type of
groups of one universe into that of its successor universe is not an
equivalence:

\begin{code}

 Lift-Group-structure-is-not-equiv : ¬ is-equiv (Lift-Group {𝓤} (𝓤 ⁺))
 Lift-Group-structure-is-not-equiv {𝓤} e = γ there-is-a-large-group
  where
   Lower-Group : Group (𝓤 ⁺) → Group 𝓤
   Lower-Group = inverse (Lift-Group (𝓤 ⁺)) e

   γ : (Σ F ꞉ Group (𝓤 ⁺) , ((G : Group 𝓤) → ¬ (G ≅ F))) → 𝟘
   γ (F , ϕ) = ϕ G i
     where
      G : Group 𝓤
      G = Lower-Group F

      F' : Group (𝓤 ⁺)
      F' = Lift-Group (𝓤 ⁺) G

      p : F' ＝ F
      p = inverses-are-sections (Lift-Group (𝓤 ⁺)) e F

      j : G ≅ F'
      j = ≅-sym F' G (Lifted-Group-is-isomorphic G)

      i : G ≅ F
      i = transport (G ≅_) p j

\end{code}
