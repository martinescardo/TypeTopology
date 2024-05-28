-------------------------------------------------------------------------------
authors:      ["Ayberk Tosun", "Martin Trucchi"]
date-started: 2024-05-02
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.SierpinskiObject
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import Dominance.Definition
open import UF.Classifiers
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

What is a Sierpiński object? In Martín Escardó´s unpublished note [_Topology via
higher-order intuitionistic logic_][1], a Sierpiński object is defined in the
setting of a topos as a subobject of the subobject classifier. This is also
given in Definition 2.4 of Davorin Lesnik's thesis, who took this unpublished
note as a starting point for his PhD thesis.

The purpose of this development is to develop these notions in the context of
HoTT/UF, where we look at subtypes of the subtype classifier. Because we work
predicatively, however, the definition of the notion of Sierpiński object is not
that straightforward in our setting.

\begin{code}

Sierpinski-Object : 𝓤 ⁺  ̇
Sierpinski-Object = Subtypes' 𝓤  (Ω 𝓤)

Sierpinski-Object' : 𝓤 ⁺ ⁺  ̇
Sierpinski-Object' = Ω 𝓤 → Ω (𝓤 ⁺)

\end{code}

Claim: these are equivalent.

\begin{code}

equivalence-of-sierpinski-object-definitions
 : is-univalent (𝓤 ⁺) → funext (𝓤 ⁺) (𝓤 ⁺ ⁺) → Subtypes' (𝓤 ⁺) (Ω 𝓤) ≃ Sierpinski-Object'
equivalence-of-sierpinski-object-definitions ua fe =
 Ω-is-subtype-classifier ua fe (Ω 𝓤)

\end{code}

We define some notation to refer to components of a Sierpiński object.

\begin{code}

index : Sierpinski-Object → 𝓤  ̇
index (I , α , _) = I

sierpinski-fun : (𝕊 : Sierpinski-Object) → index 𝕊 → Ω 𝓤
sierpinski-fun (_ , α , _) = α

\end{code}

In the module below, we assume the existence of a Sierpiński object `𝕊` and
define some notions _synthetically_, following the work of Martín Escardó (and
Davorin Lešnik).

\begin{code}

module Sierpinski-notations (𝕊 : Sierpinski-Object) where

 ι : index 𝕊 → Ω 𝓤
 ι = sierpinski-fun 𝕊

 S : 𝓤  ̇
 S = index 𝕊

\end{code}

The propositions in `Ω` that fall in the subset delineated by the Sierpiński
object are called _affirmable.

\begin{code}

 is-affirmable : Ω 𝓤 → Ω (𝓤 ⁺)
 is-affirmable P = P ∈image ι , ∃-is-prop

\end{code}

Here, we only work with sets. 

A subset of a set is said to be intrinsically open if it is a predicate defined
by affirmable propositions.

\begin{code}

 is-intrinsically-open : {(X , sX) : hSet 𝓤} → (X → Ω 𝓤) → Ω (𝓤 ⁺)
 is-intrinsically-open {X , sX} P = Ɐ x ꞉ X , is-affirmable (P x)

\end{code}

For convenience, we write down the subtype of open propositions (= subset) of a set X

\begin{code}

 open-props : hSet 𝓤 → (𝓤 ⁺) ̇
 open-props (X , sX) = Σ P ꞉ (X → Ω 𝓤) , is-intrinsically-open {X , sX} P holds

 syntax open-props X = 𝓞 X

 underlying-prop : {(X , sX) : hSet 𝓤} → (open-props (X , sX)) → (X → Ω 𝓤)
 underlying-prop = pr₁


\end{code}

Another way to define this notion, which is equivalent assuming choice, is the
following:

\begin{code}

 is-intrinsically-open′ : {(X , sX) : hSet 𝓤} → (X → Ω 𝓤) → Ω 𝓤
 is-intrinsically-open′ {X , sX} P =
  Ǝₚ h ꞉ (X → S) , (Ɐ x ꞉ X , P x ⇔ ι (h x))

\end{code}

The former definition turns out to more useful in our case.

Useful lemmas, which shorten proofs (maybe move it elsewhere at some point)

\begin{code}

 ⇔-transport : {𝓥 𝓦 : Universe} {P Q : Ω 𝓥} → (𝓟 : Ω 𝓥 → 𝓦 ̇) → ((P ⇔ Q) holds) → (𝓟 P) → (𝓟 Q)
 ⇔-transport {𝓥} {𝓦} {P} {Q} (𝓟) P-iff-Q Prop-P = transport 𝓟 q Prop-P
   where
    q : P ＝ Q
    q = ⇔-gives-＝ pe P Q (holds-gives-equal-⊤ pe fe (P ⇔ Q) P-iff-Q)


 ⇔-affirmable : {P Q : Ω 𝓤}  → ((P ⇔ Q) ⇒ is-affirmable P ⇒ is-affirmable Q) holds
 ⇔-affirmable = ⇔-transport (_holds ∘ is-affirmable)

\end{code}

The definition `is-intrinsically-open′` is stronger than is-intrinsically-open.

\begin{code}

 open-implies-open′ : {(X , sX) : hSet 𝓤 } → (P : X → Ω 𝓤)
                    → (is-intrinsically-open′ {X , sX}  P ⇒ is-intrinsically-open {X , sX} P) holds
 open-implies-open′ {X , sX} P = ∥∥-rec (holds-is-prop (is-intrinsically-open P)) †
  where
   † : (Σ h ꞉ (X → S) , ((x : X) → P x holds ↔ ι (h x) holds))
     → is-intrinsically-open P holds
   † (h , φ) x = ⇔-affirmable p ∣ (h x) , refl ∣
    where
     p : (ι (h x) holds) ↔ (P x holds)
     p = ↔-sym (φ x)

\end{code}

[1]: https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
