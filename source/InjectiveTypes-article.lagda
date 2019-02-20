wMartin Escardo, 19th Feb 2019.

Injective types in univalent mathematics.

This is an article-style version of the blackboard-style version.

This is based on the "blackboard" Agda file InjectiveTypes, which
presents the ideas as they have been developed, rather than the way
they should be presented for a mathematical audience, but still in a
fully verified way with the computer as the referee.

Here we tell the story, referring to the blackboard file for the
proofs (which can be followed as links in the html version of this
file).

The blackboard file likely has more information than that reported
here. In particular, it keeps track better of what univalent
assumptions are used in each construction (univalence, function
extensionality, propositional extensionality, existence of
propositional truncations).

Here we repeat the main definitions (in a definitionally equal way,
even with the same names) and state the main theorems with links to
their blackboard (verified) proofs.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Univalence
open import UF-PropTrunc

module InjectiveTypes-article
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import UF-FunExt
open import UF-UA-FunExt
open import UF-Embeddings
open import UF-Retracts
open import UF-Equiv
open import UF-UniverseEmbedding
open import UF-PropIndexedPiSigma

import InjectiveTypes

fe : FunExt
fe = FunExt-from-Univalence ua

pe : PropExt
pe 𝓤 = propext-from-univalence (ua 𝓤)

module blackboard = InjectiveTypes fe

\end{code}

We study the notions of injective type (data), moderately injective
type (property), and weakly injective type (property) and their
relationships.

\begin{code}

injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                     → (f : domain j → D) → Σ \(f' : codomain j → D) → f' ∘ j ∼ f

minjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
minjective-type D 𝓤 𝓥 = ∥ injective-type D 𝓤 𝓥 ∥

winjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
winjective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                      → (f : X → D) → ∃ \(f' : Y → D) → f' ∘ j ∼ f
\end{code}

Universes are injective, in at least two ways.

\begin{code}

_╲_ _╱_ :  {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓦 ̇) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇)
(f ╲ j) y = Σ \(w : fiber j y) → f(pr₁ w)
(f ╱ j) y = Π \(w : fiber j y) → f(pr₁ w)


\end{code}

The crucial idea behind the following two statements is that a sum
indexed by a proposition (the fiber) is (equivalent, and hence) equal,
to any of its summands, and a product indexed by a proposition is
equal to any of its factors, and the fiber is a propositino when j is
an embedding.

\begin{code}

╲-is-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇) → f ╲ j ∘ j ∼ f
╲-is-extension {𝓤} {𝓥} = blackboard.Σ-extension-is-extension (ua (𝓤 ⊔ 𝓥))

╱-is-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇) → f ╱ j ∘ j ∼ f
╱-is-extension {𝓤} {𝓥} = blackboard.Π-extension-is-extension (ua (𝓤 ⊔ 𝓥))

universes-are-injective-Σ : injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective-Σ {𝓤} {𝓥} j e f = (f ╲ j , ╲-is-extension j e f)

universes-are-injective-Π : injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective-Π {𝓤} {𝓥} j e f = (f ╱ j , ╱-is-extension j e f)

universes-are-injective : injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective = universes-are-injective-Σ

universes-are-injective-particular : injective-type (𝓤 ̇) 𝓤 𝓤
universes-are-injective-particular = universes-are-injective

\end{code}

For y:Y not in the image of j, the extensions give 𝟘 and 𝟙 respectively:

\begin{code}

Σ-extension-out-of-range : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
                         → (y : Y) → ((x : X) → j x ≢ y)
                         → (f ╲ j) y ≃ 𝟘 {𝓣}
Σ-extension-out-of-range f j y φ = prop-indexed-sum-zero (uncurry φ)


Π-extension-out-of-range : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
                         → (y : Y) → ((x : X) → j x ≢ y)
                         → (f ╱ j) y ≃ 𝟙 {𝓣}
Π-extension-out-of-range {𝓤} {𝓥} {𝓦} f j y φ = prop-indexed-product-one (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

\end{code}

With excluded middle, this would give that Σ and Π extensions have the
same sum and product as the non-extended maps, respectively, but
excluded middle is not needed:

\begin{code}

same-Σ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
       → Σ f ≃ Σ (f ╲ j)
same-Σ = blackboard.same-Σ

same-Π : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
       → Π f ≃ Π (f ╱ j)
same-Π = blackboard.same-Π

\end{code}

These two extensions are left and right (pointwise) Kan extensions in
the following sense. First, A map X → 𝓤, when X is viewed as a
∞-groupoid and hence an ∞-category, and when 𝓤 is viewed as the
∞-generalization of the category of sets, can be considered as a sort
of ∞-presheaf, because its functoriality is automatic. Then we can
consider natural transformations between such ∞-presheafs. But again
the naturality condition is automatic.  We denote by _≾_ the type of
natural transformations between such ∞-presheafs.

\begin{code}

_[_] : {X : 𝓤 ̇} (f : X → 𝓥 ̇) {x y : X} → Id x y → f x → f y
f [ refl ] = id

functoriality∙ : {X : 𝓤 ̇} (f : X → 𝓥 ̇) {x y z : X} (p : Id x y) (q : Id y z)
               → f [ p ∙ q ] ≡ f [ q ] ∘ f [ p ]
functoriality∙ f refl refl = refl

_≾_ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
f ≾ g = (x : domain f) → f x → g x

naturality : {X : 𝓤 ̇} (f : X → 𝓥 ̇) (g : X → 𝓦 ̇) (τ : f ≾ g) {x y : X} (p : x ≡ y)
           → τ y ∘ f [ p ] ≡ g [ p ] ∘ τ x
naturality f g τ refl = refl

\end{code}

With this notation, we have:

\begin{code}


ηΣ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
   → f ≾ f ╲ j ∘ j
ηΣ f j x B = (x , refl) , B


ηΠ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
  → (f ╱ j) ∘ j ≾ f
ηΠ f j x A = A (x , refl)

\end{code}

These actually follow from the following more general facts:

\begin{code}

Σ-extension-left-Kan : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y) (g : Y → 𝓣 ̇)
                     → (f ╲ j ≾ g) ≃ (f ≾ g ∘ j)
Σ-extension-left-Kan f j g = blackboard.Σ-extension-left-Kan f j g

Π-extension-right-Kan : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y) (g : Y → 𝓣 ̇)
                      → (g ≾ f ╱ j) ≃ (g ∘ j ≾ f)
Π-extension-right-Kan f j g = blackboard.Π-extension-right-Kan f j g

\end{code}

TODO: Add the iterated-extension and retract-extension properties.

This completes our discussion of extensions of maps into the universe.

Retracts of injective are injective:

\begin{code}

retract-of-injective : (D' : 𝓦' ̇) (D : 𝓦 ̇)
                     → injective-type D 𝓤 𝓥
                     → retract D' of D
                     → injective-type D' 𝓤 𝓥
retract-of-injective = blackboard.retract-of-injective

\end{code}

Products of injectives are injectives:

\begin{code}

Π-injective : {A : 𝓣 ̇} {D : A → 𝓦 ̇}
            → ((a : A) → injective-type (D a) 𝓤 𝓥)
            → injective-type (Π D) 𝓤 𝓥
Π-injective = blackboard.Π-injective

\end{code}

Hence exponential powers of injectives are injective.

\begin{code}

power-of-injective : {A : 𝓣 ̇} {D : 𝓦 ̇}
                   → injective-type D 𝓤 𝓥
                   → injective-type (A → D) 𝓤 𝓥
power-of-injective i = Π-injective (λ a → i)

\end{code}

An injective type is a retract of every type it is embedded into:

\begin{code}

injective-retract-of-subtype : (D : 𝓦 ̇) → injective-type D 𝓦 𝓥
                             → (Y : 𝓥 ̇) → D ↪ Y → retract D of Y
injective-retract-of-subtype D i Y (j , e) = blackboard.embedding-retract D Y j e i

\end{code}

The identity-type former Id is an embedding X → (X → 𝓤):

\begin{code}

Id-is-embedding : {X : 𝓤 ̇} → is-embedding(Id {𝓤} {X})
Id-is-embedding {𝓤} = UA-Id-embedding (ua 𝓤) fe
 where
  open import UF-IdEmbedding

\end{code}

From this we conclude that injective types are powers of universes:

\begin{code}

injective-is-retract-of-power-of-universe : (D : 𝓤 ̇)
                                          → injective-type D 𝓤  (𝓤 ⁺)
                                          → retract D of (D → 𝓤 ̇)
injective-is-retract-of-power-of-universe {𝓤} D i = injective-retract-of-subtype D i (D → 𝓤 ̇)
                                                      (Id , Id-is-embedding)

\end{code}

The above results, when combined together in the obvious way, almost
give directly that the injective types are precisely the retracts of
exponential powers of universes, but there is a universe mismatch.

Keeping track of the universes to avoid the mismatch, what we get
instead is a resizing theorem:

\begin{code}

injective-resizing₀ : (D : 𝓤 ̇) → injective-type D 𝓤 (𝓤 ⁺) → injective-type D 𝓤 𝓤
injective-resizing₀ {𝓤} D i = φ (injective-is-retract-of-power-of-universe D i)
 where
  φ : retract D of (D → 𝓤 ̇) → injective-type D 𝓤 𝓤
  φ = retract-of-injective D (D → 𝓤 ̇) (power-of-injective (universes-are-injective))

\end{code}

A further injective resizing for-free construction is possible by
considering a notion of flabiness as data (rather than as property, as
in the 1-topos literature).

\begin{code}

flabby : 𝓦 ̇ → (𝓤 : Universe) → 𝓦 ⊔ 𝓤 ⁺ ̇
flabby D 𝓤 = (P : 𝓤 ̇) → is-prop P → (f : P → D) → Σ \(d : D) → (p : P) → d ≡ f p

\end{code}

Flabby types are pointed:

\begin{code}

flabby-pointed : (D : 𝓦 ̇) → flabby D 𝓤 → D
flabby-pointed D φ = pr₁ (φ 𝟘 𝟘-is-prop unique-from-𝟘)

\end{code}

And injective types (in the proof-relevant way we have defined them)
are flabby, because maps P → 𝟙 from propositions P are embeddings:

\begin{code}

injective-types-are-flabby : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → flabby D 𝓤
injective-types-are-flabby = blackboard.injective-types-are-flabby

\end{code}

The interesting thing is that the universe 𝓥 is forgotten in this
construction, with only 𝓤 remaining, particularly regarding this
converse, which says that flabby types are injective:

\begin{code}

flabby-types-are-injective : (D : 𝓦 ̇) → flabby D (𝓤 ⊔ 𝓥) → injective-type D 𝓤 𝓥
flabby-types-are-injective = blackboard.flabby-types-are-injective

\end{code}

TODO. Explain this verbally or reproduce the proof (or both).

We then get this resizing theorem by composing the conversions between
flabiness and injectivity:

\begin{code}

injective-resizing₁ : (D : 𝓦 ̇) → injective-type D (𝓤 ⊔ 𝓣) 𝓥 → injective-type D 𝓤 𝓣
injective-resizing₁ D i j e f = flabby-types-are-injective D (injective-types-are-flabby D i) j e f

\end{code}

We record two particular cases that may make this clearer:

\begin{code}

injective-resizing₂ : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤 𝓤
injective-resizing₂ = injective-resizing₁

injective-resizing₃ : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤₀ 𝓤
injective-resizing₃ = injective-resizing₁

\end{code}

This is resizing down.

The type Ω 𝓤 of propositions of a universe 𝓤 is flabby. More generally:

\begin{code}

Ω-flabby : {𝓤 𝓥 : Universe} → flabby (Ω (𝓤 ⊔ 𝓥)) 𝓤
Ω-flabby {𝓤} {𝓥} = blackboard.Ω-flabby {𝓤} {𝓥} (pe (𝓤 ⊔ 𝓥))

\end{code}

Therefore it is injective:

\begin{code}

Ω-injective : injective-type (Ω (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Ω-injective {𝓤} {𝓥} = flabby-types-are-injective (Ω (𝓤 ⊔ 𝓥)) (Ω-flabby {𝓤 ⊔ 𝓥} {𝓤})

\end{code}

Another way to see this is that it is a retract of the universe by
propositional truncation. (Exercise, not included.)

Flabiness can also be applied to show that all types are injective iff
excluded middle holds.

\begin{code}

open import UF-ExcludedMiddle

EM-gives-pointed-types-flabby : (D : 𝓦 ̇) → EM 𝓤 → D → flabby D 𝓤
EM-gives-pointed-types-flabby = blackboard.EM-gives-pointed-types-flabby

\end{code}

For the converse, we consider, given a proposition P, the type P + ¬ P + 𝟙,
which, if it is flabby, gives the decidability of P.

\begin{code}

flabby-EM-lemma : (P : 𝓦 ̇) → is-prop P → flabby ((P + ¬ P) + 𝟙) 𝓦 → P + ¬ P
flabby-EM-lemma = blackboard.flabby-EM-lemma

\end{code}

From this we conclude:

\begin{code}

pointed-types-flabby-gives-EM : ((D : 𝓦 ̇) → D → flabby D 𝓦) → EM 𝓦
pointed-types-flabby-gives-EM {𝓦} α P i = flabby-EM-lemma P i (α ((P + ¬ P) + 𝟙) (inr *))

EM-gives-pointed-types-injective : EM (𝓤 ⊔ 𝓥) → (D : 𝓦 ̇) → D → injective-type D 𝓤 𝓥
EM-gives-pointed-types-injective em D d = flabby-types-are-injective D (EM-gives-pointed-types-flabby D em d)

pointed-types-injective-gives-EM : ((D : 𝓦 ̇) → D → injective-type D 𝓦 𝓤) → EM 𝓦
pointed-types-injective-gives-EM α = pointed-types-flabby-gives-EM (λ D d → injective-types-are-flabby D (α D d))

\end{code}

Returning to size issues, we now apply flabiness to show that
propositional resizing gives unrestricted injective resizing.

The propositional resizing principle, from 𝓤 to 𝓥, that we consider
here says that every proposition in the universe 𝓤 has an equivalent
copy in the universe 𝓥 (this is consistent because it is implied by
excluded middle, but, as far as we are aware, there is no known
computational interpretation of this axiom).

We begin with this lemma:

\begin{code}

open import UF-Resizing

flabiness-resizing : (D : 𝓦 ̇) (𝓤 𝓥 : Universe) → propositional-resizing 𝓤 𝓥
                   → flabby D 𝓥 → flabby D 𝓤
flabiness-resizing = blackboard.flabiness-resizing

\end{code}

TODO. Explain the (simple) idea behind it.

And from this it follows that the injectivity of a type with respect
to two given universes 𝓤 and 𝓥 implies its injectivity with respect to
all universes 𝓤' and 𝓥': we convert back-and-forth between injectivity
and flabiness:

\begin{code}

injective-resizing : propositional-resizing (𝓤' ⊔ 𝓥') 𝓤
                   → (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤' 𝓥'
injective-resizing = blackboard.injective-resizing

\end{code}

As an application of this and of injectivity of universes, we have
that any universe is a retract of any larger universe.

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, https://arxiv.org/abs/1507.03634).

But we can choose the retraction so that the section is an embedding,
in this case:

\begin{code}

universe-retract : Propositional-resizing
                 → (𝓤 𝓥 : Universe)
                 → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)) → is-embedding (section ρ)
universe-retract = blackboard.universe-retract ua

\end{code}

Here are are using the fact that every injective type is a retract of
any type in which it is embedded into, in conjunction with resizing,
and that there is an embedding of any universe into any larger
universe, assuming univalence.

As mentioned above, we almost have that the injective types are
precisely the retracts of exponential powers of universes, upto a
universe mismatch. This mismatch is side-steped by propositional
resizing:

\begin{code}

injective-characterization : propositional-resizing (𝓤 ⁺) 𝓤
                           → (D : 𝓤 ̇) → injective-type D 𝓤 𝓤 ⇔ Σ \(X : 𝓤 ̇) → retract D of (X → 𝓤 ̇)
injective-characterization {𝓤} = blackboard.injective-characterization (ua 𝓤)

\end{code}

We now discuss moderate and weak injectivity as defined above in
relation to injectivity.

\begin{code}

winjectivity-is-a-prop : (D : 𝓦 ̇) (𝓤 𝓥 : Universe)
                       → is-prop (winjective-type D 𝓤 𝓥)
winjectivity-is-a-prop = blackboard.weakly-injective.winjectivity-is-a-prop pt

injective-gives-winjective : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → winjective-type D 𝓤 𝓥
injective-gives-winjective = blackboard.weakly-injective.injective-gives-winjective pt

minjective-gives-winjective : (D : 𝓦 ̇) → minjective-type D 𝓤 𝓥  → winjective-type D 𝓤 𝓥
minjective-gives-winjective = blackboard.weakly-injective.∥injective∥-gives-winjective pt

\end{code}

In order to relate weak injectivity to moderate injectivity, we first
prove some facts we already proved for injectivity for weak
injectivity. These facts cannot be obtained by reduction (in
particular products of weakly injectives are not necessarily weakly
injectives, but exponential powers are).

\begin{code}

embedding-∥retract∥ : (D : 𝓦 ̇) (Y : 𝓥 ̇) (j : D → Y) → is-embedding j → winjective-type D 𝓦 𝓥
                   → ∥ retract D of Y ∥
embedding-∥retract∥ = blackboard.weakly-injective.embedding-∥retract∥ pt

retract-of-winjective : (D' : 𝓤 ̇) (D : 𝓥 ̇)
                      → winjective-type D 𝓦 𝓣
                      → retract D' of D
                      → winjective-type D' 𝓦 𝓣
retract-of-winjective = blackboard.weakly-injective.retract-of-winjective pt

power-of-winjective : {A : 𝓣 ̇} {D : 𝓣 ⊔ 𝓦 ̇}
                    → winjective-type D       (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
                    → winjective-type (A → D) (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
power-of-winjective {𝓣} {𝓦} {𝓤} {𝓥} = blackboard.weakly-injective.power-of-winjective pt {𝓣} {𝓦} {𝓤} {𝓥}

winjective-∥retract∥-of-power-of-universe : (D : 𝓤 ̇)
                                          → winjective-type D 𝓤 (𝓤 ⁺)
                                          → ∥ retract D of (D → 𝓤 ̇) ∥
winjective-∥retract∥-of-power-of-universe {𝓤} D = blackboard.weakly-injective.winjective-retract-of-power-of-universe
                                                    pt D (ua 𝓤)
\end{code}

With this we get a partial converse to the fact that moderately
injectives are weakly injective:

\begin{code}

winjective-gives-minjective : (D : 𝓤 ̇)
                             → winjective-type D 𝓤 (𝓤 ⁺)
                             → minjective-type D 𝓤 𝓤
winjective-gives-minjective {𝓤} = blackboard.weakly-injective.winjective-gives-∥injective∥ pt (ua 𝓤)

\end{code}

So, in summary, regarding the relationship between winjectivity and
truncated injectivity, so far we know that

  minjective-type D 𝓤 𝓥  → winjective-type D 𝓤 𝓥

and

  winjective-type D 𝓤 (𝓤 ⁺) → minjective-type D 𝓤 𝓤,

and hence, using propositional resizing, we get the following
characterization of a particular case of winjectivity in terms of
injectivity.

\begin{code}

winjectivity-in-terms-of-injectivity' : propositional-resizing (𝓤 ⁺) 𝓤
                                      → (D : 𝓤  ̇) → winjective-type D 𝓤 (𝓤 ⁺)
                                                   ⇔ minjective-type D 𝓤 (𝓤 ⁺)
winjectivity-in-terms-of-injectivity' {𝓤} = blackboard.weakly-injective.winjectivity-in-terms-of-injectivity' pt
                                             (ua 𝓤)

\end{code}

We we would like to do better than this. For that purpose, we consider
the lifting monad in conjunction with resizing.

TODO. Include the stuff about the lifting monad regarding injectives.

\begin{code}

import Lifting
import LiftingAlgebras
import LiftingEmbeddingViaSIP

𝓛 : {𝓣 𝓤 : Universe} → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛 {𝓣} {𝓤} X = Σ \(P : 𝓣 ̇) → (P → X) × is-prop P

𝓛-unit : {𝓣 𝓤 : Universe} (X : 𝓤 ̇) → X → 𝓛 {𝓣} X
𝓛-unit X x = 𝟙 , (λ _ → x) , 𝟙-is-prop

𝓛-unit-is-embedding : (X : 𝓤 ̇) → is-embedding (𝓛-unit {𝓣} X)
𝓛-unit-is-embedding {𝓤} {𝓣} X = LiftingEmbeddingViaSIP.η-is-embedding' 𝓣 𝓤 X (ua 𝓣) (fe 𝓣 𝓤)

joinop : {𝓣 𝓤 : Universe} → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
joinop {𝓣} {𝓤} X = {P : 𝓣 ̇} → is-prop P → (P → X) → X

𝓛-alg-Law₀ : {𝓣 𝓤 : Universe} {X : 𝓤 ̇} → joinop {𝓣} X → 𝓤 ̇
𝓛-alg-Law₀ {𝓣} {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x

𝓛-alg-Law₁ : {𝓣 𝓤 : Universe} {X : 𝓤 ̇} → joinop {𝓣} X → (𝓣 ⁺) ⊔ 𝓤 ̇
𝓛-alg-Law₁ {𝓣} {𝓤} {X} ∐ = (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p)) (f : Σ Q → X)
                                → ∐ (Σ-is-prop i j) f ≡ ∐ i (λ p → ∐ (j p) (λ q → f (p , q)))

𝓛-alg : {𝓣 𝓤 : Universe} → 𝓤 ̇ → (𝓣 ⁺) ⊔ 𝓤 ̇
𝓛-alg {𝓣} {𝓤} X = Σ \(∐ : joinop {𝓣} X) → 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

𝓛-alg-flabby : {𝓣 𝓤 : Universe} {A : 𝓤 ̇} → 𝓛-alg {𝓣} A → flabby A 𝓣
𝓛-alg-flabby {𝓣} {𝓤} = blackboard.injectivity-of-lifting.𝓛-alg-flabby 𝓣 (pe 𝓣) (fe 𝓣 𝓣) (fe 𝓣 𝓤)

𝓛-alg-injective : (A : 𝓤 ̇) → 𝓛-alg {𝓣} A → injective-type A 𝓣 𝓣
𝓛-alg-injective A α = flabby-types-are-injective A (𝓛-alg-flabby α)

free-𝓛-algebra-injective : (X : 𝓣 ̇) → injective-type (𝓛 {𝓣} X) 𝓣 𝓣
free-𝓛-algebra-injective {𝓣} X = 𝓛-alg-injective (𝓛 X)
                                   (LiftingAlgebras.𝓛-algebra-gives-alg 𝓣
                                     (LiftingAlgebras.free-𝓛-algebra 𝓣 (ua 𝓣) X))
\end{code}

Because the unit of the lifting monad is an embedding, it follows that
injective types are retracts of underlying objects of free algebras:

\begin{code}

injective-is-retract-of-free-𝓛-algebra : (D : 𝓣 ̇) → injective-type D 𝓣 (𝓣 ⁺) → retract D of (𝓛 {𝓣} D)
injective-is-retract-of-free-𝓛-algebra D i = injective-retract-of-subtype D i (𝓛 D)
                                               (𝓛-unit D , 𝓛-unit-is-embedding D)
\end{code}

With propositional resizing, the injective types are precisely the
retracts of the underlying objects of free algebras of the lifting
monad:

\begin{code}

injectives-in-terms-of-free-𝓛-algebras : (D : 𝓣 ̇) → propositional-resizing (𝓣 ⁺) 𝓣
                                       → injective-type D 𝓣 𝓣
                                       ⇔ Σ \(X : 𝓣 ̇) → retract D of (𝓛 {𝓣} X)
injectives-in-terms-of-free-𝓛-algebras {𝓣} D R =  a , b
  where
   a : injective-type D 𝓣 𝓣 → Σ \(X : 𝓣 ̇) → retract D of (𝓛 X)
   a i = D , injective-is-retract-of-free-𝓛-algebra D (injective-resizing R D i)
   b : (Σ \(X : 𝓣 ̇) → retract D of (𝓛 X)) → injective-type D 𝓣 𝓣
   b (X , r) = retract-of-injective D (𝓛 X) (free-𝓛-algebra-injective X) r

\end{code}

TODO. Discuss the lifting monad. What is crucial is that (1) the unit
is an embedding, (2) with impredicativity the lifting construction
remains in the same universe, and (3) lifted types are injective
(because they are flabby - in fact all algebras, not just the free
algebras of the lifting monad as flabby (the algebra structure adds
equations to flabiness)). For the moment we just quote the results
that rely on this.

Instead of propositional resizing, we consider the impredicativity of
the universe 𝓤, which says that the type of propositions in 𝓤, which
lives in the next universe 𝓤 ⁺, has an equivalent copy in 𝓤 (for the
relationship between resizing and impredicativity, see the module
UF-Resizing).

\begin{code}

winjectivity-in-terms-of-injectivity : Ω-impredicative 𝓤
                                     → (D  : 𝓤 ̇) → winjective-type D 𝓤 𝓤
                                                  ⇔ minjective-type D 𝓤 𝓤
winjectivity-in-terms-of-injectivity {𝓤} i = blackboard.weakly-injective.winjectivity-in-terms-of-injectivity
                                               pt i (ua 𝓤)

\end{code}

Here are some corollaries:

\begin{code}

winjective-resizing : Ω-impredicative 𝓤
                    → (D : 𝓤 ̇)
                    → winjective-type D 𝓤 𝓤
                    → (𝓥 𝓦 : Universe) → propositional-resizing (𝓥 ⊔ 𝓦) 𝓤 → winjective-type D 𝓥 𝓦
winjective-resizing {𝓤} = blackboard.weakly-injective.winjective-resizing pt (ua 𝓤)

EM-gives-pointed-types-winjective : EM 𝓤 → (D : 𝓤 ̇) → D → winjective-type D 𝓤 𝓤
EM-gives-pointed-types-winjective {𝓤} em D d = injective-gives-winjective D
                                                 (EM-gives-pointed-types-injective em D d)

pointed-types-winjective-gives-EM : Ω-impredicative 𝓤
                                  → ((D : 𝓤 ̇) → D → winjective-type D 𝓤 𝓤) → EM 𝓤
pointed-types-winjective-gives-EM {𝓤} i = blackboard.weakly-injective.pointed-types-winjective-gives-EM
                                            pt i (ua 𝓤)

\end{code}

I think the list of TODO's includes pretty much what is left to have a
complete article.

TODO. To make sure, go over every single line of the 1586 lines of the
InjectiveTypes file.

Fixities:

\begin{code}

infix  7 _╲_
infix  7 _╱_
infixr 4 _≾_

\end{code}
