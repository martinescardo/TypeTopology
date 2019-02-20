Martin Escardo, 19th Feb 2019.

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

open import UF-Univalence
open import UF-PropTrunc

module InjectiveTypes-article
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import SpartanMLTT
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Embeddings
open import UF-Retracts
open import UF-IdEmbedding
open import UF-UniverseEmbedding

import InjectiveTypes

fe : FunExt
fe = FunExt-from-Univalence ua

pe : PropExt
pe 𝓤 = propext-from-univalence (ua 𝓤)

module blackboard = InjectiveTypes fe

\end{code}

We first define injective types, moderately injective types, and
weakly injective types as follows.

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

Universes are injective:

\begin{code}

universes-are-injective : injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective {𝓤} {𝓥} = blackboard.universes-are-injective-Π (ua (𝓤 ⊔ 𝓥))

universes-are-injective-particular : injective-type (𝓤 ̇) 𝓤 𝓤
universes-are-injective-particular = universes-are-injective

\end{code}

We will rehearse the above construction to get more information below
(still using what is developed in the blackboard). (Kan extensions.)

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

TODO. Include the stuff about the lifting monad regarding injectives.

A further injective resizing for-free construction is possible by
considering a "proof-relevant" notion of flabiness.

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

Ω-injective : propext (𝓤 ⊔ 𝓥) → injective-type (Ω (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Ω-injective {𝓤} {𝓥} pe = flabby-types-are-injective (Ω (𝓤 ⊔ 𝓥)) (Ω-flabby {𝓤 ⊔ 𝓥} {𝓤})

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
propositional resizing gives injective resizing.

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

injective-characterization : propositional-resizing (𝓤 ⁺) 𝓤 → (D : 𝓤 ̇)
                           → injective-type D 𝓤 𝓤 ⇔ Σ \(X : 𝓤 ̇) → retract D of (X → 𝓤 ̇)
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

winjective-∥retract∥-of-power-of-universe : (D : 𝓤 ̇) → is-univalent 𝓤
                                          → winjective-type D 𝓤 (𝓤 ⁺)
                                          → ∥ retract D of (D → 𝓤 ̇) ∥
winjective-∥retract∥-of-power-of-universe = blackboard.weakly-injective.winjective-retract-of-power-of-universe pt

\end{code}

With this we get a partial converse to the fact that moderately
injectives are weakly injective:

\begin{code}

winjective-gives-minjective : is-univalent 𝓤
                             → (D : 𝓤 ̇)
                             → winjective-type D 𝓤 (𝓤 ⁺)
                             → minjective-type D 𝓤 𝓤
winjective-gives-minjective = blackboard.weakly-injective.winjective-gives-∥injective∥ pt

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
                                     → is-univalent 𝓤
                                     → (D  : 𝓤 ̇) → winjective-type D 𝓤 𝓤
                                                  ⇔ minjective-type D 𝓤 𝓤
winjectivity-in-terms-of-injectivity = blackboard.weakly-injective.winjectivity-in-terms-of-injectivity pt

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

pointed-types-winjective-gives-EM : Ω-impredicative 𝓤 → is-univalent 𝓤
                                  → ((D : 𝓤 ̇) → D → winjective-type D 𝓤 𝓤) → EM 𝓤
pointed-types-winjective-gives-EM = blackboard.weakly-injective.pointed-types-winjective-gives-EM pt

\end{code}

TODO. Add the Kan extension properties of the universe and related
things, including that they are themselves embedding (but not only
that). This is actually at the beginning the the injectivity file.

TODO. Add the iterated-extension property.

TODO. Add the retract-extension property.

And I think the list of TODO's includes pretty much what is left to
have a complete article.
