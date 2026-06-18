Martin Escardo, 24th January 2019.
With several additions after that, including by Tom de Jong.

Voedvodsky (Types'2011) considered resizing rules for a type theory
for univalent foundations. These rules govern the syntax of the formal
system, and hence are of a meta-mathematical nature.

Here we instead formulate, in our type theory without such rules, a
mathematical resizing principle. This principle is provable in the
system with Voevodsky's rules. But we don't postulate this principle
as an axiom. Instead, we use it an assumption, when needed, or as a
conclusion, when it follows from stronger principles, such as excluded
middle.

The consistency of the resizing rules is an open problem at the time
of writing (30th January 2018), but the resizing principle is
consistent relative to ZFC with Grothendieck universes, because it
follows from excluded middle, which is known to be validated by the
simplicial-set model (assuming classical logic in its development).

We develop some consequences of propositional resizing here, such as
the fact that every universe is a retract of any higher universe,
where the section is an embedding (its fibers are all propositions),
which seems to be a new result.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Size where

open import MLTT.Spartan
open import UF.Base
open import UF.ClassicalLogic
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.ExitPropTrunc
open import UF.FunExt
open import UF.Hedberg
open import UF.KrausLemma
open import UF.PropIndexedPiSigma
open import UF.PropTrunc
open import UF.Retracts
open import UF.Section-Embedding
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.UA-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

\end{code}

We say that a type X has size 𝓥, or that it is 𝓥 small if it is
equivalent to a type in the universe 𝓥:

\begin{code}

_is_small : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺  ⊔ 𝓤 ̇
X is 𝓥 small = Σ Y ꞉ 𝓥 ̇ , Y ≃ X

native-size : (X : 𝓤 ̇ ) → X is 𝓤 small
native-size X = X , ≃-refl X

resized : (X : 𝓤 ̇ ) → X is 𝓥 small → 𝓥 ̇
resized X = pr₁

resizing-condition : {X : 𝓤 ̇ } (s : X is 𝓥 small)
                   → resized X s ≃ X
resizing-condition = pr₂

\end{code}

Obsolete notation used in some publications:

\begin{code}

private
 _has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺  ⊔ 𝓤 ̇
 X has-size 𝓥 = X is 𝓥 small

\end{code}

The preferred terminology is now "_is_small", but it is better to keep
the terminology "_has-size_" in the papers that have already been
published, in particular "Injective types in univalent mathematics".

\begin{code}

propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-prop P → P is 𝓥 small

Propositional-Resizing : 𝓤ω
Propositional-Resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

\end{code}

Propositional resizing from a universe to a higher universe just
holds, of course:

\begin{code}

resize-up : (X : 𝓤 ̇ ) → X is (𝓤 ⊔ 𝓥) small
resize-up {𝓤} {𝓥} X = Lift 𝓥 X , Lift-is-universe-embedding 𝓥 X

resize-up-proposition : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-proposition {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P

\end{code}

We use the following to work with propositional resizing more
abstractly. We first define the type of some functions and then define
them.

\begin{code}

resize : propositional-resizing 𝓤 𝓥 → (P : 𝓤 ̇ ) (i : is-prop P) → 𝓥 ̇

resize-is-prop : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P)
               → is-prop (resize ρ P i)

to-resize : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P)
          → P → resize ρ P i

from-resize : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P)
            → resize ρ P i → P

to-resize-is-equiv : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P)
                   → is-equiv (to-resize ρ P i)

from-resize-is-equiv : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P)
                     → is-equiv (from-resize ρ P i)

\end{code}

Definitions:

\begin{code}

resize               {𝓤} {𝓥} ρ P i = resized P (ρ P i)
resize-is-prop       {𝓤} {𝓥} ρ P i = equiv-to-prop (resizing-condition (ρ P i)) i
to-resize            {𝓤} {𝓥} ρ P i = ⌜ resizing-condition (ρ P i) ⌝⁻¹
from-resize          {𝓤} {𝓥} ρ P i = ⌜ resizing-condition (ρ P i) ⌝
to-resize-is-equiv   {𝓤} {𝓥} ρ P i = ⌜⌝⁻¹-is-equiv (resizing-condition (ρ P i))
from-resize-is-equiv {𝓤} {𝓥} ρ P i = ⌜⌝-is-equiv (resizing-condition (ρ P i))

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

\end{code}

Propositional resizing is consistent, because it is implied by
excluded middle, which is consistent (with or without univalence):

\begin{code}

decidable-propositions-have-any-size : (P : 𝓤 ̇ )
                                     → is-prop P
                                     → is-decidable P
                                     → P is 𝓥 small
decidable-propositions-have-any-size {𝓤} {𝓥} P i d = Q d , e d
 where
  Q : is-decidable P → 𝓥 ̇
  Q (inl p) = 𝟙
  Q (inr n) = 𝟘

  j : (d : is-decidable P) → is-prop (Q d)
  j (inl p) = 𝟙-is-prop
  j (inr n) = 𝟘-is-prop

  f : (d : is-decidable P) → P → Q d
  f (inl p) p' = ⋆
  f (inr n) p  = 𝟘-elim (n p)

  g : (d : is-decidable P) → Q d → P
  g (inl p) q = p
  g (inr n) q = 𝟘-elim q

  e : (d : is-decidable P) → Q d ≃ P
  e d = logically-equivalent-props-are-equivalent
         (j d) i (g d) (f d)

EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR em P i = decidable-propositions-have-any-size P i (em P i)

\end{code}

To show that the axiom of propositional resizing is itself a
proposition, we use univalence here (and there is a proof with weaker
hypotheses below). But notice that the type "X is 𝓥 small" is a
proposition for every type X if and only if univalence holds.

\begin{code}

being-small-is-prop : Univalence
                    → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                    → is-prop (X is 𝓥 small)
being-small-is-prop {𝓤} ua X 𝓥 = c
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  a : (Y : 𝓥 ̇ ) → (Y ≃ X) ≃ (Lift 𝓤 Y ＝ Lift 𝓥 X)
  a Y = (Y ≃ X)                ≃⟨ a₀ ⟩
        (Lift 𝓤 Y ≃ Lift 𝓥 X)  ≃⟨ a₁ ⟩
        (Lift 𝓤 Y ＝ Lift 𝓥 X)  ■
   where
    a₀ = ≃-cong fe
           (≃-sym (Lift-is-universe-embedding 𝓤 Y))
           (≃-sym (Lift-is-universe-embedding 𝓥 X))
    a₁ = ≃-sym (univalence-≃ (ua (𝓤 ⊔ 𝓥)) _ _)

  b : (Σ Y ꞉ 𝓥 ̇ , Y ≃ X) ≃ (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ＝ Lift 𝓥 X)
  b = Σ-cong a

  c : is-prop (Σ Y ꞉ 𝓥 ̇ , Y ≃ X)
  c = equiv-to-prop b (Lift-is-embedding ua (Lift 𝓥 X))

propositional-resizing-is-prop : Univalence
                               → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-prop {𝓤} {𝓥} ua =
 Π-is-prop (fe (𝓤 ⁺) (𝓥 ⁺ ⊔ 𝓤))
  (λ P → Π-is-prop (fe 𝓤 (𝓥 ⁺ ⊔ 𝓤))
  (λ i → being-small-is-prop ua P 𝓥))
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

\end{code}

And here is a proof that the axiom of propositional resizing is itself
a proposition using propositional and functional extensionality
instead of univalence:

\begin{code}

prop-being-small-is-prop : PropExt
                         → FunExt
                         → (P : 𝓤 ̇ )
                         → is-prop P
                         → {𝓥 :  Universe} → is-prop (P is 𝓥 small)
prop-being-small-is-prop {𝓤} pe fe P i {𝓥} = c
 where
  j : is-prop (Lift 𝓥 P)
  j = equiv-to-prop (Lift-is-universe-embedding 𝓥 P) i

  a : (Y : 𝓥 ̇ ) → (Y ≃ P) ≃ (Lift 𝓤 Y ＝ Lift 𝓥 P)
  a Y = (Y ≃ P)                ≃⟨ a₀ ⟩
        (Lift 𝓤 Y ≃ Lift 𝓥 P)  ≃⟨ a₁ ⟩
        (Lift 𝓤 Y ＝ Lift 𝓥 P) ■
   where
    a₀ = ≃-cong fe
           (≃-sym (Lift-is-universe-embedding 𝓤 Y))
           (≃-sym (Lift-is-universe-embedding 𝓥 P))

    a₁ = ≃-sym (prop-univalent-≃
           (pe (𝓤 ⊔ 𝓥))(fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (Lift 𝓤 Y) (Lift 𝓥 P) j)

  b : (Σ Y ꞉ 𝓥 ̇ , Y ≃ P) ≃ (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ＝ Lift 𝓥 P)
  b = Σ-cong a

  c : is-prop (Σ Y ꞉ 𝓥 ̇ , Y ≃ P)
  c = equiv-to-prop b (prop-fiber-Lift pe fe (Lift 𝓥 P) j)

propositional-resizing-is-prop' : PropExt
                                → FunExt
                                → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-prop' pe fe =
 Π₂-is-prop (fe _ _) (λ P i → prop-being-small-is-prop pe fe P i)

\end{code}

Impredicativity. We begin with this strong notion, which says that the
type Ω 𝓤 of truth values in the universe 𝓤 has a copy in any successor
universe (i.e. in all universes except the first).

\begin{code}

Ω⁺-resizing : (𝓤 : Universe) → 𝓤ω
Ω⁺-resizing 𝓤 = (𝓥 : Universe) → (Ω 𝓤) is (𝓥 ⁺) small

Ω⁺-resizing-from-pr-pe-fe : Propositional-resizing
                          → PropExt
                          → FunExt
                          → Ω⁺-resizing 𝓤
Ω⁺-resizing-from-pr-pe-fe {𝓤} ρ pe fe 𝓥 = γ
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-prop ρ Q j

  ψ : Ω 𝓤 → Ω 𝓥
  ψ (P , i) = resize ρ P i , resize-is-prop ρ P i

  φψ : (p : Ω 𝓤) → φ (ψ p) ＝ p
  φψ (P , i) = Ω-extensionality (pe 𝓤) (fe 𝓤 𝓤)
               (from-resize ρ P i ∘
                from-resize ρ (resize ρ P i) (resize-is-prop ρ P i))
               (to-resize ρ (resize ρ P i) (resize-is-prop ρ P i) ∘
                to-resize ρ P i)

  ψφ : (q : Ω 𝓥) → ψ (φ q) ＝ q
  ψφ (Q , j) = Ω-extensionality (pe 𝓥) (fe 𝓥 𝓥)
               (from-resize ρ Q j ∘
                from-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j))
               (to-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j) ∘
                to-resize ρ Q j)

  γ : (Ω 𝓤) is (𝓥 ⁺) small
  γ = Ω 𝓥 , qinveq φ (ψ , ψφ , φψ)
\end{code}

A more standard notion of impredicativity is that the type Ω 𝓤 of
truth-values in the universe 𝓤 itself lives in 𝓤.

\begin{code}

Ω-resizing : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω-resizing 𝓤 = (Ω 𝓤) is 𝓤 small

\end{code}

Propositional resizing doesn't imply that the first universe 𝓤₀ is
impredicative, but it does imply that all other, successor, universes
𝓤 ⁺ are.

\begin{code}

Ω-resizing⁺-from-pr-pe-fe : Propositional-resizing
                          → PropExt
                          → FunExt
                          → Ω-resizing (𝓤 ⁺)
Ω-resizing⁺-from-pr-pe-fe {𝓤} ρ pe fe = Ω⁺-resizing-from-pr-pe-fe ρ pe fe 𝓤

\end{code}

But excluded middle does give the impredicativity of the first
universe, and of all other universes, of course:

\begin{code}

Ω-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Ω-Resizing 𝓤 𝓥 = (Ω 𝓤) is 𝓥 small

Ω-global-resizing-from-em-pe-fe : EM 𝓤
                                → propext 𝓤
                                → funext 𝓤 𝓤
                                → (𝓥 : Universe) → Ω-Resizing 𝓤 𝓥
Ω-global-resizing-from-em-pe-fe {𝓤} lem pe fe 𝓥 = γ
 where
  em : LEM 𝓤
  em = EM-gives-LEM lem

  φ : 𝟙 + 𝟙 → Ω 𝓤
  φ (inl x) = ⊥
  φ (inr y) = ⊤

  ψ : (p : Ω 𝓤) → is-decidable (p holds) → 𝟙 + 𝟙
  ψ p (inl h) = inr ⋆
  ψ p (inr n) = inl ⋆

  ψφ : (z : 𝟙 + 𝟙) (d : is-decidable ((φ z) holds)) → ψ (φ z) d ＝ z
  ψφ (inl x) (inl h) = 𝟘-elim h
  ψφ (inl x) (inr n) = ap inl (𝟙-is-prop ⋆ x)
  ψφ (inr y) (inl h) = ap inr (𝟙-is-prop ⋆ y)
  ψφ (inr y) (inr n) = 𝟘-elim (n ⋆)

  φψ : (p : Ω 𝓤) (d : is-decidable (p holds)) → φ (ψ p d) ＝ p
  φψ p (inl h) = (true-gives-equal-⊤  pe fe (p holds) (holds-is-prop p) h)⁻¹
  φψ p (inr n) = (false-gives-equal-⊥ pe fe (p holds) (holds-is-prop p) n)⁻¹

  γ : Ω-Resizing 𝓤 𝓥
  γ =  (𝟙 {𝓥} + 𝟙 {𝓥}) ,
       qinveq φ
         ((λ p → ψ p (em p)) ,
          (λ z → ψφ z (em (φ z))) ,
          (λ p → φψ p (em p)))

\end{code}

We also have that moving Ω around universes moves propositions around
universes:

\begin{code}

Ω-resizing-gives-propositional-resizing : Ω-Resizing 𝓤 𝓥
                                        → propext 𝓤
                                        → funext 𝓤 𝓤
                                        → propositional-resizing 𝓤 𝓥
Ω-resizing-gives-propositional-resizing {𝓤} {𝓥} (O , e) pe fe P i = γ
 where
  down : Ω 𝓤 → O
  down = ⌜ ≃-sym e ⌝

  O-is-set : is-set O
  O-is-set = equiv-to-set e (Ω-is-set fe pe)

  Q : 𝓥 ̇
  Q = down ⊤ ＝ down (P , i)

  j : is-prop Q
  j = O-is-set

  φ : Q → P
  φ q = idtofun 𝟙 P (ap pr₁ (equivs-are-lc down (⌜⌝-is-equiv (≃-sym e)) q)) ⋆

  ψ : P → Q
  ψ p = ap down (to-Σ-＝ (pe 𝟙-is-prop i (λ _ → p) (λ _ → ⋆) ,
                         being-prop-is-prop fe _ _))

  ε : Q ≃ P
  ε = logically-equivalent-props-are-equivalent j i φ ψ

  γ : Σ Q ꞉ 𝓥 ̇ , Q ≃ P
  γ = Q , ε

Ω-resizing₀ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω-resizing₀ 𝓤 = (Ω 𝓤) is 𝓤₀ small

Ω-resizing₀-from-em-pe-fe₀ : EM 𝓤
                           → propext 𝓤
                           → funext 𝓤 𝓤
                           → Ω-resizing₀ 𝓤
Ω-resizing₀-from-em-pe-fe₀ {𝓤} em pe fe =
 Ω-global-resizing-from-em-pe-fe em pe fe 𝓤₀

\end{code}

What we get with propositional resizing is that all types of
propositions of any universe 𝓤 are equivalent to Ω 𝓤₀, which lives in
the second universe 𝓤₁:

\begin{code}

Ω-resizing₁ : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓤₂ ̇
Ω-resizing₁ 𝓤 = (Ω 𝓤) is 𝓤₁ small

Ω-resizing₁-from-pr-pe-fe : Propositional-resizing
                          → PropExt
                          → FunExt
                          → Ω-resizing₁ 𝓤
Ω-resizing₁-from-pr-pe-fe {𝓤} ρ pe fe = Ω⁺-resizing-from-pr-pe-fe ρ pe fe 𝓤₀

Ω-resizing₁-≃-from-pr-pe-fe : Propositional-resizing
                            → PropExt
                            → FunExt
                            → Ω 𝓤 ≃ Ω 𝓤₀
Ω-resizing₁-≃-from-pr-pe-fe {𝓤} ρ pe fe =
  ≃-sym (resizing-condition (Ω-resizing₁-from-pr-pe-fe {𝓤} ρ pe fe))

private
 Ω-𝓤₀-lives-in-𝓤₁ : 𝓤₁ ̇
 Ω-𝓤₀-lives-in-𝓤₁ = Ω 𝓤₀

\end{code}

With propositional resizing, we have that any universe is a retract of
any larger universe (this seems to be a new result).

\begin{code}

Lift-is-section : Univalence
                → Propositional-resizing
                → (𝓤 𝓥 : Universe)
                → is-section (Lift {𝓤} 𝓥)
Lift-is-section ua R 𝓤 𝓥 = (r , rs)
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = Lift 𝓥

  e : is-embedding s
  e = Lift-is-embedding ua

  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)

  f : (Y : 𝓤 ⊔ 𝓥 ̇ ) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)

  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = (p : F Y) → fiber-point (f Y p)

  rs : (X : 𝓤 ̇ ) → r (s X) ＝ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇ ) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)

    u : F (s X)
    u = g (s X) (X , refl)

    v : fiber s (s X)
    v = f (s X) u

    i : (Y : 𝓤 ⊔ 𝓥 ̇ ) → is-prop (F Y)
    i Y = resize-is-prop R (fiber s Y) (e Y)

    X' : 𝓤 ̇
    X' = fiber-point v

    a : r (s X) ≃ X'
    a = prop-indexed-product u (Univalence-gives-FunExt ua 𝓤 𝓤) (i (s X))

    b : s X' ＝ s X
    b = fiber-identification v

    c : X' ＝ X
    c = embeddings-are-lc s e b

    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a

    γ : r (s X) ＝ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

\end{code}

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, Logical Methods in Computer
Science, April 27, 2017, Volume 12, Issue 3,
https://lmcs.episciences.org/2027 , Theorem 3.10).

Hence it is worth stating this explicitly:

\begin{code}

universe-retract' : Univalence
                  → Propositional-resizing
                  → (𝓤 𝓥 : Universe)
                  → Σ (r , s , η) ꞉ retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ ), is-embedding s
universe-retract' ua R 𝓤 𝓥 = (pr₁ a , Lift 𝓥 , pr₂ a) , Lift-is-embedding ua
 where
  a : Σ lower ꞉ (𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇ ) , lower ∘ Lift 𝓥 ∼ id
  a = Lift-is-section ua R 𝓤 𝓥

\end{code}

A more conceptual version of the above construction is in the module
InjectiveTypes (which was discovered first - this is just an unfolding
of that construction).

TODO. If we assume that we have such a retraction, does weak
propositional resizing follow?

The following construction is due to Voevodsky, but we use the
resizing axiom rather than his rules (and we work with non-cumulative
universes).

\begin{code}

module _ {𝓤 : Universe} where

 ∥_∥⁺ : 𝓤 ̇ → 𝓤 ⁺ ̇
 ∥ X ∥⁺ = (P :  𝓤 ̇ ) → is-prop P → (X → P) → P

 ∥∥⁺-is-prop : FunExt → {X : 𝓤 ̇ } → is-prop (∥ X ∥⁺)
 ∥∥⁺-is-prop fe = Π-is-prop (fe _ _)
                    (λ P → Π-is-prop (fe _ _)
                            (λ i → Π-is-prop (fe _ _)
                                     (λ u → i)))

 ∣_∣⁺ : {X : 𝓤 ̇ } → X → ∥ X ∥⁺
 ∣ x ∣⁺ = λ P i u → u x

 ∥∥⁺-rec : {X P : 𝓤 ̇ } → is-prop P → (X → P) → ∥ X ∥⁺ → P
 ∥∥⁺-rec {X} {P} i u s = s P i u

resizing-truncation : FunExt
                    → Propositional-resizing
                    → propositional-truncations-exist
resizing-truncation fe R = record {
    ∥_∥          = λ {𝓤} X → resize R ∥ X ∥⁺ (∥∥⁺-is-prop fe)
  ; ∥∥-is-prop   = λ {𝓤} {X} → resize-is-prop R ∥ X ∥⁺ (∥∥⁺-is-prop fe)
  ; ∣_∣          = λ {𝓤} {X} x → to-resize R ∥ X ∥⁺ (∥∥⁺-is-prop fe) ∣ x ∣⁺
  ; ∥∥-rec       = λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                              (∥∥⁺-rec (resize-is-prop R P i)
                                                       (to-resize R P i ∘ u)
                                                       (from-resize R ∥ X ∥⁺
                                                         (∥∥⁺-is-prop fe) s))
 }

\end{code}

Images:

\begin{code}

module Image
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        (fe : FunExt)
        (R : Propositional-resizing)
       where

 open PropositionalTruncation (resizing-truncation fe R)

 image : (X → Y) → 𝓥 ̇
 image f = Σ y ꞉ Y , resize (R {𝓤 ⊔ 𝓥} {𝓥}) (∃ x ꞉ X , f x ＝ y) ∥∥-is-prop

 restriction : (f : X → Y) → image f → Y
 restriction f (y , _) = y

 restriction-embedding : (f : X → Y) → is-embedding (restriction f)
 restriction-embedding f = pr₁-is-embedding (λ y → resize-is-prop R _ _)

 corestriction : (f : X → Y) → X → image f
 corestriction f x = f x , to-resize R _ _ ∣ x , refl ∣

\end{code}

TODO. Prove the properties / perform the constructions in
UF.ImageAndSurjection. Better: reorganize the code so that reproving
is not necessary.

Added 24 January 2020 (originally proved 19 November 2019) by Tom de Jong.

It turns out that a proposition Y has size 𝓥 precisely if
(Y is 𝓥 small) is 𝓥 small.

Hence, if you can resize the propositions of the form (Y is 𝓥 small)
(with Y in 𝓤), then you can resize all propositions in 𝓤 (to 𝓥).

\begin{code}

being-small-is-idempotent : (ua : Univalence) (𝓤 𝓥 : Universe) (Y : 𝓤 ̇ )
                          → is-prop Y
                          → (Y is 𝓥 small) is 𝓥 small
                          → Y is 𝓥 small
being-small-is-idempotent ua 𝓤 𝓥 Y i (H , e) = X , γ
 where
  X : 𝓥 ̇
  X = Σ h ꞉ H , resized Y (eqtofun e h)

  γ = X  ≃⟨ Σ-change-of-variable (resized Y) (eqtofun e) (eqtofun- e) ⟩
      X' ≃⟨ ϕ ⟩
      Y  ■
   where
    X' : 𝓥 ⁺ ⊔ 𝓤 ̇
    X' = Σ h ꞉ Y is 𝓥 small , resized Y h

    ϕ = logically-equivalent-props-are-equivalent j i f g
     where
      j : is-prop X'
      j = Σ-is-prop (being-small-is-prop ua Y 𝓥)
            (λ (h : Y is 𝓥 small) → equiv-to-prop (resizing-condition h) i)

      f : X' → Y
      f (e' , x) = eqtofun (resizing-condition e') x

      g : Y → X'
      g y = (𝟙{𝓥} , 𝟙-≃-singleton (pointed-props-are-singletons y i)) , ⋆

deJong-resizing : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
deJong-resizing 𝓤 𝓥 = (Y : 𝓤 ̇ ) → (Y is 𝓥 small) is 𝓥 small

deJong-resizing-implies-propositional-resizing : (ua : Univalence)
                                                 (𝓤 𝓥 : Universe)
                                               → deJong-resizing 𝓤 𝓥
                                               → propositional-resizing 𝓤 𝓥
deJong-resizing-implies-propositional-resizing ua 𝓤 𝓥 r P i =
 being-small-is-idempotent ua 𝓤 𝓥 P i (r P)

being-small-is-idempotent-converse
 : (ua : Univalence) (𝓤 𝓥 : Universe) (Y : 𝓤 ̇ )
 → Y is 𝓥 small
 → (Y is 𝓥 small) is 𝓥 small
being-small-is-idempotent-converse ua 𝓤 𝓥 Y r = 𝟙{𝓥} , γ
 where
  γ : 𝟙{𝓥} ≃ (Y is 𝓥 small)
  γ = 𝟙-≃-singleton
       (pointed-props-are-singletons r (being-small-is-prop ua Y 𝓥))

being-small-is-idempotent-≃ : (ua : Univalence) (𝓤 𝓥 : Universe) (Y : 𝓤 ̇ )
                            → is-prop Y
                            → ((Y is 𝓥 small) is 𝓥 small) ≃ (Y is 𝓥 small)
being-small-is-idempotent-≃ ua 𝓤 𝓥 Y i =
 logically-equivalent-props-are-equivalent
  (being-small-is-prop ua (Y is 𝓥 small) 𝓥)
  (being-small-is-prop ua Y 𝓥)
  (being-small-is-idempotent ua 𝓤 𝓥 Y i)
  (being-small-is-idempotent-converse ua 𝓤 𝓥 Y)

being-small-is-idempotent-＝ : (ua : Univalence) (𝓤 𝓥 : Universe) (Y : 𝓤 ̇ )
                            → is-prop Y
                            → ((Y is 𝓥 small) is 𝓥 small) ＝ (Y is 𝓥 small)
being-small-is-idempotent-＝ ua 𝓤 𝓥 Y i =
 eqtoid (ua (𝓤 ⊔ 𝓥 ⁺))
  ((Y is 𝓥 small) is 𝓥 small)
  (Y is 𝓥 small)
  (being-small-is-idempotent-≃ ua 𝓤 𝓥 Y i)

\end{code}

Added 26th January 2021. The following is based on joint work of Tom
de Jong with Martin Escardo.

TODO. Maybe "is-small" should be "is-essentially-small" and "is-large"
should also be renamed, for conformance with the (category-theoretic)
literature.

\begin{code}

is-small : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
is-small {𝓤} X = X is 𝓤 small

is-large : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
is-large X = ¬ is-small X

universes-are-large : is-large (𝓤 ̇ )
universes-are-large = II
 where
  open import Various.LawvereFPT

  I : ¬ (Σ X ꞉ 𝓤 ̇ , 𝓤 ̇ ≃ X)
  I = generalized-Coquand.Theorem

  II : ¬ (Σ X ꞉ 𝓤 ̇ , X ≃ 𝓤 ̇ )
  II = contrapositive (λ (X , 𝕗) → (X , ≃-sym 𝕗)) I

_is_small-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (X → Y)
              → (𝓦 : Universe)
              → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
f is 𝓦 small-map = ∀ y → fiber f y is 𝓦 small

_is-small-map : {X Y : 𝓤 ⁺ ̇ } → (X → Y) → 𝓤 ⁺ ̇
_is-small-map {𝓤} f = f is 𝓤 small-map

native-size-of-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → f is 𝓤 ⊔ 𝓥 small-map
native-size-of-map f y = native-size (fiber f y)

\end{code}

Obsolete notation used in some publications:

\begin{code}

private
 _Has-size_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
 f Has-size 𝓦 = f is 𝓦 small-map

\end{code}

The above should not be used anymore, but should be kept here.

\begin{code}

pr₁-is-small-map : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → (λ (σ : Σ Y) → pr₁ σ) is 𝓥 small-map
pr₁-is-small-map {𝓤} {𝓥} {X} {Y} x = Y x , ≃-sym (pr₁-fiber-equiv x)

𝟚-to-Ω-is-small-map : funext 𝓤 𝓤
                    → propext 𝓤
                    → (𝟚-to-Ω {𝓤}) is 𝓤 small-map
𝟚-to-Ω-is-small-map fe pe p = (¬ (p holds) + p holds) ,
                              ≃-sym (𝟚-to-Ω-fiber fe pe p)

size-contravariance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → f is 𝓦 small-map
                    → Y is 𝓦 small
                    → X is 𝓦 small
size-contravariance {𝓤} {𝓥} {𝓦} {X} {Y} f f-size (Y' , 𝕘) = γ
 where
  F : Y → 𝓦 ̇
  F y = resized (fiber f y) (f-size y)

  F-is-fiber : (y : Y) → F y ≃ fiber f y
  F-is-fiber y = resizing-condition (f-size y)

  X' : 𝓦 ̇
  X' = Σ y' ꞉ Y' , F (⌜ 𝕘 ⌝ y')

  e = X'                    ≃⟨ Σ-change-of-variable F ⌜ 𝕘 ⌝ (⌜⌝-is-equiv 𝕘) ⟩
      (Σ y ꞉ Y , F y)       ≃⟨ Σ-cong F-is-fiber ⟩
      (Σ y ꞉ Y , fiber f y) ≃⟨ total-fiber-is-domain f ⟩
      X                     ■

  γ : X is 𝓦 small
  γ = X' , e

size-covariance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → f is 𝓦 small-map
                → ¬ (X is 𝓦 small)
                → ¬ (Y is 𝓦 small)
size-covariance f ϕ = contrapositive (size-contravariance f ϕ)

small-contravariance : {X Y : 𝓤 ⁺ ̇ } (f : X → Y)
                     → f is-small-map
                     → is-small Y
                     → is-small X
small-contravariance = size-contravariance

large-covariance : {X Y : 𝓤 ⁺ ̇ } (f : X → Y)
                 → f is-small-map
                 → is-large X
                 → is-large Y
large-covariance = size-covariance

size-of-section-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
                          → is-section s
                          → is-embedding s
                          → s is 𝓥 small-map
size-of-section-embedding {𝓤} {𝓥} {X} {Y} s (r , η) e y = γ
 where
  c : (x : Y) → collapsible (s (r x) ＝ x)
  c = section-embedding-gives-collapsible r s η e

  κ : s (r y) ＝ y → s (r y) ＝ y
  κ = pr₁ (c y)

  κ-constant : (p p' : s (r y) ＝ y) → κ p ＝ κ p'
  κ-constant = pr₂ (c y)

  B : 𝓥 ̇
  B = fix κ

  B-is-prop : is-prop B
  B-is-prop = fix-is-prop κ κ-constant

  α : B → fiber s y
  α = (λ p → r y , p) ∘ from-fix κ

  β : fiber s y → B
  β = to-fix κ κ-constant ∘ λ (x , p) → s (r y)     ＝⟨ ap (s ∘ r) (p ⁻¹) ⟩
                                        s (r (s x)) ＝⟨ ap s (η x) ⟩
                                        s x         ＝⟨ p ⟩
                                        y           ∎

  δ : B ≃ fiber s y
  δ = logically-equivalent-props-are-equivalent B-is-prop (e y) α β

  γ : (fiber s y) is 𝓥 small
  γ = B , δ

section-embedding-size-contravariance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (s : X → Y)
                                      → is-embedding s
                                      → is-section s
                                      → Y is 𝓦 small
                                      → X is 𝓦 small
section-embedding-size-contravariance
 {𝓤} {𝓥} {𝓦} {X} {Y} s e (g , η) (Y' , h , i) = γ
 where
  h⁻¹ : Y → Y'
  h⁻¹ = inverse h i

  s' : X → Y'
  s' = h⁻¹ ∘ s

  η' = λ x → g (h (h⁻¹ (s x))) ＝⟨ ap g (inverses-are-sections h i (s x)) ⟩
             g (s x)           ＝⟨ η x ⟩
             x                 ∎

  δ : s' is 𝓦 small-map
  δ = size-of-section-embedding s' (g ∘ h , η')
       (∘-is-embedding e (equivs-are-embeddings h⁻¹
                         (inverses-are-equivs h i)))

  γ : X is 𝓦 small
  γ = size-contravariance s' δ (Y' , ≃-refl Y')

embedded-retract-is-small : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            (ρ : retract X of Y)
                          → is-embedding (section ρ)
                          → Y is 𝓦 small
                          → X is 𝓦 small
embedded-retract-is-small (r , s , rs) s-is-embedding Y-is-small =
 section-embedding-size-contravariance s s-is-embedding (r , rs) Y-is-small

\end{code}

Added 17 January 2026 by Tom de Jong, after a discussion with Martín Escardó.

The embedding condition in the above lemma is actually redundant: small types
are closed under general retracts. This is Theorem 2.13 of

 Tom de Jong and Martín Hötzel Escardó.
 On Small Types in Univalent Foundations.
 Logical Methods in Computer Science, 19(2):8:1─8:33, 2023.
 https://doi.org/10.46298/lmcs-19(2:8)2023

which uses Lemma 3.6 and the construction in the proof of Theorem 5.3 of

 Michael Shulman.
 Idempotents in intensional type theory.
 Logical Methods in Computer Science, 12(3):9:1–9:24, 2016.
 https://doi.org/10.2168/LMCS-12(3:9)2016

Shulman's results are formalized in the Coq-HoTT library
(https://github.com/HoTT/Coq-HoTT, see theories/Idempotents.v).

Here we formalize Theorem 2.13 of our paper, but take Shulman's construction as
an hypothesis, rather than porting the whole proof from Coq to Agda.

Note that Shulman's construction relies only on function extensionality (which
can be checked in Rocq and is also claimed in Shulman's paper), so we include
that as an assumption.

Also note that Shulman's Theorem 5.3 is in fact more general than we consider
here: it applies to any quasi-idempotent f. By Lemma 3.6, any retraction r with
section s determines a quasi-idempotent f via f := s ∘ r which is enough for
purposes.

\begin{code}

Shulman's-Splitting-Construction : 𝓤ω
Shulman's-Splitting-Construction =
 Fun-Ext
 → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (ρ : retract Y of X)
 → let f = section ρ ∘ retraction ρ in
   let A = Σ a ꞉ (ℕ → X) , Π n ꞉ ℕ , f (a (succ n)) ＝ a n in
   Σ ρ' ꞉ retract A of X , section ρ' ∘ retraction ρ' ∼ f

retracts-of-small-types-are-small
 : Fun-Ext
 → Shulman's-Splitting-Construction
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → retract Y of X
 → X is 𝓦 small
 → Y is 𝓦 small
retracts-of-small-types-are-small {𝓤} {𝓥} {𝓦} fe ssc {X} {Y} ρ₀ (X' , φ) = A , ψ
 where
  ρ : retract Y of X'
  ρ = retracts-compose (≃-gives-▷ φ) ρ₀
  r : X' → Y
  r = retraction ρ
  s : Y → X'
  s = section ρ

  f : (x : X') → X'
  f = s ∘ r
  A : 𝓦 ̇
  A = Σ a ꞉ (ℕ → X') , Π n ꞉ ℕ , f (a (succ n)) ＝ a n
  shulman-splitting : Σ ρ' ꞉ retract A of X' , section ρ' ∘ retraction ρ' ∼ f
  shulman-splitting = ssc fe ρ

  ρ' = pr₁ shulman-splitting
  r' : X' → A
  r' = retraction ρ'
  s' : A → X'
  s' = section ρ'
  eq : s' ∘ r' ∼ s ∘ r
  eq = pr₂ shulman-splitting

  ψ : A ≃ Y
  ψ = r ∘ s' , qinvs-are-equivs (r ∘ s') (r' ∘ s , I , II)
   where
    I : r' ∘ s ∘ r ∘ s' ∼ id
    I a = (r' ∘ s ∘ r ∘ s') a   ＝⟨ ap r' ((eq (s' a)) ⁻¹) ⟩
          (r' ∘ s' ∘ r' ∘ s') a ＝⟨ retract-condition ρ' (r' (s' a)) ⟩
          (r' ∘ s') a           ＝⟨ retract-condition ρ' a ⟩
          a                     ∎
    II : r ∘ s' ∘ r' ∘ s ∼ id
    II y = (r ∘ s' ∘ r' ∘ s) y ＝⟨ ap r (eq (s y)) ⟩
           (r ∘ s ∘ r ∘ s) y   ＝⟨ retract-condition ρ (r (s y)) ⟩
           (r ∘ s) y           ＝⟨ retract-condition ρ y ⟩
           y                   ∎

\end{code}

End of addition.

\begin{code}

≃-size-contravariance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → X ≃ Y
                      → Y is 𝓦 small
                      → X is 𝓦 small
≃-size-contravariance {𝓤} {𝓥} {𝓦} {X} {Y} e (Z , d) = Z , ≃-comp d (≃-sym e)

singletons-have-any-size : {X : 𝓤 ̇ }
                         → is-singleton X
                         → X is 𝓥 small
singletons-have-any-size i = 𝟙 , 𝟙-≃-singleton i

equivs-have-any-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-equiv f
                     → f is 𝓦 small-map
equivs-have-any-size {𝓤} {𝓥} {𝓦} {X} {Y} f e y =
 singletons-have-any-size (equivs-are-vv-equivs f e y)

equivs-have-any-size' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝕗 : X ≃ Y)
                     → ⌜ 𝕗 ⌝ is 𝓦 small-map
equivs-have-any-size' (f , e) = equivs-have-any-size f e

\end{code}

The following notion of local smallness is due to Egbert Rijke, in his
join-construction paper https://arxiv.org/abs/1701.07538.

\begin{code}

_is-locally_small : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
X is-locally 𝓥 small = (x y : X) → (x ＝ y) is 𝓥 small

is-locally-small : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
is-locally-small X = (x y : X) → is-small (x ＝ y)

\end{code}

For example, by univalence, universes are locally small, and so is the
(large) type of ordinals in a universe.

\begin{code}

universes-are-locally-small : is-univalent 𝓤 → is-locally-small (𝓤 ̇ )
universes-are-locally-small ua X Y = (X ≃ Y) , ≃-sym (univalence-≃ ua X Y)

Ω-is-locally-small : propext 𝓤 → funext 𝓤 𝓤 → is-locally-small (Ω 𝓤)
Ω-is-locally-small pe fe p q = ((p holds) ↔ (q holds)) ,
                               Ω-extensionality-≃ pe fe

\end{code}

General machinery for dealing with local smallness:

\begin{code}

_＝⟦_⟧_ : {X : 𝓤 ̇ } → X → X is-locally 𝓥 small → X → 𝓥 ̇
x ＝⟦ ls ⟧ y = resized (x ＝ y) (ls x y)

Id⟦_⟧ : {X : 𝓤 ̇ } → X is-locally 𝓥 small → X → X → 𝓥 ̇
Id⟦ ls ⟧ x y = x ＝⟦ ls ⟧ y

＝⟦_⟧-≃-＝ : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
           → (x ＝⟦ ls ⟧ y) ≃ (x ＝ y)
＝⟦ ls ⟧-≃-＝ {x} {y} = resizing-condition (ls x y)

＝⟦_⟧-gives-＝ : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
               → x ＝⟦ ls ⟧ y → x ＝ y
＝⟦ ls ⟧-gives-＝ = ⌜ ＝⟦ ls ⟧-≃-＝ ⌝

＝-gives-＝⟦_⟧ : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
               → x ＝ y → x ＝⟦ ls ⟧ y
＝-gives-＝⟦ ls ⟧ = ⌜ ＝⟦ ls ⟧-≃-＝ ⌝⁻¹

＝⟦_⟧-refl : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x : X} → x ＝⟦ ls ⟧ x
＝⟦ ls ⟧-refl {x} = ⌜ ≃-sym (resizing-condition (ls x x)) ⌝ refl

＝⟦_⟧-sym : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
          → x ＝⟦ ls ⟧ y
          → y ＝⟦ ls ⟧ x
＝⟦ ls ⟧-sym p = ＝-gives-＝⟦ ls ⟧ (＝⟦ ls ⟧-gives-＝ p ⁻¹)

_≠⟦_⟧_ : {X : 𝓤 ̇ } → X → X is-locally 𝓥 small → X → 𝓥 ̇
x ≠⟦ ls ⟧ y = ¬ (x ＝⟦ ls ⟧ y)

≠⟦_⟧-irrefl : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x : X} → ¬ (x ≠⟦ ls ⟧ x)
≠⟦ ls ⟧-irrefl {x} ν = ν ＝⟦ ls ⟧-refl

≠⟦_⟧-sym : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
         → x ≠⟦ ls ⟧ y
         → y ≠⟦ ls ⟧ x
≠⟦ ls ⟧-sym {x} {y} n = λ (p : y ＝⟦ ls ⟧ x) → n (＝⟦ ls ⟧-sym p)

≠-gives-≠⟦_⟧ : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
             → x ≠ y
             → x ≠⟦ ls ⟧ y
≠-gives-≠⟦ ls ⟧ = contrapositive ＝⟦ ls ⟧-gives-＝

≠⟦_⟧-gives-≠ : {X : 𝓤 ̇ } (ls : X is-locally 𝓥 small) {x y : X}
             → x ≠⟦ ls ⟧ y → x ≠ y
≠⟦ ls ⟧-gives-≠ = contrapositive ＝-gives-＝⟦ ls ⟧

\end{code}

Added 11 Jul 2023 by Martin Escardo.

\begin{code}

subtype-is-small : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                 → ((x : X) → is-prop (A x))
                 → X is 𝓦 small
                 → Σ A is 𝓥 ⊔ 𝓦 small
subtype-is-small {𝓤} {𝓥} {𝓦} {X} {A} A-is-prop-valued (X' , 𝕗) = S , 𝕘
 where
  S : 𝓥 ⊔ 𝓦 ̇
  S = Σ x' ꞉ X' , A (⌜ 𝕗 ⌝ x')

  𝕘 = (Σ x' ꞉ X' , A (⌜ 𝕗 ⌝ x')) ≃⟨ Σ-change-of-variable-≃ A 𝕗 ⟩
      (Σ x ꞉ X , A x)            ■

subtype-is-locally-small : {X : 𝓤 ⁺ ̇ } {A : X → 𝓤 ⁺ ̇ }
                         → ((x : X) → is-prop (A x))
                         → is-locally-small X
                         → is-locally-small (Σ A)
subtype-is-locally-small A-is-prop-valued X-is-ls (x , a) (y , b) = γ
 where
  γ : is-small ((x , a) ＝ (y , b))
  γ = x ＝⟦ X-is-ls ⟧ y ,
     (x ＝⟦ X-is-ls ⟧ y     ≃⟨ resizing-condition (X-is-ls x y) ⟩
     (x ＝ y)               ≃⟨ to-subtype-＝-≃ A-is-prop-valued ⟩
     ((x , a) ＝ (y , b))   ■)

subtype-is-locally-small⁻ : {X : 𝓤 ⁺ ̇ } {A : X → 𝓤 ̇ }
                          → ((x : X) → is-prop (A x))
                          → is-locally-small X
                          → is-locally-small (Σ A)
subtype-is-locally-small⁻ A-is-prop-valued X-is-ls (x , a) (y , b) = γ
 where
  γ : is-small ((x , a) ＝ (y , b))
  γ = x ＝⟦ X-is-ls ⟧ y ,
     (x ＝⟦ X-is-ls ⟧ y     ≃⟨ resizing-condition (X-is-ls x y) ⟩
     (x ＝ y)               ≃⟨ to-subtype-＝-≃ A-is-prop-valued ⟩
     ((x , a) ＝ (y , b))   ■)

\end{code}

TODO. Generalize the above to resize (the values of) A as well.

Added by Ian Ray 11th September 2024.

If X is 𝓥-small then it is locally 𝓥-small.

\begin{code}

small-implies-locally-small : (X : 𝓤 ̇ ) (𝓥 : Universe)
                            → X is 𝓥 small
                            → X is-locally 𝓥 small
small-implies-locally-small X 𝓥 (Y , e) x x' =
 ((⌜ e ⌝⁻¹ x ＝ ⌜ e ⌝⁻¹ x') , path-resized)
 where
  path-resized : (⌜ e ⌝⁻¹ x ＝ ⌜ e ⌝⁻¹ x') ≃ (x ＝ x')
  path-resized = ≃-sym (ap ⌜ e ⌝⁻¹ , ap-is-equiv ⌜ e ⌝⁻¹ (⌜⌝⁻¹-is-equiv e))

\end{code}

Added by Ian Ray 18th August 2025.

\begin{code}

subtype-is-locally-small' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                          → X is-locally 𝓤' small
                          → ((x : X) → is-prop (A x))
                          → Σ A is-locally 𝓤' small
subtype-is-locally-small' {_} {_} {𝓤'}
 X-is-ls A-is-prop-valued (x , a) (y , b) = γ
 where
  γ : ((x , a) ＝ (y , b)) is 𝓤' small
  γ = resized (x ＝ y) (X-is-ls x y) ,
      (resized (x ＝ y) (X-is-ls x y) ≃⟨ resizing-condition (X-is-ls x y) ⟩
      (x ＝ y)                        ≃⟨ to-subtype-＝-≃ A-is-prop-valued ⟩
      ((x , a) ＝ (y , b))            ■)

\end{code}

End of addition.

Added 5 April 2022 by Tom de Jong, after discussion with Martín.
(Refactoring an earlier addition dated 15 March 2022.)

Set Replacement is what we call the following principle:
given X : 𝓤 and Y a locally 𝓥-small *set*, the image of a map f : X → Y is
(𝓤 ⊔ 𝓥)-small.

In particular, if 𝓤 and 𝓥 are the same, then the image is 𝓤-small.

The name "Set Replacement" is inspired by [Section 2.19, Bezem+2022], but is
different in two ways:
(1) In [Bezem+2022] replacement is not restricted to maps into sets, hence our
    name *Set* Replacement
(2) In [Bezem+2022] the universe parameters 𝓤 and 𝓥 are taken to be the same.

[Rijke2017] shows that the replacement of [Bezem+2022] is provable in the
presence of a univalent universes 𝓤 closed under pushouts.

In Quotient.Type.lagda, we prove that Set Replacement is provable if we assume
that for every X : 𝓤 and 𝓥-valued equivalence relation ≈, the set quotient X / ≈
exists in 𝓤 ⊔ 𝓥.

In Quotient.Type.lagda we prove the converse using a specific construction of
quotients, similar to [Corollary 5.1, Rijke2017].

Thus, Set Replacement is equivalent to having set quotients in 𝓤 ⊔ 𝓥 for every
type in 𝓤 with a 𝓥-valued equivalence relation (which is what you would have
when adding set quotients as higher inductive types).

[Rijke2017]  Egbert Rijke. The join construction.
             https://arxiv.org/abs/1701.07538, January 2017.

[Bezem+2022] Marc Bezem, Ulrik Buchholtz, Pierre Cagne, Bj‌ørn Ian Dundas and
             Daniel R. Grayson
             Symmetry
             https://unimath.github.io/SymmetryBook/book.pdf
             https://github.com/UniMath/SymmetryBook
             Book version: 2722568 (2022-03-31)

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open import UF.ImageAndSurjection pt

 Set-Replacement : 𝓤ω
 Set-Replacement = {𝓦 𝓣 𝓤 𝓥 : Universe} {X : 𝓣 ̇ } {Y : 𝓦 ̇ } (f : X → Y)
                 → X is 𝓤 small
                 → Y is-locally 𝓥 small
                 → is-set Y
                 → image f is (𝓤 ⊔ 𝓥) small
\end{code}

Added by Martin Escardo and Tom de Jong 29th August 2024.

\begin{code}

WEM-gives-that-negated-types-are-small
 : funext 𝓤 𝓤₀
 → typal-WEM 𝓤
 → (X : 𝓤 ̇ ) → (¬ X) is 𝓥 small
WEM-gives-that-negated-types-are-small {𝓤} {𝓥} fe wem X =
 Cases (wem (¬ X)) f g
 where
  f : ¬¬ X → (¬ X) is 𝓥 small
  f h = 𝟘 , ≃-sym (empty-≃-𝟘 h)

  g : ¬¬¬ X → (¬ X) is 𝓥 small
  g h = 𝟙 ,
        𝟙-≃-singleton
         (pointed-props-are-singletons
           (three-negations-imply-one h)
           (negations-are-props fe))

\end{code}
