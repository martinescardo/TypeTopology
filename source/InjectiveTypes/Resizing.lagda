Tom de Jong and Martin Escardo, 25th August 2023.

The idea is that there should be no small injective types. However,
with Ω-resizing (a form of impredicativity for HoTT/UF), there are
small injective types, for example Ω 𝓤₀.  So we instead show that,
under some conditions, small injective types give resizing. But at the
moment we are able to derive Ω¬¬-resizing only (which is a weaker, but
still not provable, form of impredicativity).

It was previously known that if propositional resizing
holds then

 ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤' 𝓥'

for all universes 𝓤, 𝓥, 𝓤', 𝓥', so that (algebraic) injectivity is
universe independent.

It was also known that

 ainjective-type D (𝓤 ⊔ 𝓣) 𝓥 → ainjective-type D 𝓤 𝓣,

which resizes down the first universe parameter, and that

 * ainjective-type (𝓤  ̇ ) 𝓤 𝓤      (Universes are injective)
 * ainjective-type (Ω 𝓤) 𝓤 𝓤       (the type of propositions is injective)
 * ainjective-type (Ω¬¬ 𝓤) 𝓤 𝓤     (the type of ¬¬-stable propositions is injective)
 * ainjective-type (Ordinal 𝓤) 𝓤 𝓤 (the type of ordinals is injective)
 * ainjective-type (Magma∞ 𝓤) 𝓤 𝓤  (the type of ∞-magmas is injective)
 * ainjective-type (Monoid 𝓤) 𝓤 𝓤  (the type of monoids is injective)
 * ainjective-type (𝕄 𝓤) 𝓤 𝓤       (the type of iterative multisets is injective)
 * ainjective-type (𝕍 𝓤) 𝓤 𝓤       (the type of iterative sets is injective)

among others. We show that the above universe parameters are tight, in
the sense that we cannot increase

 ainjective D 𝓤 𝓤

to

 ainjective D (𝓤 ⁺) 𝓤

for the above choices of D unless we have Ω¬¬-resizing. In fact, the
third parameter is irrelevant. For any 𝓥, we have that

 ainjective D (𝓤 ⁺) 𝓥

implies Ω¬¬-resizing for the above choices of D.

We also show that for no type D in the first universe 𝓤₀ can we have

 ainjective D 𝓤₀ 𝓤₀

as soon as it has two distinct points, other than in models that
validate Ω¬¬ 𝓤₀ resizing (in which Ω¬¬ 𝓤₀, being a retract of Ω 𝓤₀, is
injective and serves as an example of such a D).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.Resizing
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.NotNotStablePropositions
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import InjectiveTypes.Article ua pt
open import InjectiveTypes.OverSmallMaps fe

\end{code}

The fact that retracts of small types are small is proved in Theorem
2.13 of

 Tom de Jong and Martín Hötzel Escardó.
 On Small Types in Univalent Foundations.
 Logical Methods in Computer Science, 19(2):8:1─8:33, 2023.
 https://doi.org/10.46298/lmcs-19(2:8)2023

This uses Lemma 3.6 and the construction in the proof of Theorem 5.3
of

 Michael Shulman.
 Idempotents in intensional type theory.
 Logical Methods in Computer Science, 12(3):9:1–9:24, 2016.
 https://doi.org/10.2168/LMCS-12(3:9)2016

But we haven't proved it in TypeTopology yet, and so we assume it as a
hypothesis.

TODO. Formalize the proof of the following
`retracts-of-small-types-are-small` hypothesis, which is provided in the
above two papers.

\begin{code}

retracts-of-small-types-are-small : 𝓤ω
retracts-of-small-types-are-small =
   {𝓤 𝓥 𝓦 : Universe}
   {X : 𝓤 ̇ }
 → {Y : 𝓥 ̇ }
 → retract Y of X
 → X is 𝓦 small
 → Y is 𝓦 small

small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing
 : retracts-of-small-types-are-small
 → (D : 𝓤 ̇ )
 → ainjective-type D (𝓤 ⊔ 𝓥) 𝓦
 → has-two-distinct-points D
 → Ω¬¬ 𝓤 is 𝓤 small
small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing
 {𝓤} {𝓥} {𝓦} small-retracts D D-ainj ((x₀ , x₁) , distinct) = II I
 where
  f : 𝟚 → D
  f ₀ = x₀
  f ₁ = x₁

  I : Σ s ꞉ (Ω¬¬ 𝓤 → D) , s ∘ 𝟚-to-Ω¬¬ ∼ f
  I = ainjectivity-over-small-maps {𝓤} {𝓤₀} {𝓤 ⁺} {𝓤} {𝓥} {𝓦}
       D
       D-ainj
       𝟚-to-Ω¬¬
       (𝟚-to-Ω¬¬-is-embedding fe pe)
       (𝟚-to-Ω¬¬-is-small-map fe pe)
       f

  II : type-of I → Ω¬¬ 𝓤 is 𝓤 small
  II (s , extension-property) = Ω¬¬-is-small
   where
    III : s ⊥Ω¬¬ ＝ x₀
    III = extension-property ₀

    IV : s ⊤Ω¬¬ ＝ x₁
    IV = extension-property ₁

    V : (𝕡 : Ω¬¬ 𝓤) → s 𝕡 ≠ x₀ → pr₁ 𝕡 holds
    V 𝕡 e = V₃
     where
      V₀ : 𝕡 ＝ ⊥Ω¬¬ → s 𝕡 ＝ x₀
      V₀ e = transport⁻¹ (λ - → s - ＝ x₀) e III
      V₁ : 𝕡 ≠ ⊥Ω¬¬
      V₁ = contrapositive V₀ e
      V₂ : ¬¬ (𝕡 holds')
      V₂ u = V₁ (to-Ω¬¬-＝ fe' (fails-gives-equal-⊥ pe' fe' (Ω¬¬-to-Ω 𝕡) u))
      V₃ : 𝕡 holds'
      V₃ = holds'-is-¬¬-stable 𝕡 V₂

    VI  : (𝕡 : Ω¬¬ 𝓤) → pr₁ 𝕡 holds → s 𝕡 ≠ x₀
    VI 𝕡 h = VI₃
     where
      VI₀ : Ω¬¬-to-Ω 𝕡 ＝ ⊤
      VI₀ = holds-gives-equal-⊤ pe' fe' (Ω¬¬-to-Ω 𝕡) h
      VI₁ : 𝕡 ＝ ⊤Ω¬¬
      VI₁ = to-Ω¬¬-＝ fe' VI₀
      VI₂ : s 𝕡 ＝ x₁
      VI₂ = transport⁻¹ (λ - → s - ＝ x₁) VI₁ IV
      VI₃ : s 𝕡 ≠ x₀
      VI₃ e = distinct
               (x₀  ＝⟨ e ⁻¹ ⟩
                s 𝕡 ＝⟨ VI₂ ⟩
                x₁  ∎)

    VII : (𝕡 : Ω¬¬ 𝓤) → (s 𝕡 ≠ x₀) ＝ (pr₁ 𝕡 holds)
    VII 𝕡 = pe' (negations-are-props fe')
                (holds'-is-prop 𝕡)
                (V 𝕡)
                (VI 𝕡)

    r : D → Ω¬¬ 𝓤
    r d = ((d ≠ x₀) , negations-are-props fe') , ¬-is-¬¬-stable

    rs : r ∘ s ∼ id
    rs 𝕡 = r (s 𝕡)              ＝⟨ refl ⟩
           ((s 𝕡 ≠ x₀) , _) , _ ＝⟨ to-Ω¬¬-＝' fe' (VII 𝕡) ⟩
           𝕡                     ∎

    ρ : retract (Ω¬¬ 𝓤) of D
    ρ = r , s , rs

    Ω¬¬-is-small : Ω¬¬ 𝓤 is 𝓤 small
    Ω¬¬-is-small = small-retracts ρ (native-size D)

\end{code}

A special case of the above is the following, which says that no type
in the first universe 𝓤₀ can be injective as soon as it has two
distinct points, other than in models that validate Ω¬¬ 𝓤₀ resizing
(in which Ω¬¬ 𝓤₀, being a retract of Ω 𝓤₀, is injective).

\begin{code}

small₀-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing
 : retracts-of-small-types-are-small
 → (D : 𝓤₀ ̇ )
 → ainjective-type D 𝓤₀ 𝓤₀
 → has-two-distinct-points D
 → Ω¬¬ 𝓤₀ is 𝓤₀ small
small₀-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing =
 small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing

\end{code}

Of course, making the universe parameters for the injectivity of D
bigger doesn't help:

\begin{code}

small₁-ainjective-types-with-two-distinct-points-gives-Ω¬¬-resizing
 : retracts-of-small-types-are-small
 → (D : 𝓤₀ ̇ )
 → ainjective-type D 𝓥 𝓦
 → has-two-distinct-points D
 → Ω¬¬ 𝓤₀ is 𝓤₀ small
small₁-ainjective-types-with-two-distinct-points-gives-Ω¬¬-resizing =
 small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing

\end{code}

Question. Can the homotopy circle S¹ be injective, for some choice of
universe parameter, without assuming excluded middle or resizing? If
not, can any other connected type in the first universe 𝓤₀, possibly
assuming higher-inductive types, be injective without classical or
resizing assumptions?

The above also shows that e.g. the result that

  ainjective-type (𝓤 ̇ ) 𝓤 𝓤

is tight. If we increase the first occurrence of 𝓤 to 𝓤 ⁺ then we get
Ω¬¬-resizing.

The second occurrence is not important, because we always have

 ainjective-type D (𝓤 ⊔ 𝓣) 𝓥 → ainjective-type D 𝓤 𝓣,

and in particular e.g.

  ainjective-type (𝓤 ̇ ) (𝓤 ⁺) 𝓥 → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺).

\begin{code}

module Ω¬¬-resizing-examples
        (small-retracts : retracts-of-small-types-are-small)
       where

 open import Iterative.Multisets
 open import Iterative.Multisets-Addendum ua
 open import Iterative.Sets ua
 open import Iterative.Sets-Addendum ua
 open import Ordinals.Arithmetic fe
 open import Ordinals.Injectivity
 open import Ordinals.Type

 recall-𝓤-ainjective : ainjective-type (𝓤  ̇ ) 𝓤 𝓤
 recall-𝓤-ainjective = universes-are-ainjective-Π

 recall-ainjective-resizing : (D : 𝓦 ̇)
                            → ainjective-type D (𝓤 ⊔ 𝓣) 𝓥
                            → ainjective-type D 𝓤 𝓣
 recall-ainjective-resizing = ainjective-resizing₁

 𝓤-ainjective-resizing : ainjective-type (𝓤 ̇ ) (𝓤 ⁺) 𝓥
                       → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺)
 𝓤-ainjective-resizing = ainjective-resizing₁ _

 𝓤-example : ainjective-type (𝓤 ̇ ) (𝓤 ⁺ ⊔ 𝓥) 𝓦
           → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 𝓤-example {𝓤} {𝓥} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓥} {𝓦}
   small-retracts
   (𝓤 ̇ )
   ainj
   ((𝟘 {𝓤} , 𝟙 {𝓤}) , 𝟘-is-not-𝟙)

 𝓤-example₀ : ainjective-type (𝓤 ̇ ) (𝓤 ⁺) 𝓦
            → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 𝓤-example₀ {𝓤} {𝓦} = 𝓤-example {𝓤} {𝓢} {𝓦}
  where
   𝓢 = 𝓤
   -- 𝓢 = 𝓤₀   -- also works
   -- 𝓢 = 𝓤 ⁺  -- also works

 recall-Ω-ainjective : ainjective-type (Ω 𝓤) 𝓤 𝓤
 recall-Ω-ainjective = Ω-ainjective

 Ω-example : ainjective-type (Ω 𝓤) (𝓤 ⁺) 𝓦
           → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 Ω-example {𝓤} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓤} {𝓦}
   small-retracts
   (Ω 𝓤)
   ainj
   ((⊥ , ⊤) , ⊥-is-not-⊤)

 Ω¬¬-ainjective : ainjective-type (Ω¬¬ 𝓤) 𝓤 𝓤
 Ω¬¬-ainjective {𝓤} = retract-of-ainjective (Ω¬¬ 𝓤) (Ω 𝓤)
                       Ω-ainjective
                       (Ω¬¬-is-retract-of-Ω fe' pe')

 Ω¬¬-example : ainjective-type (Ω¬¬ 𝓤) (𝓤 ⁺) 𝓦
             → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 Ω¬¬-example {𝓤} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓤} {𝓦}
   small-retracts
   (Ω¬¬ 𝓤)
   ainj
   ((⊥Ω¬¬ , ⊤Ω¬¬) , ⊥Ω¬¬-is-not-⊤Ω¬¬)

 recall-Ordinal-ainjective : ainjective-type (Ordinal 𝓤) 𝓤 𝓤
 recall-Ordinal-ainjective = ordinals-injectivity.Ordinal-is-ainjective fe (ua _)

 Ordinal-example : ainjective-type (Ordinal 𝓤) (𝓤 ⁺) 𝓦
                 → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 Ordinal-example {𝓤} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓤} {𝓦}
   small-retracts
   (Ordinal 𝓤)
   ainj
   ((𝟘ₒ , 𝟙ₒ) , 𝟘ₒ-is-not-𝟙ₒ)

 recall-Multisets-ainjective : ainjective-type (𝕄 𝓤) 𝓤 𝓤
 recall-Multisets-ainjective {𝓤} = 𝕄-is-ainjective 𝓤

 Multiset-example : ainjective-type (𝕄 𝓤) (𝓤 ⁺) 𝓦
                  → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 Multiset-example {𝓤} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓤} {𝓦}
   small-retracts
   (𝕄 𝓤)
   ainj
   ((𝟘ᴹ 𝓤 , 𝟙ᴹ 𝓤) , 𝟘ᴹ-is-not-𝟙ᴹ 𝓤)

 recall-Iterative-sets-ainjective : Set-Replacement pt → ainjective-type (𝕍 𝓤) 𝓤 𝓤
 recall-Iterative-sets-ainjective {𝓤} = 𝕍-is-ainjective 𝓤 pt

 Iterative-set-example : ainjective-type (𝕍 𝓤) (𝓤 ⁺) 𝓦
                       → Ω¬¬ (𝓤 ⁺) is 𝓤 ⁺ small
 Iterative-set-example {𝓤} {𝓦} ainj =
  small-ainjective-type-with-two-distinct-points-gives-Ω¬¬-resizing {𝓤 ⁺} {𝓤} {𝓦}
   small-retracts
   (𝕍 𝓤)
   ainj
   ((𝟘ⱽ 𝓤 , 𝟙ⱽ 𝓤) , 𝟘ⱽ-is-not-𝟙ⱽ 𝓤)

\end{code}

TODO. The type of monoids is injective (InjectiveTypes.MathematicalStructures).
We get the same resizing conclusion as above by considering the
monoids freely generated by the types 𝟘 and 𝟙 respectively (singleton
monoid and monoid of natural numbers).
