Martin Escardo, 23rd August 2023.

Some counterexamples to injectivity.

We already know that if excluded middle holds then all pointed types
are algebraically injective, and that the converse also holds.

So we can't really give an example of any type which is not
algebraically injective, other than the empty type. The best we can hope
is to derive a constructive taboo, rather than a contradiction, from
the assumption that a type of interest would be injective.

Most types one encounters in practice are "not" injective in the above
sense.

NB. We work with the assumption of algebraic injectivity, rather than
its truncated version (injectivity), but this doesn't matter because
most of our conclusions are propositions, and when they are not we can
consider their truncations, which are also constructive taboos.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.CounterExamples-working
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import Taboos.Decomposability ua
open import UF.Embeddings
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Miscelanea
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
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

open import InjectiveTypes.Blackboard fe
open import TypeTopology.SimpleTypes fe pt

open import InjectiveTypes.CounterExamples ua pt
open import UF.Size

recall-Ω-resizing-gives-propositional-resizing : Ω-resizing 𝓤 → propositional-resizing {!!} {!!}
recall-Ω-resizing-gives-propositional-resizing = {!!}

small-ainjective-types-with-two-distinct-points-gives-Ω-resizing
 : retracts-of-small-types-are-small
 → (D : 𝓤 ̇ )
   (x₀ x₁ : D)
 → x₀ ≠ x₁
 → ((x : D) → ¬¬-stable (x ＝ x₁))
 → ainjective-type D (𝓤 ⊔ 𝓥) 𝓦
 → Ω-resizing 𝓤
small-ainjective-types-with-two-distinct-points-gives-Ω-resizing
 {𝓤} {𝓥} {𝓦} small-retracts D x₀ x₁ distinct ¬¬-stable₁ D-ainj = {!!} -- II I
 where
  f : 𝟚 → D
  f ₀ = x₀
  f ₁ = x₁

  I : Σ s ꞉ (Ω 𝓤 → D) , s ∘ 𝟚-to-Ω ∼ f
  I = ainjectivity-over-small-maps {𝓤} {𝓤₀} {𝓤 ⁺} {𝓤} {𝓥} {𝓦}
       D
       D-ainj
       𝟚-to-Ω
       (𝟚-to-Ω-is-embedding fe' pe')
       (𝟚-to-Ω-is-small-map fe' pe')
       f

  II : type-of I → Ω 𝓤 is 𝓤 small
  II (s , extension-property) = {!!} -- Ω-is-small
   where
    III : s ⊥Ω ＝ x₀
    III = extension-property ₀

    IV : s ⊤Ω ＝ x₁
    IV = extension-property ₁

\end{code}

s p = ¬¬ p

s p ＝ s ⊤
¬¬ p = ⊥


\begin{code}

    V : (p : {!!}) → s p ＝ x₁ → p holds -- things break here!
    V p = {!!}

    VI : (p : {!!}) → p holds → s p ＝ x₁ -- this is fine and boring.
    VI p = {!!}

    r : D → Ω 𝓤
    r d = ¬¬ (d ＝ x₁) , negations-are-props fe'

    rs : r ∘ s ∼ id
    rs p = r (s p)              ＝⟨ refl ⟩
           (¬¬ (s p ＝ x₁) , _) ＝⟨ rs₀ ⟩
           (s p ＝ x₁) , _      ＝⟨ rs₁ ⟩
           p                    ∎
         where
          rs₀ = Ω-extensionality fe' pe' (¬¬-stable₁ (s p)) ¬¬-intro
          rs₁ = to-subtype-＝ (λ P → being-prop-is-prop fe') {!!}

    ρ : retract (Ω 𝓤) of D
    ρ = r , s , rs
{-
    Ω-is-small : Ω 𝓤 is 𝓤 small
    Ω-is-small = small-retracts ρ (native-size D)
-}



\end{code}

Conjecture. If every extension of f defined above along 𝟚-to-Ω is
left-cancellable, then a taboo holds. Yes: Just take D = Ω¬¬, which,
being a retract of Ω, is injective, because a possible extension is
double negation.

Let D be injective and assume that Ω is a retract of D.

Or just assume that we have a left cancellable map s : Ω → D such that
s ⊤ is h-isolated. This assumption holds for D=𝓤 or
iterative multisets, or iterative sets, or monoids.

Again define r : D → Ω to be r d := (d ＝ s ⊤)

r (s p) = (s p ＝ s ⊤)
        = (p ＝ ⊤)
        = p


(List P ≃ List Q) → P ≃ Q


\begin{code}

open import UF.UniverseEmbedding

remark : ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺ ⁺)
       → retract 𝓤 ̇ of (𝓤 ⁺ ̇)
remark {𝓤} ainj = ρ σ
 where
  σ : Σ r ꞉ (𝓤 ⁺ ̇ → 𝓤 ̇ ) , r ∘ Lift (𝓤 ⁺) ∼ id
  σ = ainj (Lift (𝓤 ⁺)) (Lift-is-embedding ua) id

  ρ : type-of σ → retract 𝓤 ̇ of (𝓤 ⁺ ̇)
  ρ (r , rs) = r , Lift (𝓤 ⁺) , rs

kramer : retract 𝓤 ̇ of (𝓤 ⁺ ̇)
       → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺)
kramer {𝓤} ρ =
 retract-of-ainjective (𝓤 ̇) (𝓤 ⁺ ̇) (universes-are-ainjective-Π (ua (𝓤 ⁺))) ρ

\end{code}

Notice that in InjectiveTypes.Article we prove that if propositional
resizing holds then 𝓤 is a retract of 𝓤⁺.

TODO. Show that if 𝓤 is a retract of 𝓤⁺ then propositional resizing
holds.

TODO. Think more about universe levels.
