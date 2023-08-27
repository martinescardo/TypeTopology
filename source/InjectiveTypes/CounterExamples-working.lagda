Martin Escardo, 23rd August 2023.

Some counterexamples to injectivity.

We already know that if excluded middle holds then all pointed types
are algebraicly injective, and that the converse also holds.

So we can't really give an example of any type which is not
algebraicly injective, other than the empty type. The best we can hope
is to derive a constructive taboo, rather than a contradiction, from
the assumption that a type of interest would be injective.

Most types one encounters in practice are "not" injective in the above
sense.

NB. We work with the assumption of algebraic injectivity, rather than
its truncated version (injectivity), but this doesn't matter because
most of our conclusions are propositions, and when they are not we can
consider their truncations, which are also constructive taboos.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

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

\end{code}

Added 25th August 2023. Join work of Martin Escardo with Tom de
Jong. The remaining hole is easy to fill, but it requires some
labour. This is a blackboard development for the moment.

The idea is that there are should be no small injective types.

The following is true, by a result of de Jong and Escardo (using a
result of Shulman), but we haven't ptoved it in TypeTopology yet, and
so we assume it as a hypothesis.

\begin{code}

open import UF.Size

retracts-of-small-types-are-small : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇
retracts-of-small-types-are-small {𝓤} {𝓥} {𝓦} =
   {X : 𝓤 ̇ }
 → {Y : 𝓥 ̇ }
 → retract Y of X
 → X is 𝓦 small
 → Y is 𝓦 small

open import InjectiveTypes.OverSmallMaps fe
open import TypeTopology.DiscreteAndSeparated

small-injective-sets-with-two-distinct-points-gives-Ω¬¬-resizing
 : retracts-of-small-types-are-small
 → (D : 𝓤 ̇ )
 → ainjective-type D 𝓤 𝓥
 → has-two-distinct-points D
 → Ω¬¬ 𝓤 is 𝓤 small
small-injective-sets-with-two-distinct-points-gives-Ω¬¬-resizing
 {𝓤} {𝓥} small-retracts D D-ainj ((x₀ , x₁) , distinct) = II I
 where
  f : 𝟚 → D
  f ₀ = x₀
  f ₁ = x₁

  I : Σ s ꞉ (Ω¬¬ 𝓤 → D) , s ∘ 𝟚-to-Ω¬¬ ∼ f
  I = ainjectivity-over-small-maps {𝓤} {𝓤₀} {𝓤 ⁺} {𝓤} {𝓤} {𝓥}
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
    V 𝕡@(p , ¬¬-sep) e = V₃
     where
      V₀ : 𝕡 ＝ ⊥Ω¬¬ → s 𝕡 ＝ x₀
      V₀ e = transport⁻¹ (λ - → s - ＝ x₀) e III
      V₁ : 𝕡 ≠ ⊥Ω¬¬
      V₁ = contrapositive V₀ e
      V₂ : ¬¬ (p holds)
      V₂ u = V₁ (to-subtype-＝
                  (λ p → being-¬¬-stable-is-prop fe' (holds-is-prop p))
                  (fails-gives-equal-⊥ pe' fe' p u))
      V₃ : p holds
      V₃ = ¬¬-sep V₂

    VI  : (𝕡 : Ω¬¬ 𝓤) → pr₁ 𝕡 holds → s 𝕡 ≠ x₀
    VI 𝕡@(p , ¬¬sep) h = VI₃
     where
      VI₀ : p ＝ ⊤Ω
      VI₀ = holds-gives-equal-⊤ pe' fe' p h
      VI₁ : 𝕡 ＝ ⊤Ω¬¬
      VI₁ = to-subtype-＝ (λ p → being-¬¬-stable-is-prop fe' (holds-is-prop p)) VI₀
      VI₂ : s 𝕡 ＝ x₁
      VI₂ = transport⁻¹ (λ - → s - ＝ x₁) VI₁ IV
      VI₃ : s 𝕡 ≠ x₀
      VI₃ e = distinct
               (x₀  ＝⟨ e ⁻¹ ⟩
                s 𝕡 ＝⟨ VI₂ ⟩
                x₁  ∎)

    VII : (𝕡 : Ω¬¬ 𝓤) → (s 𝕡 ≠ x₀) ＝ (pr₁ 𝕡 holds)
    VII 𝕡@(p , ¬¬sep) = pe' (negations-are-props fe')
                            (holds-is-prop p)
                            (V 𝕡)
                            (VI 𝕡)
    r : D → Ω¬¬ 𝓤
    r d = ((d ≠ x₀) , negations-are-props fe') , ¬-is-¬¬-stable

    rs : r ∘ s ∼ id
    rs p = r (s p)              ＝⟨ refl ⟩
           ((s p ≠ x₀) , _) , _ ＝⟨ rs₀ ⟩
           p                     ∎
         where
          rs₀ = to-subtype-＝
                 (λ p → being-¬¬-stable-is-prop fe' (holds-is-prop p))
                 (to-subtype-＝ (λ _ → being-prop-is-prop fe') (VII p))

    ρ : retract (Ω¬¬ 𝓤) of D
    ρ = r , s , rs

    Ω¬¬-is-small : Ω¬¬ 𝓤 is 𝓤 small
    Ω¬¬-is-small = small-retracts ρ (native-size D)

\end{code}

The above shows that e.g. the result that

  ainjective-type (𝓤 ̇ ) 𝓤 𝓤

is sharp.

If we increase the first occurrence of 𝓤 to 𝓤 ⁺ then we get Ω¬¬-resizing.

The second occurrence is not important, because we always have

 ainjective-type D (𝓤 ⊔ 𝓣) 𝓥 → ainjective-type D 𝓤 𝓣,

and in particular e.g.

  ainjective-type (𝓤 ̇ ) (𝓤 ⁺) 𝓥 → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺).

\begin{code}

example : retracts-of-small-types-are-small
        → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) (𝓤 ⁺ ⁺)
        → Ω¬¬ (𝓤 ⁺) is (𝓤 ⁺) small
example {𝓤} small-retracts ainj =
 small-injective-sets-with-two-distinct-points-gives-Ω¬¬-resizing
  small-retracts
  (𝓤 ̇ )
  ainj
  ((𝟘 , 𝟙) , 𝟘-is-not-𝟙)

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
