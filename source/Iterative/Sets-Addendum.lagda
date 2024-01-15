Martin Escardo & Tom de Jong, July 2023.

Some constructions with iterative sets.

 * The type of iterative sets is large.

 * The type of iterative sets is algebraically injective.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Sets-Addendum
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import Taboos.Decomposability ua
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import W.Type

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

𝟘ⱽ : 𝕍
𝟘ⱽ = 𝟘ᴹ , 𝟘ᴹ-is-iset

𝟙ⱽ : 𝕍
𝟙ⱽ = 𝟙ᴹ , 𝟙ᴹ-is-iset

𝟘ⱽ-is-not-𝟙ⱽ : 𝟘ⱽ ≠ 𝟙ⱽ
𝟘ⱽ-is-not-𝟙ⱽ p = 𝟘ᴹ-is-not-𝟙ᴹ (ap underlying-mset p)

\end{code}

Subsets.

\begin{code}

open import UF.Equiv
open import UF.Embeddings
open import UF.Subsingletons
open import UF.SubtypeClassifier

𝕍-separation : (A : 𝕍) (P : 𝕍 → Ω 𝓤)
             → Σ A' ꞉ 𝕍 , ((B : 𝕍) → (B ∈ A') ↔ (B ∈ A × P B holds))
𝕍-separation A@(ssup X φ , φ-emb , φ-iter) P = A' , Q
 where
  A' : 𝕍
  A' = (ssup (Σ x ꞉ X , P (φ x , φ-iter x) holds) (λ (x , p) → φ x)) ,
       ∘-is-embedding
        (pr₁-is-embedding (λ x → holds-is-prop (P (φ x , φ-iter x))))
        φ-emb ,
       (λ (x , p) → φ-iter x)

  Q→ : (B : 𝕍) → B ∈ A' → B ∈ A × P B holds
  Q→ B ((x , p) , refl) =
   (x , refl) , transport (_holds ∘ P) (to-subtype-＝ being-iset-is-prop refl) p

  Q← : (B : 𝕍) → B ∈ A × P B holds → B ∈ A'
  Q← B ((x , refl) , p) =
   (x , transport (_holds ∘ P) (to-subtype-＝ being-iset-is-prop refl) p) , refl

  Q : (B : 𝕍) → B ∈ A' ↔ (B ∈ A × P B holds)
  Q B = Q→ B ,  Q← B

subset : 𝕍 → (P : 𝕍 → Ω 𝓤) → 𝕍
subset A P = pr₁ (𝕍-separation A P)

subset-↔ : (A : 𝕍) (P : 𝕍 → Ω 𝓤)
         → (B : 𝕍) → (B ∈ subset A P) ↔ (B ∈ A × P B holds)
subset-↔ A P = pr₂ (𝕍-separation A P)

\end{code}

The type of multisets is large, in the sense that it doesn' have a
small copy.

\begin{code}

𝕍-is-large : is-large 𝕍
𝕍-is-large (X , 𝕗) = III
 where
  have-𝕗 : X ≃ 𝕍
  have-𝕗 = 𝕗

  private
   remark-X : 𝓤 ̇
   remark-X = X

   remark-𝕍 : 𝓤⁺ ̇
   remark-𝕍 = 𝕍

  A : 𝕍
  A = 𝕍-ssup X ⌜ 𝕗 ⌝ (equivs-are-embeddings' 𝕗)

  A-universal : (B : 𝕍) → B ∈ A
  A-universal B = ⌜ 𝕗 ⌝⁻¹ B , ap underlying-mset (inverses-are-sections' 𝕗 B)

  P : (B : 𝕍) → Ω 𝓤
  P B = ¬ (B ∈⁻ B) , negations-are-props fe

  R : 𝕍
  R = subset A P

  g : (B : 𝕍) → (B ∈ R) ↔ (B ∈ A × ¬ (B ∈⁻ B))
  g = subset-↔ A P

  h : (R ∈ R) ≃ (R ∈⁻ R)
  h = ∈⁻≃∈ R R

  I : R ∈⁻ R → ¬ (R ∈⁻ R)
  I i = pr₂ (lr-implication (g R) (⌜ h ⌝⁻¹ i))

  II : ¬ (R ∈⁻ R) → R ∈⁻ R
  II ν = ⌜ h ⌝ (rl-implication (g R) (A-universal R , ν))

  III : 𝟘
  III = not-equivalent-to-own-negation (I , II)

\end{code}

The type of iterative sets is algebraically injective, which is a new
result.

\begin{code}

open import InjectiveTypes.Blackboard fe'

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 𝕍-is-ainjective : ainjective-type 𝕍 𝓤 𝓤
 𝕍-is-ainjective = retract-of-ainjective 𝕍 𝕄 𝕄-is-ainjective 𝕍-is-retract-of-𝕄
  where
   open unions-of-iterative-sets pt sr

\end{code}

It follows that 𝕍 has no non-trivial decidable properties unless weak
excluded middle holds.

\begin{code}

 decomposition-of-𝕍-gives-WEM : decomposition 𝕍 → WEM 𝓤
 decomposition-of-𝕍-gives-WEM =
  decomposition-of-ainjective-type-gives-WEM
   𝕍
   𝕍-is-ainjective

\end{code}

The results of this file seem to be new.
