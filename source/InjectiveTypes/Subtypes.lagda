Martin Escardo, 21st October 2024

A necessary and sufficient condition for the injectivity of a subtype
of an injective type.

Modified by Martin Escardo and Tom de Jong 31st October 2024 to
improve the universe levels.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.Subtypes
        (fe : FunExt)
       where

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.OverSmallMaps fe
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
       where

 private
  s : Σ P → D
  s = pr₁

 endomap-with-values-and-fixed-point-conditions : 𝓤 ⊔ 𝓥 ̇
 endomap-with-values-and-fixed-point-conditions =
  Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d)

 canonical-embedding-has-retraction-reformulation
  : has-retraction s ↔ endomap-with-values-and-fixed-point-conditions
 canonical-embedding-has-retraction-reformulation = I , II
  where
   I : has-retraction s → endomap-with-values-and-fixed-point-conditions
   I (r , ρ) = f , I₁ , I₂
    where
     f : D → D
     f = s ∘ r
     I₁ : (d : D) → P (s (r d))
     I₁ d = pr₂ (r d)
     I₂ : (d : D) → P d → s (r d) ＝ d
     I₂ d p = ap pr₁ (ρ (d , p))
   II : endomap-with-values-and-fixed-point-conditions → has-retraction s
   II (f , f-I , f-II) = r , ρ
    where
     r : D → Σ P
     r d = (f d , f-I d)
     ρ : r ∘ s ∼ id
     ρ (d , p) = to-subtype-＝ P-is-prop-valued (f-II d p)

 subtype-retract-if-endomap-with-values-and-fixed-point-conditions
  : endomap-with-values-and-fixed-point-conditions
  → retract (Σ P) of D
 subtype-retract-if-endomap-with-values-and-fixed-point-conditions h
  = (pr₁ I , s , pr₂ I)
   where
    I : has-retraction s
    I = rl-implication canonical-embedding-has-retraction-reformulation h

 canonical-embedding-has-retraction-if-subtype-is-ainjective
  : ainjective-type (Σ P) (𝓥 ⊔ 𝓦) 𝓣
  → has-retraction s
 canonical-embedding-has-retraction-if-subtype-is-ainjective {𝓦} {𝓣} Σ-ainj
  = (retraction ρ , retract-condition ρ)
   where
    ρ : retract Σ P of D
    ρ = embedding-retract' 𝓦
         (Σ P)
         D
         s
         (pr₁-is-embedding P-is-prop-valued)
         pr₁-is-small-map
         Σ-ainj

    _ : s ＝ section ρ
    _ = refl

 ainjective-subtype-if-retract : ainjective-type D 𝓦 𝓣
                               → retract (Σ P) of D
                               → ainjective-type (Σ P) 𝓦 𝓣
 ainjective-subtype-if-retract = retract-of-ainjective (Σ P) D

 necessary-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓥 ⊔ 𝓦) 𝓣
  → endomap-with-values-and-fixed-point-conditions
 necessary-condition-for-injectivity-of-subtype {𝓦} {𝓣} =
    lr-implication canonical-embedding-has-retraction-reformulation
  ∘ canonical-embedding-has-retraction-if-subtype-is-ainjective {𝓦} {𝓣}

 sufficient-condition-for-injectivity-of-subtype
  : ainjective-type D 𝓦 𝓣
  → endomap-with-values-and-fixed-point-conditions
  → ainjective-type (Σ P) 𝓦 𝓣
 sufficient-condition-for-injectivity-of-subtype D-ainj
  = ainjective-subtype-if-retract D-ainj
    ∘ subtype-retract-if-endomap-with-values-and-fixed-point-conditions

\end{code}

By composing the necessary and sufficient conditions, we get the
following resizing theorem as a corollary.

\begin{code}

 subtype-injectivity-resizing
  : ({𝓦 𝓣 𝓣'} 𝓥' : Universe)
  → ainjective-type D 𝓦 𝓣
  → ainjective-type (Σ P) (𝓥 ⊔ 𝓥') 𝓣'
  → ainjective-type (Σ P) 𝓦 𝓣
 subtype-injectivity-resizing 𝓥' D-ainj Σ-ainj
  = sufficient-condition-for-injectivity-of-subtype D-ainj
     (necessary-condition-for-injectivity-of-subtype {𝓥'} Σ-ainj)

\end{code}

The following choice of universes makes the condition truly
sufficient and necessary.

\begin{code}

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
         (D-ainj : ainjective-type D (𝓥 ⊔ 𝓦) 𝓣)
       where

 necessary-and-sufficient-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓥 ⊔ 𝓦) 𝓣
  ↔ endomap-with-values-and-fixed-point-conditions D P P-is-prop-valued
 necessary-and-sufficient-condition-for-injectivity-of-subtype
  = necessary-condition-for-injectivity-of-subtype D P P-is-prop-valued {𝓦} ,
    sufficient-condition-for-injectivity-of-subtype D P P-is-prop-valued D-ainj

\end{code}

Because there are no small injective types unless Ω¬¬-resizing holds,
the following particular case is of interest.

\begin{code}

module _ (D : 𝓤 ⁺ ̇ )
         (P : D → 𝓤 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
         (D-ainj : ainjective-type D 𝓤 𝓤)
       where

 necessary-and-sufficient-condition-for-injectivity-of-subtype-single-universe
  : ainjective-type (Σ P) 𝓤 𝓤
  ↔ endomap-with-values-and-fixed-point-conditions D P P-is-prop-valued
 necessary-and-sufficient-condition-for-injectivity-of-subtype-single-universe
  = necessary-and-sufficient-condition-for-injectivity-of-subtype
     {𝓤 ⁺} {𝓤} {𝓤} {𝓤}
     D
     P
     P-is-prop-valued
     D-ainj

\end{code}

Can the above logical equivalences be made into type equivalences?

No, at least not with the functions given to prove each implication.

Example. The injectivity structure on Ω induces the following endofunction f of the universe.

\begin{code}

open import UF.Subsingletons-FunExt

module example (pe : propext 𝓤) (X : 𝓤 ̇ ) where

 f : 𝓤 ̇ → 𝓤 ̇
 f = pr₁ (necessary-condition-for-injectivity-of-subtype
           {𝓤 ⁺} {𝓤}
           (𝓤 ̇)
           is-prop
           (λ _ → being-prop-is-prop (fe 𝓤 𝓤))
           {𝓤} {𝓤}
           (Ω-ainjective pe))

 _ : f X ＝ ((is-prop X × (⋆ ＝ ⋆)) × (⋆ ＝ ⋆) → X)
 _ = refl

\end{code}

So f X ≃ (is-prop X → X), because (⋆ ＝ ⋆) ≃ 𝟙 as 𝟙 is a set.

On the other hand, another construction that Ω 𝓤 is injective is to
start with the injectivity of 𝓤 and f := propositional truncation.

But clearly we don't have that ∥ X ∥ ≃ (is-prop X → X).

TODO. Maybe complete the formalization of the example, but I am not
sure it is worth it.
