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

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

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

 necessary-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓥 ⊔ 𝓦) 𝓣
  → Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d)
 necessary-condition-for-injectivity-of-subtype {𝓦} {𝓣} Σ-ainj = f , g , h
  where
   ρ : retract Σ P of D
   ρ = embedding-retract' 𝓦
        (Σ P)
        D
        s
        (pr₁-is-embedding P-is-prop-valued)
        pr₁-is-small-map
        Σ-ainj

   r : D → Σ P
   r = retraction ρ

   _ : s ＝ section ρ
   _ = refl

   rs : r ∘ s ∼ id
   rs = retract-condition ρ

   f : D → D
   f = s ∘ r

   g : (d : D) → P (f d)
   g d = pr₂ (r d)

   fg : (d : D) (p : P d) → (f d , g d) ＝ (d , p)
   fg d p = f d , g d     ＝⟨ refl ⟩
            r (s (d , p)) ＝⟨ rs (d , p) ⟩
            (d , p)       ∎

   h : (d : D) → P d → f d ＝ d
   h d p = ap s (fg d p)

 sufficient-condition-for-injectivity-of-subtype
  : ainjective-type D 𝓦 𝓣
  →  (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
  → ainjective-type (Σ P) 𝓦 𝓣
 sufficient-condition-for-injectivity-of-subtype D-ainj (f , g , h)
  = retract-of-ainjective (Σ P) D D-ainj (r , s , rs)
  where
   r : D → Σ P
   r d = f d , g d

   rs : r ∘ s ∼ id
   rs (d , p) = r (s (d , p)) ＝⟨ refl ⟩
                r d           ＝⟨ refl ⟩
                f d , g d     ＝⟨ to-subtype-＝ P-is-prop-valued (h d p) ⟩
                d , p         ∎

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
  ↔ (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
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
  ↔ (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
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

Added 24 July 2025 by Tom de Jong.

In InjectiveTypes.InhabitedTypesTaboo we showed that the type of nonempty types
is injective by exhibiting it as a retract of the universe. Here is an
alternative proof, using that
   (Π (p : P) , ¬¬ A p)   →   ¬¬ Π (p : P) , A p
is provable when P is a proposition.

\begin{code}

open import UF.PropTrunc
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Univalence

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 Nonempty-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Nonempty-type 𝓤 = Σ X ꞉ 𝓤 ̇ , is-nonempty X

 ainjectivity-of-type-of-nonempty-types : is-univalent 𝓤 → ainjective-type (Nonempty-type 𝓤) 𝓤 𝓤
 ainjectivity-of-type-of-nonempty-types {𝓤} ua = II
  where
   f : 𝓤 ̇  → 𝓤 ̇
   f X = ¬¬ X → X
   I-f : (X : 𝓤 ̇ ) → is-nonempty (f X)
   I-f X = double-negation-elimination-inside-double-negation X
   II-f : (X : 𝓤 ̇ ) → is-nonempty X → f X ＝ X
   II-f X X-non-empty = eqtoid ua (f X) X e
    where
     e = (¬¬ X → X) ≃⟨ I ⟩
         (𝟙{𝓤} → X) ≃⟨ ≃-sym (𝟙→ fe') ⟩
         X          ■
      where
       I = →cong'' fe' fe' (idtoeq (¬¬ X) 𝟙 II)
        where
         II : ¬¬ X ＝ 𝟙
         II = holds-gives-equal-𝟙 (univalence-gives-propext ua) (¬¬ X) (negations-are-props fe') X-non-empty

   I : ainjective-type (Nonempty-type 𝓤) 𝓤 𝓤
     ↔ (Σ f ꞉ (𝓤 ̇  → 𝓤 ̇ ) , ((X : 𝓤 ̇ ) → is-nonempty (f X))
                                        × ((X : 𝓤 ̇ ) → is-nonempty X → f X ＝ X))
   I = necessary-and-sufficient-condition-for-injectivity-of-subtype-single-universe
          (𝓤 ̇ )
          is-nonempty
          (λ _ → negations-are-props (fe _ _))
          (universes-are-ainjective ua)
   II : ainjective-type (Nonempty-type 𝓤) 𝓤 𝓤
   II = rl-implication I (f , I-f , II-f)


\end{code}