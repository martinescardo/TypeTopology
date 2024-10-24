Martin Escardo, 21st October 2024

A necessary and sufficient condition for the injectivity of a subtype
of an injective type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.Subtypes
        (fe : FunExt)
       where

open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Retracts
open import UF.Subsingletons
open import UF.UA-FunExt

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
       where

 necessary-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓤 ⊔ 𝓥) 𝓤
  → Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d)
 necessary-condition-for-injectivity-of-subtype Σ-ainj = f , g , h
  where
   ρ : retract Σ P of D
   ρ = embedding-retract (Σ P) D pr₁ (pr₁-is-embedding P-is-prop-valued) Σ-ainj

   r : D → Σ P
   r = retraction ρ

   s : Σ P → D
   s = section ρ

   _ : s ＝ pr₁
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
   h d p = ap pr₁ (fg d p)

 sufficient-condition-for-injectivity-of-subtype
  : ainjective-type D 𝓦 𝓣
  →  (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
  → ainjective-type (Σ P) 𝓦 𝓣
 sufficient-condition-for-injectivity-of-subtype D-ainj (f , g , h)
  = retract-of-ainjective (Σ P) D D-ainj (r , s , rs)
  where
   r : D → Σ P
   r d = f d , g d

   s : Σ P → D
   s = pr₁

   rs : r ∘ s ∼ id
   rs (d , p) = r (s (d , p)) ＝⟨ refl ⟩
                r d           ＝⟨ refl ⟩
                f d , g d     ＝⟨ to-subtype-＝ P-is-prop-valued (h d p) ⟩
                d , p         ∎

 change-subtype-injectivity-universes
  : ainjective-type D 𝓦 𝓣
  → ainjective-type (Σ P) (𝓤 ⊔ 𝓥) 𝓤
  → ainjective-type (Σ P) 𝓦 𝓣
 change-subtype-injectivity-universes D-ainj Σ-ainj
  = sufficient-condition-for-injectivity-of-subtype D-ainj
     (necessary-condition-for-injectivity-of-subtype Σ-ainj)

\end{code}

The following choice of universes makes the condition truly
sufficient and necessary.

\begin{code}

module _ (D : 𝓤 ̇ )
         (P : D → 𝓥 ̇ )
         (P-is-prop-valued : (d : D) → is-prop (P d))
         (D-ainj : ainjective-type D (𝓤 ⊔ 𝓥) 𝓤)
       where

 necessary-and-sufficient-condition-for-injectivity-of-subtype
  : ainjective-type (Σ P) (𝓤 ⊔ 𝓥) 𝓤
  ↔ (Σ f ꞉ (D → D) , ((d : D) → P (f d)) × ((d : D) → P d → f d ＝ d))
 necessary-and-sufficient-condition-for-injectivity-of-subtype
  = necessary-condition-for-injectivity-of-subtype D P P-is-prop-valued ,
    sufficient-condition-for-injectivity-of-subtype D P P-is-prop-valued D-ainj

\end{code}

TODO. Can the above logical equivalence be made into a type
equivalence?

\begin{code}

open import UF.Univalence

module _ (𝓤 : Universe)
         (ua : is-univalent 𝓤)
       where

 open import InjectiveTypes.InhabitedTypesTaboo {!!} {!!} 𝓤
 open import UF.Subsingletons-FunExt

 Non-Empty-is-injective' : ainjective-type Non-Empty {!!} {!!}
 Non-Empty-is-injective' =
  sufficient-condition-for-injectivity-of-subtype
   (𝓤 ̇)
   is-nonempty
   (λ X → negations-are-props (fe 𝓤 𝓤₀))
   (universes-are-ainjective ua)
   ((λ X → ¬¬ X → X) ,
    double-negation-elimination-inside-double-negation ,
    (λ X → {!!}))

\end{code}
