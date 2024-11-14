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

TODO. Can the above logical equivalences be made into a type
equivalences?
