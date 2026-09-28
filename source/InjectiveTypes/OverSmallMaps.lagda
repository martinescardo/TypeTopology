Martin Escardo, August 2023

Algebraic injectivity over small maps.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.OverSmallMaps (fe : FunExt) where

open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Size
open import UF.Subsingletons

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

Added 3rd August 2023. Extensions over small embeddings induced by
algebraic flabbiness. The point is to reduce size without resizing
axioms. An application is in Taboos.Decomposability.

\begin{code}

module _ (D : 𝓦 ̇ )
         (D-is-flabby : aflabby D 𝓣)
         {X : 𝓤 ̇ }
         {Y : 𝓥 ̇ }
         (j : X → Y)
         (j-is-embedding : is-embedding j)
         (j-small : j is 𝓣 small-map)
         (f : X → D)
       where

 private
  R : Y → 𝓣 ̇
  R y = resized (fiber j y) (j-small y)

  ρ : (y : Y) → R y ≃ fiber j y
  ρ y = resizing-condition (j-small y)

  R-is-prop : (y : Y) → is-prop (R y)
  R-is-prop y = equiv-to-prop (ρ y) (j-is-embedding y)

  e : (y : Y) → Σ d ꞉ D , ((r : R y) → d ＝ f (pr₁ (⌜ ρ y ⌝ r)))
  e y = D-is-flabby (R y) (R-is-prop y) (λ r → f (pr₁ (⌜ ρ y ⌝ r)))

 sflabby-extension : (Y → D)
 sflabby-extension y = pr₁ (e y)

 sflabby-extension-property : sflabby-extension ∘ j ∼ f
 sflabby-extension-property x =
  sflabby-extension (j x)                 ＝⟨ I ⟩
  f (pr₁ (⌜ ρ (j x) ⌝ (⌜ ρ (j x) ⌝⁻¹ w))) ＝⟨ II ⟩
  f (pr₁ w)                               ＝⟨refl⟩
  f x                                     ∎
  where
   w : fiber j (j x)
   w = x , refl

   I  = pr₂ (e (j x)) (⌜ ρ (j x) ⌝⁻¹ w)
   II = ap (f ∘ pr₁) (≃-sym-is-rinv (ρ (j x)) w)

 aflabbiness-gives-injectivity-over-small-maps : Σ f' ꞉ (Y → D) , f' ∘ j ∼ f
 aflabbiness-gives-injectivity-over-small-maps = sflabby-extension ,
                                                 sflabby-extension-property
\end{code}

An extension property for injective types, with more general universes
and less general embeddings.

\begin{code}

ainjectivity-over-small-maps : {𝓤 𝓥 𝓦 𝓣₀ 𝓣₂ : Universe}
                             → (𝓣₁ : Universe)
                             → (D : 𝓦 ̇ )
                             → ainjective-type D (𝓣₀ ⊔ 𝓣₁) 𝓣₂
                             → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                               (j : X → Y)
                             → is-embedding j
                             → j is 𝓣₀ small-map
                             → (f : X → D) → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f
ainjectivity-over-small-maps {𝓤} {𝓥} {𝓦} {𝓣₀} {𝓣₂} 𝓣₁ D D-ainj =
 aflabbiness-gives-injectivity-over-small-maps D
  (aflabbiness-resizing₁ {𝓦} {𝓣₀} {𝓣₁} D (ainjective-types-are-aflabby D D-ainj))

\end{code}

Added by Martin Escardo and Tom de Jong 24th October 2024. This
improves the universe levels of InjectiveTypes.Blackboard.embedding-retract.

\begin{code}

open import UF.Retracts

embedding-retract' : {𝓤 𝓥 𝓦 𝓣 : Universe}
                   → (𝓣' : Universe)
                   → (D : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (j : D → Y)
                   → is-embedding j
                   → j is 𝓣 small-map
                   → ainjective-type D (𝓣 ⊔ 𝓣') 𝓦
                   → retract D of Y
embedding-retract' 𝓣' D Y j e s i = pr₁ a , j , pr₂ a
 where
  a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ id
  a = ainjectivity-over-small-maps 𝓣' D i j e s id

\end{code}
