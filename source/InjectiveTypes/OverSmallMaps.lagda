Martin Escardo, August 2023

More about injectivity.

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
  f (pr₁ w)                               ＝⟨ refl ⟩
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

ainjectivity-over-small-maps : {𝓤 𝓥 𝓦 𝓣₀ 𝓣₁ 𝓣₂ : Universe}
                             → (D : 𝓦 ̇ )
                             → ainjective-type D (𝓣₀ ⊔ 𝓣₁) 𝓣₂
                             → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                               (j : X → Y)
                             → is-embedding j
                             → j is 𝓣₀ small-map
                             → (f : X → D) → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f
ainjectivity-over-small-maps {𝓤} {𝓥} {𝓦} {𝓣₀} {𝓣₁} {𝓣₂} D D-ainj =
 aflabbiness-gives-injectivity-over-small-maps D
  (aflabbiness-resizing₁ {𝓦} {𝓣₀} {𝓣₁} D (ainjective-types-are-aflabby D D-ainj))

\end{code}

Added by Martin Escardo and Tom de Jong 24th October 2024. As an
application of the above, we get the following version of
embedding-retract from InjectiveTypes/Blackboard with better universe
levels.

\begin{code}

open import UF.Retracts

embedding-retract' : {𝓤 𝓥 𝓦 𝓣 𝓣' : Universe}
                   → (D : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (j : D → Y)
                   → is-embedding j
                   → j is 𝓣 small-map
                   → ainjective-type D (𝓣 ⊔ 𝓣') 𝓦
                   → retract D of Y
embedding-retract' {𝓤} {𝓥} {𝓦} {𝓣} {𝓣'} D Y j e s i = pr₁ a , j , pr₂ a
 where
  a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ id
  a = ainjectivity-over-small-maps {𝓤} {𝓥} {𝓤} {𝓣} {𝓣'} {𝓦} D i j e s id

\end{code}

Added by Martin Escardo and Tom de Jong 7th November 2024. We now
improve the universe levels of the module ainjectivity-of-Lifting in
the file BlackBoard.

\begin{code}

open import UF.Univalence

module ainjectivity-of-Lifting'
        (𝓣 : Universe)
        (ua : is-univalent 𝓣)
       where

 private
  pe : propext 𝓣
  pe = univalence-gives-propext ua

 open ainjectivity-of-Lifting 𝓣

 open import Lifting.UnivalentPrecategory 𝓣
 open import UF.UA-FunExt
 open import UF.EquivalenceExamples

 η-is-small-map : {X : 𝓤 ̇ } → (η ∶ (X → 𝓛 X)) is 𝓣 small-map
 η-is-small-map {𝓤} {X} l = is-defined l ,
                            ≃-sym (η-fiber-same-as-is-defined X pe fe' fe' fe' l)

 ainjective-is-retract-of-free-𝓛-algebra' : (D : 𝓤 ̇ )
                                          → ainjective-type D (𝓣 ⊔ 𝓥) 𝓦
                                          → retract D of (𝓛 D)
 ainjective-is-retract-of-free-𝓛-algebra' {𝓤} {𝓥} {𝓦} D =
  embedding-retract' {𝓤} {𝓣 ⁺ ⊔ 𝓤} {𝓦} {𝓣} {𝓥} D (𝓛 D) η
   (η-is-embedding' 𝓤 D ua fe')
   η-is-small-map

 ainjectives-in-terms-of-free-𝓛-algebras'
  : (D : 𝓤 ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X))
 ainjectives-in-terms-of-free-𝓛-algebras' {𝓤} D = a , b
  where
   a : ainjective-type D 𝓣 𝓣 → Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)
   a i = D , ainjective-is-retract-of-free-𝓛-algebra' {𝓤} {𝓣} {𝓣} D i

   b : (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)) → ainjective-type D 𝓣 𝓣
   b (X , r) = retract-of-ainjective D (𝓛 X) (free-𝓛-algebra-ainjective ua X) r

\end{code}

A particular case of interest that arises in practice is the following.

\begin{code}

 ainjectives-in-terms-of-free-𝓛-algebras⁺
  : (D : 𝓣 ⁺ ̇ ) → ainjective-type D 𝓣 𝓣 ↔ (Σ X ꞉ 𝓣 ⁺ ̇ , retract D of (𝓛 X))
 ainjectives-in-terms-of-free-𝓛-algebras⁺ =  ainjectives-in-terms-of-free-𝓛-algebras'

 _ : {X : 𝓣 ⁺ ̇ } → type-of (𝓛 X) ＝ 𝓣 ⁺ ̇
 _ = refl

\end{code}
