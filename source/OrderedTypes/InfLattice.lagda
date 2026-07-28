Ian Ray. July 25 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module OrderedTypes.InfLattice
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
      where

open import MLTT.Spartan
open import UF.HedbergApplications
open import UF.Logic
open import UF.Sets
open import UF.SubtypeClassifier
open import Slice.Family hiding (_[_])
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open AllCombinators pt fe

\end{code}

We give the definition of an inf lattice.

\begin{code}

module Infs {A : 𝓤 ̇ } (_≤_ : A → A → Ω 𝓥) where

 _is-a-lower-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 l is-a-lower-bound-of (U , u) = Ɐ i ꞉ U , l ≤ u i

 lower-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 lower-bound U = Σ u ꞉ A , (u is-a-lower-bound-of U) holds

 _is-glb-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-glb-of U = (u is-a-lower-bound-of U)
               ∧ (Ɐ (u′ , _) ꞉ lower-bound U , (u′ ≤ u))

module _ (𝓤 𝓣 𝓥 : Universe) where

 inf-lattice-data : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ⊔ 𝓥 ⁺ ̇
 inf-lattice-data A = (A → A → Ω 𝓣) × (Fam 𝓥 A → A)

 is-inf-lattice : {A : 𝓤 ̇ } → inf-lattice-data A → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇
 is-inf-lattice {A} (_≤_ , ⋀_) = is-partial-order A _≤_ × infima
  where
   open Infs _≤_
   infima : 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
   infima = (U : Fam 𝓥 A) → ((⋀ U) is-glb-of U) holds

 inf-lattice-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣 ⁺ ̇
 inf-lattice-structure A = Σ d ꞉ (inf-lattice-data A) , is-inf-lattice d

 Inf-Lattice : (𝓤 ⊔ 𝓣 ⊔ 𝓥)⁺ ̇
 Inf-Lattice = Σ A ꞉ 𝓤 ̇ , inf-lattice-structure A

⟨_⟩ : Inf-Lattice 𝓤 𝓣 𝓥 → 𝓤 ̇
⟨ (L , _) ⟩ = L

order-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → (⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓣)
order-of (A , (_≤_ , ⋀_) , rest) = _≤_

syntax order-of L x y = x ≤⟨ L ⟩ y

inf-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
inf-of (A , (_≤_ , ⋀_) , rest) = ⋀_

syntax inf-of L U = ⋀⟨ L ⟩ U

partial-orderedness-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                       → is-partial-order ⟨ L ⟩ (order-of L)
partial-orderedness-of (A , (_≤_ , ⋁_) , order , is-glb-of) = order

reflexivity-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-reflexive (order-of L) holds
reflexivity-of L = pr₁ (pr₁ (partial-orderedness-of L))

antisymmetry-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-antisymmetric (order-of L)
antisymmetry-of L = pr₂ (partial-orderedness-of L)

transitivity-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-transitive (order-of L) holds
transitivity-of L = pr₂ (pr₁ (partial-orderedness-of L))

inf-is-glb-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
              → (U : Fam 𝓥 ⟨ L ⟩)
              → ((order-of L) Infs.is-glb-of inf-of L U) U holds
inf-is-glb-of (A , (_≤_ , ⋁_) , order , infima) = infima

inf-is-lower-bound-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                      → (U : Fam 𝓥 ⟨ L ⟩)
                      → ((order-of L) Infs.is-a-lower-bound-of
                          inf-of L U) U holds
inf-is-lower-bound-of L U = pr₁ (inf-is-glb-of L U)

inf-is-greatest-lower-bound-of : (L : Inf-Lattice 𝓤 𝓣 𝓥)
                               → (U : Fam 𝓥 ⟨ L ⟩)
                               → ((u' , _) : Infs.lower-bound (order-of L) U)
                               → (order-of L u' (inf-of L U)) holds
inf-is-greatest-lower-bound-of L U = pr₂ (inf-is-glb-of L U)

sethood-of : (L : Inf-Lattice 𝓤 𝓣 𝓥) → is-set ⟨ L ⟩
sethood-of L =
 type-with-prop-valued-refl-antisym-rel-is-set
  (λ x → λ y → order-of L x y holds)
  (λ x → λ y → holds-is-prop (order-of L x y))
  (λ x → reflexivity-of L x)
  (λ x → λ y → antisymmetry-of L)

\end{code}

Monotone maps on an inf-lattice.

\begin{code}

is-monotone : (L : Inf-Lattice 𝓤 𝓣 𝓥) (M : Inf-Lattice 𝓤' 𝓣' 𝓥')
            → (f : ⟨ L ⟩ → ⟨ M ⟩)
            → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone L M f = (x y : ⟨ L ⟩)
                  → (x ≤⟨ L ⟩ y) holds
                  → (f x ≤⟨ M ⟩ f y) holds

is-monotone-endomap : {𝓤 𝓣 𝓥 : Universe}
                    → (L : Inf-Lattice 𝓤 𝓣 𝓥)
                    → (f : ⟨ L ⟩ → ⟨ L ⟩)
                    → 𝓤 ⊔ 𝓣 ̇
is-monotone-endomap L f = is-monotone L L f

\end{code}
