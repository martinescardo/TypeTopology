Ian Ray. 28th August 2025.

Minor changes and merged into TypeToplogy in March 2026.

We define displayed reflexive graphs (see index for references to Sterling,
Buchholtz, etc.)

Given a reflexive graph (A , ≈), a displayed reflexive graph over A
consists of a type family B : A → Type together with an reflexive relation
≈ₚ : B x → B y → Type, for every x, y : A and p : x ≈ y.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.Displayed where

open import MLTT.Spartan
open import UF.Base
open import ReflexiveGraphs.Type

module _ (𝓣 𝓦 : Universe) where

 Displayed-Refl-Graph : (𝓐 : Refl-Graph 𝓤 𝓥) → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
 Displayed-Refl-Graph 𝓐
  = Σ B ꞉ (⟨ 𝓐 ⟩ → 𝓣 ̇) ,
     Σ R ꞉ ({x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y) → B x → B y → 𝓦 ̇) ,
      ({x : ⟨ 𝓐 ⟩} (u : B x) → R (≈-refl 𝓐 x) u u)

\end{code}

Just as with reflexive graphs we will add some boiler plate and syntax to work
more easily with displayed reflexive graphs.

\begin{code}

module _ {𝓐 : Refl-Graph 𝓤 𝓥} where 

 ⟪_⟫ : Displayed-Refl-Graph 𝓣 𝓦 𝓐 → ⟨ 𝓐 ⟩ → 𝓣 ̇
 ⟪ (B , _) ⟫ = B

 displayed-edge-rel : (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
                    → {x y : ⟨ 𝓐 ⟩} (p : x ≈⟨ 𝓐 ⟩ y)
                    → ⟪ 𝓑 ⟫ x → ⟪ 𝓑 ⟫ y → 𝓦 ̇
 displayed-edge-rel (_ , R , _) = R

 syntax displayed-edge-rel 𝓑 p u v = u ≈⟨ 𝓑 ﹐ p ⟩ v

 ≈-disp-refl : (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
             → {x : ⟨ 𝓐 ⟩} (u : ⟪ 𝓑 ⟫ x)
             → u ≈⟨ 𝓑 ﹐ ≈-refl 𝓐 x ⟩ u 
 ≈-disp-refl (_ , _ , r) u = r u
 
\end{code}

We show that the component of a displayed reflexive graph is itself a
reflexive graph.

\begin{code}

 component-refl-graph : Displayed-Refl-Graph 𝓣 𝓦 𝓐
                      → ⟨ 𝓐 ⟩
                      → Refl-Graph 𝓣 𝓦
 component-refl-graph 𝓑 x
  = (⟪ 𝓑 ⟫ x , displayed-edge-rel 𝓑 (≈-refl 𝓐 x) , ≈-disp-refl 𝓑)

 syntax component-refl-graph 𝓑 x = [ 𝓑 ] x

\end{code}

Displayed reflexive graph homomorphism.

\begin{code}

displayed-refl-graph-hom : {𝓐 : Refl-Graph 𝓤 𝓥} {𝓐' : Refl-Graph 𝓤' 𝓥'}
                         → (F : refl-graph-hom 𝓐 𝓐')
                         → (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
                         → (𝓑' : Displayed-Refl-Graph 𝓣' 𝓦' 𝓐')
                         → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓦 ⊔ 𝓣' ⊔ 𝓦' ̇
displayed-refl-graph-hom {_} {_} {_} {_} {_} {_} {_} {_} {𝓐} {𝓐'}
 (F₀ , F₁ , Fᵣ) 𝓑 𝓑'
 = Σ G ꞉ ((x : ⟨ 𝓐 ⟩) → ⟪ 𝓑 ⟫ x → ⟪ 𝓑' ⟫ (F₀ x)) ,
    Σ G' ꞉ ((x y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) (u : ⟪ 𝓑 ⟫ x) (v : ⟪ 𝓑 ⟫ y)
         → u ≈⟨ 𝓑 ﹐ p ⟩ v
         → (G x u) ≈⟨ 𝓑' ﹐ (F₁ x y p) ⟩ (G y v)) ,
     ((x : ⟨ 𝓐 ⟩) (u : ⟪ 𝓑 ⟫ x)
         → G' x x (≈-refl 𝓐 x) u u (≈-disp-refl 𝓑 u)
         ＝ transport (λ - → (G x u) ≈⟨ 𝓑' ﹐ - ⟩ (G x u))
             (Fᵣ x ⁻¹) (≈-disp-refl 𝓑' (G x u)))

\end{code}
