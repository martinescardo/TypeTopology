Ian Ray. 3rd September 2025.

Slight modifications made in March 2026 before merging into TypeTopology.

We define what it means for displayed reflexive graph to be univalent
(see the index for reference to Sterling, Buchholtz, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.DisplayedUnivalent where

open import MLTT.Spartan
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.Univalent

\end{code}

A displayed reflexive graph is univalent when each of its components (or fibers)
is univalent.

\begin{code}

is-displayed-univalent-refl-graph : (𝓐 : Refl-Graph 𝓤 𝓥)
                                    (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
                                  → 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
is-displayed-univalent-refl-graph 𝓐 𝓑 = (x : ⟨ 𝓐 ⟩)
                                      → is-univalent-refl-graph ([ 𝓑 ] x)

Displayed-Univalent-Refl-Graph : (𝓣 𝓦 : Universe) (𝓐 : Refl-Graph 𝓤 𝓥)
                               → 𝓤 ⊔ 𝓥 ⊔ (𝓣 ⊔ 𝓦)⁺ ̇
Displayed-Univalent-Refl-Graph 𝓣 𝓦 𝓐
 = Σ 𝓑 ꞉ (Displayed-Refl-Graph 𝓣 𝓦 𝓐) , is-displayed-univalent-refl-graph 𝓐 𝓑

underlying-displayed-refl-graph : {𝓐 : Refl-Graph 𝓤 𝓥}
                                → (𝓑 : Displayed-Univalent-Refl-Graph 𝓣 𝓦 𝓐)
                                → Displayed-Refl-Graph 𝓣 𝓦 𝓐
underlying-displayed-refl-graph (𝓑 , _) = 𝓑

syntax underlying-displayed-refl-graph 𝓑 = 𝓑 ∣ᵤ 
                               
\end{code}
