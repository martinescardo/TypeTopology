Ian Ray. 28th August 2025.

Minor changes and merged into TypeToplogy in April 2026.

We define the notion of univalent family in terms of a reflexive graph image.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.UnivalentFamilies where

open import MLTT.Spartan
open import UF.Equiv
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.Univalent

\end{code}

The reflexive graph image with carrier A, on a family B : A → Type, has edges
x ≈ y given by an equivalence between the fibers, that is B(x) ≃ B(y).

\begin{code}

refl-graph-image : (A : 𝓤 ̇) → (A → 𝓣 ̇) → Refl-Graph 𝓤 𝓣
refl-graph-image {𝓤} {𝓣} A B = (A , I , II)
 where
  I : A → A → 𝓣 ̇
  I x y = B x ≃ B y
  II : (x : A) → I x x
  II x = ≃-refl (B x)

is-univalent-family : Σ A ꞉ 𝓤 ̇ , (A → 𝓣 ̇)
                    → 𝓤 ⊔ 𝓣 ̇
is-univalent-family (A , B) = is-univalent-refl-graph (refl-graph-image A B)

\end{code}

This definition is intentionally general and offers a robust theoretical
framework for working with a universe of things. That is, if one was working
directly with the codes of a tarski style universe presentation than a
univalent family would be a pair (𝓤 , El) consiting of the universe type and
the decoding map El : 𝓤 → Type. In Agda the user may operate as if universes
where presented à la Russel and thus our pair of interest is simply (𝓤 , id).
But there are other examples of univalent families of interest such as
(Prop, pr₁), (Set, pr₁), (ℕ , finset), etc.

We can give some equivalent characterizations of univalent family of types.

\begin{code}

id-to-equiv-family : {A : 𝓤 ̇} {B : A → 𝓣 ̇}
                   → (x y : A)
                   → x ＝ y
                   → B x ≃ B y
id-to-equiv-family {_} {_} {A} {B} x y = id-to-edge (refl-graph-image A B) 

is-univalent-family-implies-id-to-equiv
 : {A : 𝓤 ̇} {B : A → 𝓣 ̇}
 → is-univalent-family (A , B)
 → (x y : A)
 → is-equiv (id-to-equiv-family x y)
is-univalent-family-implies-id-to-equiv {𝓤} {𝓣} {A} {B} is-ua-fam
 = prop-fans-implies-id-to-edge-equiv (refl-graph-image A B) is-ua-fam

\end{code}

We conclude by defining a univalent family of univalent reflexive graps.

\begin{code}

univalent-family-of-univalent-refl-graphs
 : {𝓦 𝓣 : Universe}
 → ((U , 𝓔) : Σ U ꞉ 𝓤 ̇ , (U → Univalent-Refl-Graph 𝓦 𝓣))
 → 𝓤 ⊔ 𝓦 ̇
univalent-family-of-univalent-refl-graphs (U , 𝓔)
 = is-univalent-refl-graph (refl-graph-image U (λ A → ⟨ (𝓔 A) ⟩ᵤ))

\end{code}
