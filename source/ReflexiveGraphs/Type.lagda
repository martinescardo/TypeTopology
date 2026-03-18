Ian Ray. 28th August 2025.

Minor changes and merged into TypeToplogy in February 2026.

We give the definition of reflexive graph here following Jonathan Sterling's
treatment in "Reflexive graph lenses in univalent foundations"
(see https://doi.org/10.48550/arXiv.2404.07854).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.Type where

open import MLTT.Spartan

\end{code}

A reflexive graph consists of a type, a binary type valued relation and a
reflexivity datum.

\begin{code}

module _ (𝓤 𝓥 : Universe) where

 Refl-Graph : (𝓤 ⊔ 𝓥)⁺ ̇
 Refl-Graph = Σ A ꞉ 𝓤 ̇ , Σ R ꞉ (A → A → 𝓥 ̇) , ((x : A) → R x x)

\end{code}

We provide boiler plate and syntax which allows us to conveniently discuss
the components of a reflexive graph.

\begin{code}

⟨_⟩ : Refl-Graph 𝓤 𝓥 → 𝓤 ̇
⟨ (A , _) ⟩ = A

edge-rel : (𝓐 : Refl-Graph 𝓤 𝓥) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓥 ̇
edge-rel (_ , R , _) = R

syntax edge-rel 𝓐 x y = x ≈⟨ 𝓐 ⟩ y

≈-refl : (𝓐 : Refl-Graph 𝓤 𝓥) → (x : ⟨ 𝓐 ⟩) → x ≈⟨ 𝓐 ⟩ x
≈-refl (_ , _ , r) x = r x

\end{code}

We define homomorphisms of reflexive graphs as a sigma and record type.

TODO. Decide which is preferred. So far this notion hasn't been used but it
may prove to be important in the future...

\begin{code}

Refl-Graph-Hom : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓐' : Refl-Graph 𝓤' 𝓥')
               → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
Refl-Graph-Hom 𝓐 𝓐'
 = Σ F ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓐' ⟩) ,
    Σ F' ꞉ ((x y : ⟨ 𝓐 ⟩) → x ≈⟨ 𝓐 ⟩ y → F x ≈⟨ 𝓐' ⟩ F y) ,
     ((x : ⟨ 𝓐 ⟩) → F' x x (≈-refl 𝓐 x) ＝ ≈-refl 𝓐' (F x))

record Refl-Graph-Hom-record
 (𝓐 : Refl-Graph 𝓤 𝓥) (𝓐' : Refl-Graph 𝓤' 𝓥') : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇ where
 field
  func : ⟨ 𝓐 ⟩ → ⟨ 𝓐' ⟩
  pres-≈ : (x y : ⟨ 𝓐 ⟩) → x ≈⟨ 𝓐 ⟩ y → func x ≈⟨ 𝓐' ⟩ func y
  pres-≈-refl : (x : ⟨ 𝓐 ⟩) → pres-≈ x x (≈-refl 𝓐 x) ＝ ≈-refl 𝓐' (func x)

\end{code}
