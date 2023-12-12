Tom de Jong, late February - early March 2020.
Jan - Mar 2022: Some additions, most notably on embeddings.

We define the way-below relation and the notion of a compact element in a
directed complete poset.

Contents
* Basic properties of the way-below relation and its interaction with the order.
* Definition of a compact element as an element that is way below itself.
* The compact elements are closed under existing finite joins.
* In an embedding-projection pair, the embedding preserves and reflects the
  way-below relation, and hence, compact elements.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.WayBelow
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥

way-below : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
way-below 𝓓 x y = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                → ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i

is-way-upperbound : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇ } (x : ⟨ 𝓓 ⟩) (α : I → ⟨ 𝓓 ⟩)
                  → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-way-upperbound 𝓓 {I} x α = (i : I) → α i ≪⟨ 𝓓 ⟩ x

syntax way-below 𝓓 x y = x ≪⟨ 𝓓 ⟩ y

≪-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y
≪-to-⊑ 𝓓 {x} {y} u = ∥∥-rec (prop-valuedness 𝓓 x y) γ g
 where
  α : 𝟙{𝓥} → ⟨ 𝓓 ⟩
  α ⋆ = y
  γ : (Σ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i) → x ⊑⟨ 𝓓 ⟩ y
  γ (⋆ , l) = l
  g : ∃ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i
  g = u 𝟙 α δ (∐-is-upperbound 𝓓 δ ⋆)
   where
    δ : is-Directed 𝓓 α
    δ = (∣ ⋆ ∣ , ε)
     where
      ε : (i j : 𝟙)
        → ∃ k ꞉ 𝟙 , α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k
      ε ⋆ ⋆ = ∣ ⋆ , reflexivity 𝓓 y , reflexivity 𝓓 y ∣

⊑-≪-⊑-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {a b c d : ⟨ 𝓓 ⟩}
           → a ⊑⟨ 𝓓 ⟩ b
           → b ≪⟨ 𝓓 ⟩ c
           → c ⊑⟨ 𝓓 ⟩ d
           → a ≪⟨ 𝓓 ⟩ d
⊑-≪-⊑-to-≪ 𝓓 {a} {b} {c} {d} l₁ u l₂ I α δ m = γ
 where
  γ : ∃ i ꞉ I , a ⊑⟨ 𝓓 ⟩ α i
  γ = ∥∥-functor g h
   where
    g : (Σ i ꞉ I , b ⊑⟨ 𝓓 ⟩ α i)
      → (Σ i ꞉ I , a ⊑⟨ 𝓓 ⟩ α i)
    g (i , u) = (i , v)
     where
      v = a   ⊑⟨ 𝓓 ⟩[ l₁ ]
          b   ⊑⟨ 𝓓 ⟩[ u  ]
          α i ∎⟨ 𝓓 ⟩
    h : ∃ i ꞉ I , b ⊑⟨ 𝓓 ⟩ α i
    h = u I α δ l
     where
      l = c     ⊑⟨ 𝓓 ⟩[ l₂ ]
          d     ⊑⟨ 𝓓 ⟩[ m  ]
          ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

⊑-≪-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ⊑⟨ 𝓓 ⟩ y
         → y ≪⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
⊑-≪-to-≪ 𝓓 {x} {y} {z} l u = ⊑-≪-⊑-to-≪ 𝓓 l u (reflexivity 𝓓 z)

≪-⊑-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ≪⟨ 𝓓 ⟩ y
         → y ⊑⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
≪-⊑-to-≪ 𝓓 {x} {y} {z} = ⊑-≪-⊑-to-≪ 𝓓 (reflexivity 𝓓 x)

≪-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → is-prop (x ≪⟨ 𝓓 ⟩ y)
≪-is-prop-valued 𝓓 = Π₄-is-prop fe (λ I α δ u → ∥∥-is-prop)

≪-is-antisymmetric : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩}
                   → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ x → x ＝ y
≪-is-antisymmetric 𝓓 {x} {y} u v =
 antisymmetry 𝓓 x y (≪-to-⊑ 𝓓 u) (≪-to-⊑ 𝓓 v)

≪-is-transitive : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
                → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ z → x ≪⟨ 𝓓 ⟩ z
≪-is-transitive 𝓓 {x} {y} {z} u v I α δ l = u I α δ k
 where
  k = y     ⊑⟨ 𝓓 ⟩[ ≪-to-⊑ 𝓓 v ]
      z     ⊑⟨ 𝓓 ⟩[ l ]
      ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

\end{code}

An element is called compact if it way below itself.

\begin{code}

is-compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

being-compact-is-prop : (𝓓 : DCPO {𝓤} {𝓣}) (x : ⟨ 𝓓 ⟩)
                      → is-prop (is-compact 𝓓 x)
being-compact-is-prop 𝓓 x = ≪-is-prop-valued 𝓓

compact-⊑-≃-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x : ⟨ 𝓓 ⟩}
              → is-compact 𝓓 x
              → {y : ⟨ 𝓓 ⟩}
              → (x ⊑⟨ 𝓓 ⟩ y) ≃ (x ≪⟨ 𝓓 ⟩ y)
compact-⊑-≃-≪ 𝓓 {x} c {y} =
 logically-equivalent-props-are-equivalent
  (prop-valuedness 𝓓 x y) (≪-is-prop-valued 𝓓)
  (≪-⊑-to-≪ 𝓓 c)
  (≪-to-⊑ 𝓓)

\end{code}

The compact elements are closed under existing finite joins.

\begin{code}

module _ where
 open import DomainTheory.Basics.Pointed pt fe 𝓥

 ⊥-is-compact : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → is-compact (𝓓 ⁻) (⊥ 𝓓)
 ⊥-is-compact 𝓓 I α δ _ = ∥∥-functor h (inhabited-if-Directed (𝓓 ⁻) α δ)
  where
   h : I → Σ i ꞉ I , ⊥ 𝓓 ⊑⟪ 𝓓 ⟫ α i
   h i = (i , ⊥-is-least 𝓓 (α i))

binary-join-is-compact : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
                       → x ⊑⟨ 𝓓 ⟩ z → y ⊑⟨ 𝓓 ⟩ z
                       → ((d : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ d → y ⊑⟨ 𝓓 ⟩ d → z ⊑⟨ 𝓓 ⟩ d)
                       → is-compact 𝓓 x → is-compact 𝓓 y → is-compact 𝓓 z
binary-join-is-compact
 𝓓 {x} {y} {z} x-below-z y-below-z z-lb-of-ubs x-cpt y-cpt = γ
  where
   γ : is-compact 𝓓 z
   γ I α δ z-below-∐α = ∥∥-rec₂ ∃-is-prop f
                         (x-cpt I α δ (x     ⊑⟨ 𝓓 ⟩[ x-below-z ]
                                       z     ⊑⟨ 𝓓 ⟩[ z-below-∐α ]
                                       ∐ 𝓓 δ ∎⟨ 𝓓 ⟩))
                         (y-cpt I α δ (y     ⊑⟨ 𝓓 ⟩[ y-below-z ]
                                       z     ⊑⟨ 𝓓 ⟩[ z-below-∐α ]
                                       ∐ 𝓓 δ ∎⟨ 𝓓 ⟩))
    where
     f : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i)
       → (Σ j ꞉ I , y ⊑⟨ 𝓓 ⟩ α j)
       → (∃ k ꞉ I , z ⊑⟨ 𝓓 ⟩ α k)
     f (i , x-below-αᵢ) (j , y-below-αⱼ) =
      ∥∥-functor g (semidirected-if-Directed 𝓓 α δ i j)
       where
        g : (Σ k ꞉ I , (α i ⊑⟨ 𝓓 ⟩ α k) × (α j ⊑⟨ 𝓓 ⟩ α k))
          → Σ k ꞉ I , z ⊑⟨ 𝓓 ⟩ α k
        g (k , lᵢ , lⱼ) =
         (k , z-lb-of-ubs (α k)
               (x   ⊑⟨ 𝓓 ⟩[ x-below-αᵢ ]
                α i ⊑⟨ 𝓓 ⟩[ lᵢ ]
                α k ∎⟨ 𝓓 ⟩)
               (y   ⊑⟨ 𝓓 ⟩[ y-below-αⱼ ]
                α j ⊑⟨ 𝓓 ⟩[ lⱼ ]
                α k ∎⟨ 𝓓 ⟩))

\end{code}

If we have a continuous section s with continuous retraction r, then y ≪ s x
implies r y ≪ x for all elements x and y.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 continuous-retraction-≪-criterion : (y : ⟨ 𝓔 ⟩) (x : ⟨ 𝓓 ⟩)
                                   → y ≪⟨ 𝓔 ⟩ s x
                                   → r y ≪⟨ 𝓓 ⟩ x
 continuous-retraction-≪-criterion y x y-way-below-sx I α δ x-below-∐α =
  ∥∥-functor h (y-way-below-sx I (s ∘ α) ε l)
   where
    ε : is-Directed 𝓔 (s ∘ α)
    ε = image-is-directed' 𝓓 𝓔 𝕤 δ
    l : s x ⊑⟨ 𝓔 ⟩ ∐ 𝓔 ε
    l = s x       ⊑⟨ 𝓔 ⟩[ monotone-if-continuous 𝓓 𝓔 𝕤 x (∐ 𝓓 δ) x-below-∐α ]
        s (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ continuous-∐-⊑ 𝓓 𝓔 𝕤 δ ]
        ∐ 𝓔 ε     ∎⟨ 𝓔 ⟩
    h : (Σ i ꞉ I , y ⊑⟨ 𝓔 ⟩ s (α i))
      → (Σ i ꞉ I , r y ⊑⟨ 𝓓 ⟩ α i)
    h (i , u) = (i , v)
     where
      v = r y         ⊑⟨ 𝓓 ⟩[ monotone-if-continuous 𝓔 𝓓 𝕣 y (s (α i)) u ]
          r (s (α i)) ⊑⟨ 𝓓 ⟩[ ＝-to-⊑ 𝓓 (s-section-of-r (α i)) ]
          α i         ∎⟨ 𝓓 ⟩

\end{code}

In an embedding-projection pair, the embedding preserves and reflects the
way-below relation, and hence, compact elements.

\begin{code}

module _
        (𝓓 : DCPO {𝓤}  {𝓣} )
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ε : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
        (ε-is-continuous : is-continuous 𝓓 𝓔 ε)
        (π : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩)
        (π-is-continuous : is-continuous 𝓔 𝓓 π)
        (π-ε-retraction : (x : ⟨ 𝓓 ⟩) → π (ε x) ＝ x)
        (ε-π-deflation : (y : ⟨ 𝓔 ⟩) → ε (π y) ⊑⟨ 𝓔 ⟩ y)
       where

 embeddings-preserve-≪ : (x y : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ y → ε x ≪⟨ 𝓔 ⟩ ε y
 embeddings-preserve-≪ x y x-way-below-y I α δ εx-below-∐α =
  ∥∥-functor h (x-way-below-y I (π ∘ α) δ' y-below-∐πα)
   where
    δ' : is-Directed 𝓓 (π ∘ α)
    δ' = image-is-directed' 𝓔 𝓓 (π , π-is-continuous) δ
    y-below-∐πα = y         ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
                  π (ε y)   ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
                  π (∐ 𝓔 δ) ⊑⟨ 𝓓 ⟩[ ⦅3⦆ ]
                  ∐ 𝓓 δ'    ∎⟨ 𝓓 ⟩
     where
      ⦅1⦆ = ＝-to-⊑ 𝓓 ((π-ε-retraction y) ⁻¹)
      ⦅2⦆ = monotone-if-continuous 𝓔 𝓓 (π , π-is-continuous) (ε y) (∐ 𝓔 δ)
             εx-below-∐α
      ⦅3⦆ = continuous-∐-⊑ 𝓔 𝓓 (π , π-is-continuous) δ
    h : (Σ i ꞉ I , x   ⊑⟨ 𝓓 ⟩ π (α i))
      → (Σ i ꞉ I , ε x ⊑⟨ 𝓔 ⟩ α i)
    h (i , u) = (i , (ε x         ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
                      ε (π (α i)) ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
                      α i         ∎⟨ 𝓔 ⟩))
     where
      ⦅1⦆ = monotone-if-continuous 𝓓 𝓔 (ε , ε-is-continuous) x (π (α i)) u
      ⦅2⦆ = ε-π-deflation (α i)

 embeddings-preserve-compactness : (x : ⟨ 𝓓 ⟩)
                                 → is-compact 𝓓 x → is-compact 𝓔 (ε x)
 embeddings-preserve-compactness x = embeddings-preserve-≪ x x

 embeddings-reflect-≪ : (x y : ⟨ 𝓓 ⟩) → ε x ≪⟨ 𝓔 ⟩ ε y → x ≪⟨ 𝓓 ⟩ y
 embeddings-reflect-≪ x y l = transport (λ - → - ≪⟨ 𝓓 ⟩ y) (π-ε-retraction x) lem
  where
   lem : π (ε x) ≪⟨ 𝓓 ⟩ y
   lem = continuous-retraction-≪-criterion 𝓓 𝓔 ρ (ε x) y l
    where
     ρ : 𝓓 continuous-retract-of 𝓔
     ρ = record
           { s = ε
           ; r = π
           ; s-section-of-r = π-ε-retraction
           ; s-is-continuous = ε-is-continuous
           ; r-is-continuous = π-is-continuous
           }

 embeddings-reflect-compactness : (x : ⟨ 𝓓 ⟩)
                                → is-compact 𝓔 (ε x)
                                → is-compact 𝓓 x
 embeddings-reflect-compactness x = embeddings-reflect-≪ x x

\end{code}
