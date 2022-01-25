Tom de Jong, late February - early March 2020.
4 January 2022: Minor refactorings.

The way-below relation for a directed complete poset.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoWayBelow
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥

way-below : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
way-below 𝓓 x y = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                → ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i

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
                   → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ x → x ≡ y
≪-is-antisymmetric 𝓓 {x} {y} u v =
 antisymmetry 𝓓 x y (≪-to-⊑ 𝓓 u) (≪-to-⊑ 𝓓 v)

≪-is-transitive : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
                → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ z → x ≪⟨ 𝓓 ⟩ z
≪-is-transitive 𝓓 {x} {y} {z} u v I α δ l = u I α δ k
 where
  k = y     ⊑⟨ 𝓓 ⟩[ ≪-to-⊑ 𝓓 v ]
      z     ⊑⟨ 𝓓 ⟩[ l ]
      ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

is-compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

being-compact-is-prop : (𝓓 : DCPO {𝓤} {𝓣}) (x : ⟨ 𝓓 ⟩)
                      → is-prop (is-compact 𝓓 x)
being-compact-is-prop 𝓓 x = ≪-is-prop-valued 𝓓

\end{code}
