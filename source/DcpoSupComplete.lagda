Tom de Jong

TODO

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoSupComplete
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt hiding (_∨_)

open import UF-Equiv
open import UF-EquivalenceExamples

open import Dcpo pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 record is-sup-complete : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ⋁ : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩
   ⋁-is-sup : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) (⋁ α) α

  ⋁-is-upperbound : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩)
                  → is-upperbound (underlying-order 𝓓) (⋁ α) α
  ⋁-is-upperbound α = sup-is-upperbound (underlying-order 𝓓) (⋁-is-sup α)

  ⋁-is-lowerbound-of-upperbounds : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (⋁ α) α
  ⋁-is-lowerbound-of-upperbounds α =
   sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (⋁-is-sup α)

\end{code}

TODO: Write comment

\begin{code}

module sup-complete-dcpo
        (𝓓 : DCPO {𝓤} {𝓣'})
        (𝓓-is-sup-complete : is-sup-complete 𝓓)
       where

 open is-sup-complete 𝓓-is-sup-complete

 open import List

 ⊥ : ⟨ 𝓓 ⟩
 ⊥ = ⋁ 𝟘-elim

 ⊥-is-least : is-least (underlying-order 𝓓) ⊥
 ⊥-is-least x = ⋁-is-lowerbound-of-upperbounds 𝟘-elim x 𝟘-induction

 ∨-family : (x y : ⟨ 𝓓 ⟩) → 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
 ∨-family x y (inl _) = x
 ∨-family x y (inr _) = y

 _∨_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩
 x ∨ y = ⋁ (∨-family x y)

 infix 100 _∨_

 ∨-is-upperbound₁ : {x y : ⟨ 𝓓 ⟩} → x ⊑⟨ 𝓓 ⟩ x ∨ y
 ∨-is-upperbound₁ {x} {y} = ⋁-is-upperbound (∨-family x y) (inl ⋆)

 ∨-is-upperbound₂ : {x y : ⟨ 𝓓 ⟩} → y ⊑⟨ 𝓓 ⟩ x ∨ y
 ∨-is-upperbound₂ {x} {y} = ⋁-is-upperbound (∨-family x y) (inr ⋆)

 ∨-is-lowerbound-of-upperbounds : {x y z : ⟨ 𝓓 ⟩}
                                → x ⊑⟨ 𝓓 ⟩ z → y ⊑⟨ 𝓓 ⟩ z
                                → x ∨ y ⊑⟨ 𝓓 ⟩ z
 ∨-is-lowerbound-of-upperbounds {x} {y} {z} u v =
  ⋁-is-lowerbound-of-upperbounds (∨-family x y) z γ
   where
    γ : is-upperbound (underlying-order 𝓓) z (∨-family x y)
    γ (inl _) = u
    γ (inr _) = v

 module _
         {I : 𝓦 ̇  }
         (α : I → ⟨ 𝓓 ⟩)
        where

  directify : List I → ⟨ 𝓓 ⟩
  directify []      = ⊥
  directify (x ∷ l) = α x ∨ directify l

  directify-is-inhabited : ∥ domain directify ∥
  directify-is-inhabited = ∣ [] ∣

  ++-is-upperbound₁ : (l k : List I) → directify l ⊑⟨ 𝓓 ⟩ directify (l ++ k)
  ++-is-upperbound₁ []      k = ⊥-is-least (directify ([] ++ k))
  ++-is-upperbound₁ (i ∷ l) k =
   ∨-is-lowerbound-of-upperbounds ∨-is-upperbound₁
    (directify l              ⊑⟨ 𝓓 ⟩[ ++-is-upperbound₁ l k ]
     directify (l ++ k)       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
     α i ∨ directify (l ++ k) ∎⟨ 𝓓 ⟩)

  ++-is-upperbound₂ : (l k : List I) → directify k ⊑⟨ 𝓓 ⟩ directify (l ++ k)
  ++-is-upperbound₂ []      k = reflexivity 𝓓 (directify k)
  ++-is-upperbound₂ (i ∷ l) k =
   directify k              ⊑⟨ 𝓓 ⟩[ ++-is-upperbound₂ l k ]
   directify (l ++ k)       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
   α i ∨ directify (l ++ k) ∎⟨ 𝓓 ⟩

  directify-is-semidirected : is-Semidirected 𝓓 directify
  directify-is-semidirected l k =
   ∣ (l ++ k) , ++-is-upperbound₁ l k , ++-is-upperbound₂ l k ∣

  directify-is-directed : is-Directed 𝓓 directify
  directify-is-directed = (directify-is-inhabited , directify-is-semidirected)

  directify-↓ : (x : ⟨ 𝓓 ⟩) → (Σ l ꞉ List I , directify l ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
  directify-↓ x = directify ∘ pr₁

  directify-↓-is-inhabited : {x : ⟨ 𝓓 ⟩} → ∥ domain (directify-↓ x) ∥
  directify-↓-is-inhabited {x} = ∣ [] , ⊥-is-least x ∣

  ++-is-lowerbound-of-upperbounds : (l k : List I) {x : ⟨ 𝓓 ⟩}
                                  → directify l ⊑⟨ 𝓓 ⟩ x
                                  → directify k ⊑⟨ 𝓓 ⟩ x
                                  → directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
  ++-is-lowerbound-of-upperbounds []      k {x} u v = v
  ++-is-lowerbound-of-upperbounds (i ∷ l) k {x} u v =
   ∨-is-lowerbound-of-upperbounds ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ = α i              ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
          α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
          x                 ∎⟨ 𝓓 ⟩
     ⦅2⦆ : directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
     ⦅2⦆ = ++-is-lowerbound-of-upperbounds l k ⦅2'⦆ v
      where
       ⦅2'⦆ = directify l      ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
             α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
             x                 ∎⟨ 𝓓 ⟩

  directify-↓-is-semidirected : {x : ⟨ 𝓓 ⟩} → is-Semidirected 𝓓 (directify-↓ x)
  directify-↓-is-semidirected (l , l-below-x) (k , k-below-x) =
   ∣ ((l ++ k) , ++-is-lowerbound-of-upperbounds l k l-below-x k-below-x)
               , (++-is-upperbound₁ l k) , (++-is-upperbound₂ l k) ∣

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   directify-↓-is-directed : is-Directed 𝓓 (directify-↓ x)
   directify-↓-is-directed =
    (directify-↓-is-inhabited , directify-↓-is-semidirected)

   directify-↓-upperbound : is-upperbound (underlying-order 𝓓) x (directify-↓ x)
   directify-↓-upperbound = pr₂

   ↓-family : (Σ i ꞉ I , α i ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
   ↓-family = α ∘ pr₁

   directify-↓-sup : is-sup (underlying-order 𝓓) x ↓-family
                   → is-sup (underlying-order 𝓓) x (directify-↓ x)
   directify-↓-sup (x-ub , x-lb-of-ubs) = (directify-↓-upperbound , γ)
    where
     γ : is-lowerbound-of-upperbounds (underlying-order 𝓓) x (directify-↓ x)
     γ y y-is-ub = x-lb-of-ubs y claim
      where
       claim : is-upperbound (underlying-order 𝓓) y ↓-family
       claim (i , αᵢ-below-x) =
        α i                       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
        directify-↓ x ([ i ] , u) ⊑⟨ 𝓓 ⟩[ y-is-ub ([ i ] , u) ]
        y                         ∎⟨ 𝓓 ⟩
         where
          u : α i ∨ ⊥ ⊑⟨ 𝓓 ⟩ x
          u = ∨-is-lowerbound-of-upperbounds αᵢ-below-x (⊥-is-least x)

\end{code}

TODO: Write comment

\begin{code}

 module _
         (𝓓-is-locally-small : is-locally-small 𝓓)
         {I : 𝓥 ̇  }
         (α : I → ⟨ 𝓓 ⟩)
        where

  open is-locally-small 𝓓-is-locally-small

  directify-↓-small : (x : ⟨ 𝓓 ⟩) → (Σ l ꞉ List I , directify α l ⊑ₛ x) → ⟨ 𝓓 ⟩
  directify-↓-small x = directify α ∘ pr₁

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   directify-↓-small-≃ : domain (directify-↓ α x) ≃ domain (directify-↓-small x)
   directify-↓-small-≃ =
    Σ-cong (λ l → ≃-sym ⊑ₛ-≃-⊑)

   directify-↓-small-sup : is-sup (underlying-order 𝓓) x (↓-family α)
                         → is-sup (underlying-order 𝓓) x (directify-↓-small x)
   directify-↓-small-sup x-is-sup =
    reindexed-family-sup 𝓓 directify-↓-small-≃
     (directify-↓ α x) x (directify-↓-sup α x-is-sup)

   directify-↓-small-is-directed : is-Directed 𝓓 (directify-↓-small x)
   directify-↓-small-is-directed =
    reindexed-family-is-directed 𝓓 directify-↓-small-≃
     (directify-↓ α x) (directify-↓-is-directed α)

\end{code}

TODO: Comment
As a consequence, if we have all joins, then the 'directification' of a
family of compact elements again consists of compact elements.
(To get all joins in a dcpo, it suffices to ask for all finite joins to exist,
but we don't formalize or need this.)

\begin{code}

module directify-compact
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓓-is-sup-complete : is-sup-complete 𝓓)
       where

 open sup-complete-dcpo 𝓓 𝓓-is-sup-complete
 open import List

 directify-is-compact : {I : 𝓦 ̇  } (α : I → ⟨ 𝓓 ⟩)
                      → ((i : I) → is-compact 𝓓 (α i))
                      → (l : List I) → is-compact 𝓓 (directify α l)
 directify-is-compact α αs-are-compact []      =
  ⊥-is-compact (𝓓 , ⊥ , ⊥-is-least)
 directify-is-compact α αs-are-compact (i ∷ l) =
  binary-join-is-compact 𝓓 ∨-is-upperbound₁ ∨-is-upperbound₂
   (λ d → ∨-is-lowerbound-of-upperbounds) (αs-are-compact i) IH
   where
    IH : is-compact 𝓓 (directify α l)
    IH = directify-is-compact α αs-are-compact l

 directify-↓-is-compact : {I : 𝓦 ̇  } (α : I → ⟨ 𝓓 ⟩) {x : ⟨ 𝓓 ⟩}
                        → ((i : I) → is-compact 𝓓 (α i))
                        → (j : domain (directify-↓ α x))
                        → is-compact 𝓓 (directify-↓ α x j)
 directify-↓-is-compact α αs-are-compact j =
  directify-is-compact α αs-are-compact (pr₁ j)

\end{code}
