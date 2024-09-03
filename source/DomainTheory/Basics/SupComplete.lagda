Tom de Jong, late February - early March 2022.
Refactored slightly on 26 June 2024.

We consider sup-complete dcpos. Of course, every sup-complete poset is a dcpo,
but because the basic object of our domain-theoretic development is a dcpo, the
formalization is structured around dcpos that are additionally sup-complete.

The main point of this file is to show that we can extend families into a
sup-complete dcpo to directed families.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.SupComplete
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt hiding (_∨_)

open import MLTT.List

open import UF.Equiv
open import UF.EquivalenceExamples

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

\end{code}

We first define, using a record for convenience, when a dcpo additionally has
all (small) suprema.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where
 record is-sup-complete : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ⋁ : {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩
   ⋁-is-sup : {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) (⋁ α) α

  ⋁-is-upperbound : {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩)
                  → is-upperbound (underlying-order 𝓓) (⋁ α) α
  ⋁-is-upperbound α = sup-is-upperbound (underlying-order 𝓓) (⋁-is-sup α)

  ⋁-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (⋁ α) α
  ⋁-is-lowerbound-of-upperbounds α =
   sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (⋁-is-sup α)

\end{code}

In particular, we get finite joins, which we first define.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 ∨-family : (x y : ⟨ 𝓓 ⟩) → 𝟙{𝓥} + 𝟙{𝓥} → ⟨ 𝓓 ⟩
 ∨-family x y (inl _) = x
 ∨-family x y (inr _) = y

 record has-finite-joins : 𝓤 ⊔ 𝓣 ⊔ 𝓥 ̇  where
  field
   ⊥ : ⟨ 𝓓 ⟩
   ⊥-is-least : is-least (underlying-order 𝓓) ⊥
   _∨_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩
   ∨-is-sup : (x y : ⟨ 𝓓 ⟩)
            → is-sup (underlying-order 𝓓) (x ∨ y) (∨-family x y)

  infix 100 _∨_

  ∨-is-upperbound₁ : {x y : ⟨ 𝓓 ⟩} → x ⊑⟨ 𝓓 ⟩ x ∨ y
  ∨-is-upperbound₁ {x} {y} = pr₁ (∨-is-sup x y) (inl ⋆)

  ∨-is-upperbound₂ : {x y : ⟨ 𝓓 ⟩} → y ⊑⟨ 𝓓 ⟩ x ∨ y
  ∨-is-upperbound₂ {x} {y} = pr₁ (∨-is-sup x y) (inr ⋆)

  ∨-is-lowerbound-of-upperbounds : {x y z : ⟨ 𝓓 ⟩}
                                 → x ⊑⟨ 𝓓 ⟩ z → y ⊑⟨ 𝓓 ⟩ z
                                 → x ∨ y ⊑⟨ 𝓓 ⟩ z
  ∨-is-lowerbound-of-upperbounds {x} {y} {z} u v = pr₂ (∨-is-sup x y) z γ
   where
    γ : is-upperbound (underlying-order 𝓓) z (∨-family x y)
    γ (inl _) = u
    γ (inr _) = v

sup-complete-dcpo-has-finite-joins : (𝓓 : DCPO {𝓤} {𝓣})
                                   → is-sup-complete 𝓓
                                   → has-finite-joins 𝓓
sup-complete-dcpo-has-finite-joins 𝓓 sc =
 record { ⊥ = ⋁ 𝟘-elim ;
          ⊥-is-least = λ x → ⋁-is-lowerbound-of-upperbounds 𝟘-elim x 𝟘-induction ;
          _∨_ = λ x y → ⋁ (∨-family 𝓓 x y);
          ∨-is-sup = λ x y → ⋁-is-sup (∨-family 𝓓 x y)
        }
  where
   open is-sup-complete sc

\end{code}

The converse holds as well: if a dcpo has finite joins then it is sup-complete.
This is because, by taking finite joins, we can replace an arbitrary family by
one that is directed and which has the same supremum.
This an important separate fact that we prove now.

\begin{code}

module make-family-directed
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓓-has-finite-joins : has-finite-joins 𝓓)
       where

 open has-finite-joins 𝓓-has-finite-joins

 module _
         {I : 𝓦 ̇ }
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

  ++-is-lowerbound-of-upperbounds : (l k : List I) (x : ⟨ 𝓓 ⟩)
                                  → directify l ⊑⟨ 𝓓 ⟩ x
                                  → directify k ⊑⟨ 𝓓 ⟩ x
                                  → directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
  ++-is-lowerbound-of-upperbounds []      k x  u v = v
  ++-is-lowerbound-of-upperbounds (i ∷ l) k x u v =
   ∨-is-lowerbound-of-upperbounds ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ = α i              ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
          α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
          x                 ∎⟨ 𝓓 ⟩
     ⦅2⦆ : directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
     ⦅2⦆ = ++-is-lowerbound-of-upperbounds l k x ⦅2'⦆ v
      where
       ⦅2'⦆ = directify l      ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
             α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
             x                 ∎⟨ 𝓓 ⟩

  ++-is-binary-sup : (l k : List I)
                   → is-sup (underlying-order 𝓓) (directify (l ++ k))
                            (∨-family 𝓓 (directify l) (directify k))
  ++-is-binary-sup l k = ⦅1⦆ , ⦅2⦆
   where
    ⦅1⦆ : (b : 𝟙 + 𝟙)
        → ∨-family 𝓓 (directify l) (directify k) b ⊑⟨ 𝓓 ⟩ directify (l ++ k)
    ⦅1⦆ (inl _) = ++-is-upperbound₁ l k
    ⦅1⦆ (inr _) = ++-is-upperbound₂ l k
    ⦅2⦆ : is-lowerbound-of-upperbounds (underlying-order 𝓓)
           (directify (l ++ k)) (∨-family 𝓓 (directify l) (directify k))
    ⦅2⦆ x x-ub = ++-is-lowerbound-of-upperbounds l k x
                  (x-ub (inl ⋆)) (x-ub (inr ⋆))

  directify-is-semidirected : is-Semidirected 𝓓 directify
  directify-is-semidirected l k =
   ∣ (l ++ k) , ++-is-upperbound₁ l k , ++-is-upperbound₂ l k ∣

  directify-is-directed : is-Directed 𝓓 directify
  directify-is-directed = (directify-is-inhabited , directify-is-semidirected)

  directify-upperbound : (x : ⟨ 𝓓 ⟩) → is-upperbound (underlying-order 𝓓) x α
                       → is-upperbound (underlying-order 𝓓) x directify
  directify-upperbound x x-is-ub []      = ⊥-is-least x
  directify-upperbound x x-is-ub (i ∷ l) =
   ∨-is-lowerbound-of-upperbounds (x-is-ub i) (directify-upperbound x x-is-ub l)

  directify-lowerbound-of-upperbounds :
     (x : ⟨ 𝓓 ⟩)
   → is-lowerbound-of-upperbounds (underlying-order 𝓓) x α
   → is-lowerbound-of-upperbounds (underlying-order 𝓓) x directify
  directify-lowerbound-of-upperbounds x x-is-lb y y-is-ub = x-is-lb y y-is-ub'
   where
    y-is-ub' : (i : I) → α i ⊑⟨ 𝓓 ⟩ y
    y-is-ub' i = α i             ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
                 α i ∨ ⊥         ⊑⟨ 𝓓 ⟩[ reflexivity 𝓓 _  ]
                 directify [ i ] ⊑⟨ 𝓓 ⟩[ y-is-ub [ i ]    ]
                 y               ∎⟨ 𝓓 ⟩

  directify-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x α
                → is-sup (underlying-order 𝓓) x directify
  directify-sup x (x-is-ub , x-is-lb-of-ubs) =
   ( directify-upperbound x x-is-ub
   , directify-lowerbound-of-upperbounds x x-is-lb-of-ubs)

  directify-sup' : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x directify
                 → is-sup (underlying-order 𝓓) x α
  directify-sup' x (x-is-ub , x-is-lb-of-ubs) =
   ( (λ i → α i              ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
             directify [ i ] ⊑⟨ 𝓓 ⟩[ x-is-ub [ i ] ]
             x               ∎⟨ 𝓓 ⟩)
   , (λ y y-is-ub → x-is-lb-of-ubs y (directify-upperbound y y-is-ub)))

\end{code}

Moreover, if each of the αᵢ's are compact, then so is every element in the
directified family, because taking finite joins preserves compactness.

\begin{code}

  directify-is-compact : ((i : I) → is-compact 𝓓 (α i))
                       → (l : List I) → is-compact 𝓓 (directify l)
  directify-is-compact αs-are-compact []      =
   ⊥-is-compact (𝓓 , ⊥ , ⊥-is-least)
  directify-is-compact αs-are-compact (i ∷ l) =
   binary-join-is-compact 𝓓 ∨-is-upperbound₁ ∨-is-upperbound₂
    (λ d → ∨-is-lowerbound-of-upperbounds) (αs-are-compact i) IH
    where
     IH : is-compact 𝓓 (directify l)
     IH = directify-is-compact αs-are-compact l

\end{code}

When constructing small compact bases for exponentials, it turns out that it is
convenient to consider a variation: we consider the family of elements αᵢ less
than some given element x, and the corresponding family of lists l such that
directify l is less than x.

\begin{code}

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   ↓-family : (Σ i ꞉ I , α i ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
   ↓-family = α ∘ pr₁

   directify-↓ : (Σ l ꞉ List I , directify l ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
   directify-↓ = directify ∘ pr₁

   directify-↓-is-inhabited : ∥ domain directify-↓ ∥
   directify-↓-is-inhabited = ∣ [] , ⊥-is-least x ∣

   directify-↓-is-semidirected : is-Semidirected 𝓓 directify-↓
   directify-↓-is-semidirected (l , l-below-x) (k , k-below-x) =
    ∣ ((l ++ k) , ++-is-lowerbound-of-upperbounds l k x l-below-x k-below-x)
                , (++-is-upperbound₁ l k) , (++-is-upperbound₂ l k) ∣


   directify-↓-is-directed : is-Directed 𝓓 directify-↓
   directify-↓-is-directed =
    (directify-↓-is-inhabited , directify-↓-is-semidirected)

   directify-↓-upperbound : is-upperbound (underlying-order 𝓓) x directify-↓
   directify-↓-upperbound = pr₂

   directify-↓-sup : is-sup (underlying-order 𝓓) x ↓-family
                   → is-sup (underlying-order 𝓓) x directify-↓
   directify-↓-sup (x-ub , x-lb-of-ubs) = (directify-↓-upperbound , γ)
    where
     γ : is-lowerbound-of-upperbounds (underlying-order 𝓓) x directify-↓
     γ y y-is-ub = x-lb-of-ubs y claim
      where
       claim : is-upperbound (underlying-order 𝓓) y ↓-family
       claim (i , αᵢ-below-x) =
        α i                     ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
        directify-↓ ([ i ] , u) ⊑⟨ 𝓓 ⟩[ y-is-ub ([ i ] , u) ]
        y                       ∎⟨ 𝓓 ⟩
         where
          u : α i ∨ ⊥ ⊑⟨ 𝓓 ⟩ x
          u = ∨-is-lowerbound-of-upperbounds αᵢ-below-x (⊥-is-least x)

   directify-↓-is-compact : ((i : I) → is-compact 𝓓 (α i))
                          → (j : domain directify-↓)
                          → is-compact 𝓓 (directify-↓ j)
   directify-↓-is-compact αs-are-compact j =
    directify-is-compact αs-are-compact (pr₁ j)

\end{code}

Finally if the dcpo is locally small, then the family directify-↓ can be indexed
by a small type (provided the original family was indexed by a small type).

\begin{code}

 module _
         (𝓓-is-locally-small : is-locally-small 𝓓)
         {I : 𝓥 ̇ }
         (α : I → ⟨ 𝓓 ⟩)
        where

  open is-locally-small 𝓓-is-locally-small

  directify-↓-small : (x : ⟨ 𝓓 ⟩) → (Σ l ꞉ List I , directify α l ⊑ₛ x) → ⟨ 𝓓 ⟩
  directify-↓-small x = directify α ∘ pr₁

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   directify-↓-small-≃ : domain (directify-↓ α) ≃ domain (directify-↓-small x)
   directify-↓-small-≃ =
    Σ-cong (λ l → ≃-sym ⊑ₛ-≃-⊑)

   directify-↓-small-sup : is-sup (underlying-order 𝓓) x (↓-family α)
                         → is-sup (underlying-order 𝓓) x (directify-↓-small x)
   directify-↓-small-sup x-is-sup =
    reindexed-family-sup 𝓓 directify-↓-small-≃
     (directify-↓ α) x (directify-↓-sup α x-is-sup)

   directify-↓-small-is-directed : is-Directed 𝓓 (directify-↓-small x)
   directify-↓-small-is-directed =
    reindexed-family-is-directed 𝓓 directify-↓-small-≃
     (directify-↓ α) (directify-↓-is-directed α)

\end{code}

As announced, we get that dcpos with finite joins are sup-complete.

\begin{code}

dcpo-with-finite-joins-is-sup-complete : (𝓓 : DCPO {𝓤} {𝓣})
                                       → has-finite-joins 𝓓
                                       → is-sup-complete 𝓓
dcpo-with-finite-joins-is-sup-complete 𝓓 h =
 record {
  ⋁ = sup ;
  ⋁-is-sup = λ α → directify-sup' 𝓓 h α (sup α)
                                  (∐-is-sup 𝓓 (directify-is-directed 𝓓 h α))
 }
  where
   open has-finite-joins h
   open make-family-directed
   sup : {I : 𝓥 ̇} → (I → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩
   sup {I} α = ∐ 𝓓 (directify-is-directed 𝓓 h α)

\end{code}

Finally, we re-export the directify constructions via this module for use in
other files.

\begin{code}

module sup-complete-dcpo
        (𝓓 : DCPO {𝓤} {𝓣'})
        (𝓓-is-sup-complete : is-sup-complete 𝓓)
       where

 open is-sup-complete 𝓓-is-sup-complete
 open make-family-directed
       𝓓 (sup-complete-dcpo-has-finite-joins 𝓓 𝓓-is-sup-complete)
      public

\end{code}
