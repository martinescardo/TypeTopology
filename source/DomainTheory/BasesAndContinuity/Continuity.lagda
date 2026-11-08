Tom de Jong, early January 2022.

We define when a dcpo is (structurally) continuous/algebraic and prove the
nullary, unary and binary interpolation properties of the way-below relation in
a continuous dcpo.

We also show that in a continuous dcpo being locally small is equivalent to the
way-below relation having small truth values. Further, being (structurally)
continuous is preserved by taking continuous retracts.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.Continuity
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.IndCompletion pt fe 𝓥

\end{code}

We first define an untruncated, non-propositional, version of continuity for
dcpos, which we call continuity data. The notion of a continuous dcpo will
then be given by truncating the type of continuity data.

The motivation for our definition of continuity is discussed in
ContinuityDiscussion.lagda.

We use record syntax to have descriptively named projections available without
having to add them as boilerplate.

\begin{code}

record continuity-data  (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇ where
 field
  index-of-approximating-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  approximating-family : (x : ⟨ 𝓓 ⟩)
                       → (index-of-approximating-family x) → ⟨ 𝓓 ⟩
  approximating-family-is-directed : (x : ⟨ 𝓓 ⟩)
                                   → is-Directed 𝓓 (approximating-family x)
  approximating-family-is-way-below : (x : ⟨ 𝓓 ⟩)
                                    → is-way-upperbound 𝓓 x
                                       (approximating-family x)
  approximating-family-∐-＝ : (x : ⟨ 𝓓 ⟩)
                           → ∐ 𝓓 (approximating-family-is-directed x) ＝ x

 approximating-family-∐-⊑ : (x : ⟨ 𝓓 ⟩)
                          → ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ x
 approximating-family-∐-⊑ x = ＝-to-⊑ 𝓓 (approximating-family-∐-＝ x)

 approximating-family-∐-⊒ : (x : ⟨ 𝓓 ⟩)
                          → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (approximating-family-is-directed x)
 approximating-family-∐-⊒ x = ＝-to-⊒ 𝓓 (approximating-family-∐-＝ x)

\end{code}

NB. We previously used the terminology "structural continuity" instead of
"continuity data".

We now prefer the latter because the word "structure" suggests that we are
interested in preserving this data, but we are not. (E.g., preserving this data
would mean preserving the way-below relation which Scott continuous functions
rarely do, ruling out constant functions with non-compact values for example.)
We only want to stress that we are not dealing with a property and the word
"data" is better for this.

At the moment the code and its comments still use the old terminology, so for
now we have following aliases, although in the future we will likely update the
terminology throughout the development.

\begin{code}

module structurally-continuous = continuity-data
structurally-continuous = continuity-data

is-continuous-dcpo : DCPO {𝓤} {𝓣} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-continuous-dcpo 𝓓 = ∥ structurally-continuous 𝓓 ∥

being-continuous-dcpo-is-prop : (𝓓 : DCPO {𝓤} {𝓣})
                              → is-prop (is-continuous-dcpo 𝓓)
being-continuous-dcpo-is-prop 𝓓 = ∥∥-is-prop

\end{code}

Added 25 March 2025 by Tom de Jong following a discussion with Martin Escardo.

In particular, two continuous dcpos are equal precisely when they are
isomorphic.

\begin{code}

open import UF.Univalence

characterization-of-continuous-DCPO-＝ : Univalence
                                       → (𝓓 𝓔 : DCPO {𝓤} {𝓣})
                                       → (c₁ : is-continuous-dcpo 𝓓)
                                       → (c₂ : is-continuous-dcpo 𝓔)
                                       → ((𝓓 , c₁) ＝ (𝓔 , c₂)) ≃ (𝓓 ≃ᵈᶜᵖᵒ 𝓔)
characterization-of-continuous-DCPO-＝ ua 𝓓 𝓔 c₁ c₂ =
 ((𝓓 , c₁) ＝ (𝓔 , c₂)) ≃⟨ I ⟩
 (𝓓 ＝ 𝓔)               ≃⟨ II ⟩
 (𝓓 ≃ᵈᶜᵖᵒ 𝓔)            ■
  where
   open import UF.Embeddings using (to-subtype-＝-≃)
   I  = ≃-sym (to-subtype-＝-≃ being-continuous-dcpo-is-prop)
   II = characterization-of-DCPO-＝ ua 𝓓 𝓔

\end{code}

End of addition.

Similarly, we define when a dcpo has algebraicity data where the
approximating family is required to consist of compact elements.

\begin{code}

record algebraicity-data (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇ where
 field
  index-of-compact-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  compact-family : (x : ⟨ 𝓓 ⟩) → (index-of-compact-family x) → ⟨ 𝓓 ⟩
  compact-family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (compact-family x)
  compact-family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index-of-compact-family x)
                            → is-compact 𝓓 (compact-family x i)
  compact-family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (compact-family-is-directed x) ＝ x

 compact-family-is-upperbound : (x : ⟨ 𝓓 ⟩)
                              → is-upperbound (underlying-order 𝓓)
                                              x (compact-family x)
 compact-family-is-upperbound x i =
  compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
  ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
  x                                  ∎⟨ 𝓓 ⟩
   where
    ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
    ⦅2⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

\end{code}

NB. We previously used the terminology "structural algebraicity" instead of
"algebraicity data". Again, we now prefer the latter for the reasons explained
above in the other comment on terminology.

At the moment the code and its comments still use the old terminology, so for
now we have following aliases, although in the future we will likely update the
terminology throughout the development.

\begin{code}

module structurally-algebraic = algebraicity-data
structurally-algebraic = algebraicity-data

is-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic-dcpo 𝓓 = ∥ structurally-algebraic 𝓓 ∥

structurally-continuous-if-structurally-algebraic :
   (𝓓 : DCPO {𝓤} {𝓣})
 → structurally-algebraic 𝓓 → structurally-continuous 𝓓
structurally-continuous-if-structurally-algebraic 𝓓 sa =
 record
  { index-of-approximating-family     = index-of-compact-family
  ; approximating-family              = compact-family
  ; approximating-family-is-directed  = compact-family-is-directed
  ; approximating-family-is-way-below = γ
  ; approximating-family-∐-＝          = compact-family-∐-＝
 }
  where
   open structurally-algebraic sa
   γ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (compact-family x)
   γ x i = ≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
                      (compact-family-is-upperbound x i)

is-continuous-dcpo-if-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                                     → is-algebraic-dcpo 𝓓
                                     → is-continuous-dcpo 𝓓
is-continuous-dcpo-if-algebraic-dcpo 𝓓 =
 ∥∥-functor (structurally-continuous-if-structurally-algebraic 𝓓)

\end{code}

We characterize the order in a structurally continuous dcpo using approximating
families.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 structurally-continuous-⊑-criterion :
    {x y : ⟨ 𝓓 ⟩}
  → ((i : index-of-approximating-family x) → approximating-family x i ⊑⟨ 𝓓 ⟩ y)
  → x ⊑⟨ 𝓓 ⟩ y
 structurally-continuous-⊑-criterion {x} {y} l =
  transport (λ - → - ⊑⟨ 𝓓 ⟩ y) (approximating-family-∐-＝ x) γ
   where
    γ : ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ y
    γ = ∐-is-lowerbound-of-upperbounds 𝓓 (approximating-family-is-directed x) y l

 structurally-continuous-⊑-criterion' :
    {x y : ⟨ 𝓓 ⟩}
  → ((i : index-of-approximating-family x) → approximating-family x i ≪⟨ 𝓓 ⟩ y)
  → x ⊑⟨ 𝓓 ⟩ y
 structurally-continuous-⊑-criterion' {x} {y} l =
  structurally-continuous-⊑-criterion (λ i → ≪-to-⊑ 𝓓 (l i))

 structurally-continuous-⊑-criterion'-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ⊑⟨ 𝓓 ⟩ y
  → ((i : index-of-approximating-family x) → approximating-family x i ≪⟨ 𝓓 ⟩ y)
 structurally-continuous-⊑-criterion'-converse {x} {y} l i =
  ≪-⊑-to-≪ 𝓓 (approximating-family-is-way-below x i) l

 structurally-continuous-⊑-criterion-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ⊑⟨ 𝓓 ⟩ y
  → ((i : index-of-approximating-family x) → approximating-family x i ⊑⟨ 𝓓 ⟩ y)
 structurally-continuous-⊑-criterion-converse {x} {y} l i =
  ≪-to-⊑ 𝓓 (structurally-continuous-⊑-criterion'-converse l i)

\end{code}

We also characterize the way-below relation in terms of the order and
approximating families.

\begin{code}

 structurally-continuous-≪-criterion :
    {x y : ⟨ 𝓓 ⟩}
  → (∃ i ꞉ index-of-approximating-family y , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
  → x ≪⟨ 𝓓 ⟩ y
 structurally-continuous-≪-criterion {x} {y} = ∥∥-rec (≪-is-prop-valued 𝓓) γ
  where
   γ : (Σ i ꞉ index-of-approximating-family y
            , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
     → x ≪⟨ 𝓓 ⟩ y
   γ (i , l) = ⊑-≪-to-≪ 𝓓 l (approximating-family-is-way-below y i)

 structurally-continuous-≪-criterion-converse :
    {x y : ⟨ 𝓓 ⟩}
  → x ≪⟨ 𝓓 ⟩ y
  → (∃ i ꞉ index-of-approximating-family y , x ⊑⟨ 𝓓 ⟩ approximating-family y i)
 structurally-continuous-≪-criterion-converse {x} {y} wb =
  wb (index-of-approximating-family y) (approximating-family y)
     (approximating-family-is-directed y) (approximating-family-∐-⊒ y)

\end{code}

We set out to prove nullary, unary and binary interpolation for (structurally)
continuous dcpos.

\begin{code}

 ≪-nullary-interpolation-str : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation-str x =
  ∥∥-functor γ (inhabited-if-Directed 𝓓 (approximating-family x)
                                        (approximating-family-is-directed x))
   where
    γ : index-of-approximating-family x → Σ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
    γ i = (approximating-family x i , approximating-family-is-way-below x i)

\end{code}

Our proof of the unary interpolation property is inspired by Proposition 2.12 of
"Continuous categories and Exponentiable Toposes" by Peter Johnstone and André
Joyal. The idea is to approximate y by a family αᵢ, approximate each αᵢ by
another family βᵢⱼ, and finally to approximate y as the "sum" of the βᵢⱼs.

\begin{code}

 ≪-unary-interpolation-str : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                           → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation-str {x} {y} x-way-below-y = interpol
  where
   Iʸ : 𝓥 ̇
   Iʸ = index-of-approximating-family y
   αʸ : Iʸ → ⟨ 𝓓 ⟩
   αʸ = approximating-family y
   δʸ : is-Directed 𝓓 αʸ
   δʸ = approximating-family-is-directed y
   J : (i : Iʸ) → 𝓥 ̇
   J i = index-of-approximating-family (αʸ i)
   β : (i : Iʸ) → J i → ⟨ 𝓓 ⟩
   β i = approximating-family (αʸ i)
   δ : (i : Iʸ) → is-Directed 𝓓 (β i)
   δ i = approximating-family-is-directed (αʸ i)

   open Ind-completion 𝓓
   𝓑 : Iʸ → Ind
   𝓑 i = J i , β i , δ i
   𝓘 : Ind
   𝓘 = Ind-∐ 𝓑 (inhabited-if-Directed 𝓓 αʸ δʸ , σ)
    where
     σ : is-semidirected _≲_ 𝓑
     σ i₁ i₂ = ∥∥-functor r (semidirected-if-Directed 𝓓 αʸ δʸ i₁ i₂)
      where
       r : (Σ i ꞉ Iʸ , (αʸ i₁ ⊑⟨ 𝓓 ⟩ αʸ i) × (αʸ i₂ ⊑⟨ 𝓓 ⟩ αʸ i))
         → Σ i ꞉ Iʸ , (𝓑 i₁ ≲ 𝓑 i) × (𝓑 i₂ ≲ 𝓑 i)
       r (i , u , v) = i , l₁ , l₂
        where
         w = approximating-family-∐-⊒ (αʸ i)
         l₁ : 𝓑 i₁ ≲ 𝓑 i
         l₁ j = approximating-family-is-way-below (αʸ i₁) j (J i) (β i) (δ i)
                 (αʸ i₁     ⊑⟨ 𝓓 ⟩[ u ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)
         l₂ : 𝓑 i₂ ≲ 𝓑 i
         l₂ j = approximating-family-is-way-below (αʸ i₂) j (J i) (β i) (δ i)
                 (αʸ i₂     ⊑⟨ 𝓓 ⟩[ v ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)

   K : 𝓥 ̇
   K = pr₁ 𝓘
   γ : K → ⟨ 𝓓 ⟩
   γ = pr₁ (pr₂ 𝓘)
   γ-is-directed : is-Directed 𝓓 γ
   γ-is-directed = pr₂ (pr₂ 𝓘)

   y-below-∐-of-γ : y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
   y-below-∐-of-γ = structurally-continuous-⊑-criterion u
    where
     u : (i : Iʸ) → αʸ i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
     u i = structurally-continuous-⊑-criterion v
      where
       v : (j : J i) → β i j ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
       v j = ∐-is-upperbound 𝓓 γ-is-directed (i , j)

   x-below-γ : ∃ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k
   x-below-γ = x-way-below-y K γ γ-is-directed y-below-∐-of-γ

   interpol : ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
   interpol = ∥∥-functor r lemma
    where
     r : (Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                               × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                               × (αʸ i ≪⟨ 𝓓 ⟩ y))
       → Σ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
     r (i , j , u , v , w) = (αʸ i , ⊑-≪-to-≪ 𝓓 u v , w)
     lemma : ∥ Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                    × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                    × (αʸ i ≪⟨ 𝓓 ⟩ y) ∥
     lemma = ∥∥-functor s x-below-γ
      where
       s : (Σ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k)
         → Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                × (αʸ i ≪⟨ 𝓓 ⟩ y)
       s ((i , j) , l) = (i , j , l ,
                          approximating-family-is-way-below (αʸ i) j ,
                          approximating-family-is-way-below y i)

\end{code}

From the unary interpolation property, one quickly derives the binary version,
although the proof involves eliminating several propositional truncations. For
that reason, we use so-called do-notation (which is possible because ∥-∥ is a
monad) to shorten the proof below. If we write x ← t, then x : X and t : ∥ X ∥.

\begin{code}

 ≪-binary-interpolation-str : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                            → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                          × (y ≪⟨ 𝓓 ⟩ d)
                                          × (d ≪⟨ 𝓓 ⟩ z)
 ≪-binary-interpolation-str {x} {y} {z} x-way-below-z y-way-below-z = do
  let δ = approximating-family-is-directed z
  let l = approximating-family-∐-⊒ z
  (d₁ , x-way-below-d₁ , d₁-way-below-z) ← ≪-unary-interpolation-str
                                            x-way-below-z
  (d₂ , y-way-below-d₂ , d₂-way-below-z) ← ≪-unary-interpolation-str
                                            y-way-below-z

  (i₁ , d₁-below-zⁱ₁)                    ← d₁-way-below-z _ _ δ l
  (i₂ , d₂-below-zⁱ₂)                    ← d₂-way-below-z _ _ δ l

  (i , zⁱ₁-below-zⁱ , zⁱ₂-below-zⁱ)      ← semidirected-if-Directed 𝓓 _ δ i₁ i₂
  let α = approximating-family z
  let d₁-below-αⁱ = d₁   ⊑⟨ 𝓓 ⟩[ d₁-below-zⁱ₁ ]
                    α i₁ ⊑⟨ 𝓓 ⟩[ zⁱ₁-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  let d₂-below-αⁱ = d₂   ⊑⟨ 𝓓 ⟩[ d₂-below-zⁱ₂ ]
                    α i₂ ⊑⟨ 𝓓 ⟩[ zⁱ₂-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  ∣ approximating-family z i , ≪-⊑-to-≪ 𝓓 x-way-below-d₁ d₁-below-αⁱ
                             , ≪-⊑-to-≪ 𝓓 y-way-below-d₂ d₂-below-αⁱ
                             , approximating-family-is-way-below z i ∣

\end{code}

The interpolation properties for continuous dcpos now follow immediately.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (c : is-continuous-dcpo 𝓓)
       where

 ≪-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation x =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-nullary-interpolation-str 𝓓 C x) c

 ≪-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                       → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation x-way-below-y =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-unary-interpolation-str 𝓓 C x-way-below-y) c

 ≪-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                        → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                      × (y ≪⟨ 𝓓 ⟩ d)
                                      × (d ≪⟨ 𝓓 ⟩ z)
 ≪-binary-interpolation {x} {y} {z} u v =
  ∥∥-rec ∥∥-is-prop (λ C → ≪-binary-interpolation-str 𝓓 C u v) c

\end{code}

We show that in a (structurally) continuous dcpo local smallness is logically
equivalent to the way-below relation having small values.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 ≪-is-small-valued-str : is-locally-small 𝓓
                       → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
 ≪-is-small-valued-str ls x y = (∃ i ꞉ I , x ⊑ₛ α i) , ψ
  where
   open is-locally-small ls
   I : 𝓥 ̇
   I = index-of-approximating-family y
   α : I → ⟨ 𝓓 ⟩
   α = approximating-family y
   ψ = (∃ i ꞉ I , x ⊑ₛ      α i) ≃⟨ ∃-cong pt (λ i → ⊑ₛ-≃-⊑) ⟩
       (∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩  α i) ≃⟨ e ⟩
       x ≪⟨ 𝓓 ⟩ y                ■
    where
     e = logically-equivalent-props-are-equivalent ∃-is-prop (≪-is-prop-valued 𝓓)
          (structurally-continuous-≪-criterion 𝓓 C)
          (structurally-continuous-≪-criterion-converse 𝓓 C)

 ≪-is-small-valued-str-converse : ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                                → is-locally-small 𝓓
 ≪-is-small-valued-str-converse ≪-is-small-valued =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
   where
    _≪ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
    x ≪ₛ y = pr₁ (≪-is-small-valued x y)
    ≪ₛ-≃-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y ≃ x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-≃-≪ {x} {y} = pr₂ (≪-is-small-valued x y)
    γ : (x y : ⟨ 𝓓 ⟩) → is-small (x ⊑⟨ 𝓓 ⟩ y)
    γ x y = (∀ (i : I) → α i ≪ₛ y) , ψ
     where
      I : 𝓥 ̇
      I = index-of-approximating-family x
      α : I → ⟨ 𝓓 ⟩
      α = approximating-family x
      ψ = (∀ (i : I) → α i ≪ₛ     y) ≃⟨ Π-cong fe fe (λ i → ≪ₛ-≃-≪) ⟩
          (∀ (i : I) → α i ≪⟨ 𝓓 ⟩ y) ≃⟨ e ⟩
          x ⊑⟨ 𝓓 ⟩ y                 ■
       where
        e = logically-equivalent-props-are-equivalent
             (Π-is-prop fe (λ i → ≪-is-prop-valued 𝓓)) (prop-valuedness 𝓓 x y)
             (structurally-continuous-⊑-criterion' 𝓓 C)
             (structurally-continuous-⊑-criterion'-converse 𝓓 C)

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
        (c : is-continuous-dcpo 𝓓)
       where

 open import UF.Size hiding (is-small ; is-locally-small)

 abstract -- for performance
  ≪-is-small-valued : is-locally-small 𝓓
                    → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
  ≪-is-small-valued ls x y = ∥∥-rec p (λ C → ≪-is-small-valued-str 𝓓 C ls x y) c
   where
    p : is-prop (is-small (x ≪⟨ 𝓓 ⟩ y))
    p = prop-being-small-is-prop (λ _ → pe) (λ _ _ → fe)
         (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)

  ≪-is-small-valued-converse : ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                             → is-locally-small 𝓓
  ≪-is-small-valued-converse ws =
   ∥∥-rec (being-locally-small-is-prop 𝓓 (λ _ → pe))
    (λ C → ≪-is-small-valued-str-converse 𝓓 C ws) c

\end{code}

Finally, we prove that (structural) continuity is preserved by continuous
retracts.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 structural-continuity-of-dcpo-preserved-by-continuous-retract :
    structurally-continuous 𝓔
  → structurally-continuous 𝓓
 structural-continuity-of-dcpo-preserved-by-continuous-retract C =
  record
   { index-of-approximating-family     = λ x → index-of-approximating-family
                                                (s x)
   ; approximating-family              = λ x → r ∘ approximating-family (s x)
   ; approximating-family-is-directed  = lemma₁
   ; approximating-family-is-way-below = lemma₂
   ; approximating-family-∐-＝          = lemma₃
  }
   where
    open structurally-continuous C
    α : (y : ⟨ 𝓔 ⟩) → index-of-approximating-family y → ⟨ 𝓔 ⟩
    α = approximating-family
    lemma₁ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (r ∘ α (s x))
    lemma₁ x = image-is-directed' 𝓔 𝓓 𝕣
                (approximating-family-is-directed (s x))
    lemma₂ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (r ∘ α (s x))
    lemma₂ x i = continuous-retraction-≪-criterion 𝓓 𝓔 ρ (α (s x) i) x
                  (approximating-family-is-way-below (s x) i)
    lemma₃ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (lemma₁ x) ＝ x
    lemma₃ x = ∐ 𝓓 (lemma₁ x) ＝⟨ ⦅1⦆ ⟩
               r (∐ 𝓔 δ)      ＝⟨ ⦅2⦆ ⟩
               r (s x)        ＝⟨ ⦅3⦆ ⟩
               x              ∎
     where
      δ : is-Directed 𝓔 (α (s x))
      δ = approximating-family-is-directed (s x)
      ⦅1⦆ = (continuous-∐-＝ 𝓔 𝓓 𝕣 δ) ⁻¹
      ⦅2⦆ = ap r (approximating-family-∐-＝ (s x))
      ⦅3⦆ = s-section-of-r x

 continuity-of-dcpo-preserved-by-continuous-retract : is-continuous-dcpo 𝓔
                                                    → is-continuous-dcpo 𝓓
 continuity-of-dcpo-preserved-by-continuous-retract =
  ∥∥-functor structural-continuity-of-dcpo-preserved-by-continuous-retract

\end{code}

Added 8 July 2024.

The purpose of the following construction is to show that structural continuity
is not a property of a dcpo.

\begin{code}

structurally-continuous-+-construction :
  (𝓓 : DCPO {𝓤} {𝓣})
 → structurally-continuous 𝓓
 → structurally-continuous 𝓓
structurally-continuous-+-construction 𝓓 sc =
 record
  { index-of-approximating-family = λ x → I x + I x
  ; approximating-family = [α,α]
  ; approximating-family-is-directed = δ'
  ; approximating-family-is-way-below = wb'
  ; approximating-family-∐-＝ = eq'
 }
  where
   open structurally-continuous sc
         renaming (index-of-approximating-family to I ;
                   approximating-family to α ;
                   approximating-family-is-directed to δ ;
                   approximating-family-is-way-below to wb ;
                   approximating-family-∐-＝ to eq)
   [α,α] : (x : ⟨ 𝓓 ⟩) → I x + I x → ⟨ 𝓓 ⟩
   [α,α] x = cases (α x) (α x)

   lemma₁ : {x : ⟨ 𝓓 ⟩} (i : I x) → ∃ j ꞉ I x + I x , α x i ⊑⟨ 𝓓 ⟩ [α,α] x j
   lemma₁ {x} i = ∣ inl i , reflexivity 𝓓 (α x i) ∣
   lemma₂ : {x : ⟨ 𝓓 ⟩} (j : I x + I x) → ∃ i ꞉ I x , [α,α] x j ⊑⟨ 𝓓 ⟩ α x i
   lemma₂ {x} (inl i) = ∣ i , reflexivity 𝓓 (α x i) ∣
   lemma₂ {x} (inr i) = ∣ i , reflexivity 𝓓 (α x i) ∣

   δ' : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 ([α,α] x)
   δ' x = directed-if-bicofinal 𝓓 lemma₁ lemma₂ (δ x)

   wb' : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x ([α,α] x)
   wb' x (inl i) = wb x i
   wb' x (inr i) = wb x i

   eq' : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (δ' x) ＝ x
   eq' x = ∐-＝-if-bicofinal 𝓓 lemma₂ lemma₁ (δ' x) (δ x) ∙ eq x

\end{code}
