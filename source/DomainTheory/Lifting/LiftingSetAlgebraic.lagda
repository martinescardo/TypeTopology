Tom de Jong, 25 & 26 January 2022.

We show that 𝟙 + X is a small compact basis for the pointed dcpo 𝓛 X. In
particular, this dcpo is algebraic.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Lifting.LiftingSetAlgebraic
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (fe : Fun-Ext)
        (𝓤 : Universe)
       where

open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

open import Lifting.Lifting 𝓤 hiding (⊥)
open import Lifting.Miscelanea 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.Monad 𝓤

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤

open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe

open import OrderedTypes.Poset fe

module _
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

 open import Lifting.UnivalentPrecategory 𝓤 X

\end{code}

The order _⊑'_ is convenient for many purposes, but it does have large truth
values. However, because _⊑_ has small truth values the dcpo 𝓛 X is still
locally small.

\begin{code}

 𝓛-is-locally-small : is-locally-small (𝓛-DCPO X-is-set)
 𝓛-is-locally-small = record { _⊑ₛ_ = _⊑_ ; ⊑ₛ-≃-⊑ = γ }
  where
   γ : {x y : 𝓛 X} → (x ⊑ y) ≃ (x ⊑' y)
   γ {x} {y} = logically-equivalent-props-are-equivalent
                (⊑-prop-valued fe fe X-is-set x y)
                (⊑'-prop-valued X-is-set)
                ⊑-to-⊑' ⊑'-to-⊑

\end{code}

A small compact basis for 𝓛 X will be given by [⊥ , η] : 𝟙 + X → 𝓛 X.

\begin{code}

 κ : 𝟙{𝓤} + X → 𝓛 X
 κ (inl ⋆) = ⊥ (𝓛-DCPO⊥ X-is-set)
 κ (inr x) = η x

 κ⁺ : (l : 𝓛 X) → (Σ i ꞉ (𝟙 + X) , κ i ⊑' l) → 𝓛 X
 κ⁺ l = κ ∘ pr₁

 κ⁺-is-directed : (l : 𝓛 X) → is-Directed (𝓛-DCPO X-is-set) (κ⁺ l)
 κ⁺-is-directed l = inh , semidir
  where
   inh : ∃ i ꞉ (𝟙 + X) , κ i ⊑' l
   inh = ∣ inl ⋆ , ⊥-is-least (𝓛-DCPO⊥ X-is-set) l ∣
   semidir : is-semidirected _⊑'_ (κ⁺ l)
   semidir (inl ⋆ , u) (inl ⋆ , v) = ∣ (inl ⋆ , u)
                                     , ⊑'-is-reflexive , ⊑'-is-reflexive ∣
   semidir (inl ⋆ , u) (inr y , v) = ∣ (inr y , v)
                                     , ⊥-is-least (𝓛-DCPO⊥ X-is-set) (η y)
                                     , ⊑'-is-reflexive ∣
   semidir (inr x , u) (inl ⋆ , pr₄) = ∣ (inr x , u)
                                       , ⊑'-is-reflexive
                                       , (⊥-is-least (𝓛-DCPO⊥ X-is-set) (η x)) ∣
   semidir (inr x , u) (inr y , v) = ∣ (inr x , u)
                                     , ⊑'-is-reflexive , (λ _ → e) ∣
    where
     e = η y ＝⟨ v ⋆      ⟩
         l   ＝⟨ (u ⋆) ⁻¹ ⟩
         η x ∎

 κ⁺-sup : (l : 𝓛 X) → is-sup _⊑'_ l (κ⁺ l)
 κ⁺-sup l = ub , lb-of-ubs
  where
   ub : (i : domain (κ⁺ l)) → κ⁺ l i ⊑' l
   ub (i , u) = u
   lb-of-ubs : is-lowerbound-of-upperbounds _⊑'_ l (κ⁺ l)
   lb-of-ubs m m-is-ub l-is-def = l                    ＝⟨ ⦅1⦆ ⟩
                                  η (value l l-is-def) ＝⟨ ⦅2⦆ ⟩
                                  m                    ∎
    where
     ⦅1⦆ : l ＝ η (value l l-is-def)
     ⦅1⦆ = is-defined-η-＝ l-is-def
     ⦅2⦆ : η (value l l-is-def) ＝ m
     ⦅2⦆ = m-is-ub (inr (value l l-is-def) , v) ⋆
      where
       v : κ (inr (value l l-is-def)) ⊑' l
       v _ = ⦅1⦆ ⁻¹

 ηs-are-compact : (x : X) → is-compact (𝓛-DCPO X-is-set) (η x)
 ηs-are-compact x I α δ ηx-below-∐α =
  ∥∥-functor h (＝-to-is-defined (ηx-below-∐α ⋆) ⋆)
   where
    h : (Σ i ꞉ I , is-defined (α i))
      → (Σ i ꞉ I , η x ⊑' α i)
    h (i , pᵢ) = i , (λ _ → e)
     where
      e : η x ＝ α i
      e = η x                      ＝⟨ ηx-below-∐α ⋆ ⟩
          lifting-sup X-is-set α δ ＝⟨ e'            ⟩
          α i                      ∎
       where
        e' = (family-defined-somewhere-sup-＝ X-is-set δ i pᵢ) ⁻¹

 compact-if-in-image-of-κ : (l : 𝓛 X)
                          → l ∈image κ
                          → is-compact (𝓛-DCPO X-is-set) l
 compact-if-in-image-of-κ l l-in-image-of-κ =
  ∥∥-rec (being-compact-is-prop (𝓛-DCPO X-is-set) l) γ l-in-image-of-κ
   where
    γ : (Σ i ꞉ domain κ , κ i ＝ l)
      → is-compact (𝓛-DCPO X-is-set) l
    γ (inl ⋆ , refl) = ⊥-is-compact (𝓛-DCPO⊥ X-is-set)
    γ (inr x , refl) = ηs-are-compact x

 in-image-of-κ-if-compact : (l : 𝓛 X)
                          → is-compact (𝓛-DCPO X-is-set) l
                          → l ∈image κ
 in-image-of-κ-if-compact l@(P , φ , P-is-prop) l-cpt = ∥∥-functor goal claim
  where
   I : 𝓤 ̇
   I = 𝟙{𝓤} + P
   α : I → 𝓛 X
   α = add-⊥ (𝓛-DCPO⊥ X-is-set) (η ∘ φ)
   δ : is-Directed (𝓛-DCPO X-is-set) α
   -- We use --lossy-unification here to speed up typechecking
   δ = add-⊥-is-directed (𝓛-DCPO⊥ X-is-set) σ
    where
     σ : is-semidirected _⊑'_ (η ∘ φ)
     σ = subsingleton-indexed-is-semidirected (𝓛-DCPO X-is-set) (η ∘ φ) P-is-prop
   l-below-∐α : l ⊑' ∐ (𝓛-DCPO X-is-set) δ
   l-below-∐α p = l                      ＝⟨ ⦅1⦆ ⟩
                  η (φ p)                ＝⟨ ⦅2⦆ ⟩
                  ∐ (𝓛-DCPO X-is-set) δ ∎
    where
     ⦅1⦆ = is-defined-η-＝ p
     ⦅2⦆ = ∐-is-upperbound (𝓛-DCPO X-is-set) δ (inr p) ⋆
   claim : ∃ i ꞉ I , l ⊑' α i
   claim = l-cpt I α δ l-below-∐α
   goal : (Σ i ꞉ I , l ⊑' α i)
        → (Σ k ꞉ domain κ , κ k ＝ l)
   goal (inl ⋆ , lᵢ) =
    (inl ⋆ , ⊑'-is-antisymmetric (⊥-is-least (𝓛-DCPO⊥ X-is-set) l) lᵢ)
   goal (inr p , lᵢ) =
    (inr (φ p) , ((lᵢ p) ⁻¹))

 κ-is-small-compact-basis : is-small-compact-basis (𝓛-DCPO X-is-set) κ
 κ-is-small-compact-basis =
  record
   { basis-is-compact = λ b → compact-if-in-image-of-κ (κ b) ∣ b , refl ∣
   ; ⊑ᴮ-is-small      = λ l b → ⌜ local-smallness-equivalent-definitions
                                 (𝓛-DCPO X-is-set) ⌝
                              𝓛-is-locally-small (κ b) l
   ; ↓ᴮ-is-directed   = κ⁺-is-directed
   ; ↓ᴮ-is-sup        = κ⁺-sup
   }

 𝓛-has-specified-small-compact-basis : has-specified-small-compact-basis
                                         (𝓛-DCPO X-is-set)
 𝓛-has-specified-small-compact-basis = ((𝟙 + X) , κ , κ-is-small-compact-basis)

 𝓛-structurally-algebraic : structurally-algebraic (𝓛-DCPO X-is-set)
 𝓛-structurally-algebraic =
  structurally-algebraic-if-specified-small-compact-basis
   (𝓛-DCPO X-is-set) 𝓛-has-specified-small-compact-basis

 𝓛-is-algebraic-dcpo : is-algebraic-dcpo (𝓛-DCPO X-is-set)
 𝓛-is-algebraic-dcpo = ∣ 𝓛-structurally-algebraic ∣

\end{code}

TODO: Show that freely adding a least element to a dcpo gives an algebraic dcpo
      with a small compact basis if the original dcpo had a small compact basis.
      (Do so in another file, e.g. LiftingDcpoAlgebraic.lagda).
