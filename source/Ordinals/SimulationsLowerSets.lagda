Tom de Jong, 25-28 September 2026.

We characterize the type of simulations into a fixed ordinal α as
the type of lower-closed subsets of α.

TODO. Mention HoTT Book exercise.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

module Ordinals.SimulationsLowerSets
        (ua : Univalence)
       where

open import MLTT.Spartan

open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

module _
        (α : Ordinal 𝓤)
       where

 is-lower-set : 𝓟 ⟨ α ⟩ → 𝓤 ̇
 is-lower-set S = (a b : ⟨ α ⟩) → b ∈ S → a ≺⟨ α ⟩ b → a ∈ S

 being-lower-set-is-prop : (S : 𝓟 (⟨ α ⟩)) → is-prop (is-lower-set S)
 being-lower-set-is-prop S =
  Π₄-is-prop fe' (λ x _ _ _ → ∈-is-prop S x)

 Lower-Set : 𝓤 ⁺ ̇
 Lower-Set = Σ S ꞉ 𝓟 ⟨ α ⟩ , is-lower-set S

 lower-set-ordinal : Lower-Set → Ordinal 𝓤
 lower-set-ordinal (S , lc) =
  (𝕋 S ,
   _≺_ ,
   subtype-order-is-prop-valued α (_∈ S) ,
   subtype-order-is-well-founded α (_∈ S) ,
   ext ,
   subtype-order-is-transitive α (_∈ S))
    where
     ι : 𝕋 S → ⟨ α ⟩
     ι = 𝕋-to-carrier S
     _≺_ = subtype-order α (_∈ S)
     ≼-lemma : (x y : 𝕋 S) → ((z : 𝕋 S) → z ≺ x → z ≺ y) → ι x ≼⟨ α ⟩ ι y
     ≼-lemma (x , s) _ u a l = u (a , t) l
      where
       t : a ∈ S
       t = lc a x s l
     ext : is-extensional _≺_
     ext x y u v =
      to-subtype-＝
       (∈-is-prop S)
       (Extensionality α (ι x) (ι y) (≼-lemma x y u) (≼-lemma y x v))

 lower-set-ordinal-⊴ : (S : Lower-Set) → lower-set-ordinal S ⊴ α
 lower-set-ordinal-⊴ (S , lc) = ι , ι-is-initial-segment , ι-is-order-preserving
  where
   σ = lower-set-ordinal (S , lc)
   ι : ⟨ σ ⟩ → ⟨ α ⟩
   ι = 𝕋-to-carrier S
   ι-is-order-preserving : is-order-preserving σ α ι
   ι-is-order-preserving x y l = l
   ι-is-initial-segment : is-initial-segment σ α ι
   ι-is-initial-segment (x , s) a l = (a , t) , (l , refl)
    where
     t : a ∈ S
     t = lc a x s l

\end{code}

TODO. COMMENT

\begin{code}

 module images-of-simulations
         (pt : propositional-truncations-exist)
        where
  open PropositionalTruncation pt
  open import UF.ImageAndSurjection pt
  open 𝓟-image pt public

  module _
          (β : Ordinal 𝓤)
          (𝕗 : β ⊴ α)
         where

   private
    f : ⟨ β ⟩ → ⟨ α ⟩
    f = [ β , α ]⟨ 𝕗 ⟩
    f-sim : is-simulation β α f
    f-sim = [ β , α ]⟨ 𝕗 ⟩-is-simulation

   image-of-simulation-is-lower-set : is-lower-set (image-as-subset f)
   image-of-simulation-is-lower-set a b a-in-im l =
    ∥∥-functor I a-in-im
     where
      I : (Σ y ꞉ ⟨ β ⟩ , f y ＝ b)
        → Σ x ꞉ ⟨ β ⟩ , f x ＝ a
      I (y , refl) = (pr₁ II , pr₂ (pr₂ II))
       where
        II : Σ x ꞉ ⟨ β ⟩ , (x ≺⟨ β ⟩ y) × (f x ＝ a)
        II = simulations-are-initial-segments β α f f-sim y a l

   image-of-simulation-lower-set : Lower-Set
   image-of-simulation-lower-set =
    (image-as-subset f , image-of-simulation-is-lower-set)

   image-of-simulation-ordinal : Ordinal 𝓤
   image-of-simulation-ordinal = lower-set-ordinal image-of-simulation-lower-set

  image-of-simulation-ordinal-≃ₒ
   : (β : Ordinal 𝓤) (f : β ⊴ α) → β ≃ₒ image-of-simulation-ordinal β f
  image-of-simulation-ordinal-≃ₒ β 𝕗@(f , f-sim) =
   (ι , order-preserving-reflecting-equivs-are-order-equivs β σ ι I II III)
    where
     σ = image-of-simulation-ordinal β 𝕗
     ι : ⟨ β ⟩ → ⟨ σ ⟩
     ι = corestriction f

     I : is-equiv ι
     I = surjective-embeddings-are-equivs ι
          (factor-is-embedding ι (restriction f)
            (simulations-are-embeddings fe β α f f-sim)
            (restrictions-are-embeddings f))
          (corestrictions-are-surjections f)

     II : is-order-preserving β σ ι
     II = simulations-are-order-preserving β α f f-sim

     III : is-order-reflecting β σ ι
     III = simulations-are-order-reflecting β α f f-sim

\end{code}

TODO. Comment

\begin{code}

simulations-as-lower-sets
 : propositional-truncations-exist
 → (α : Ordinal 𝓤)
 → (Σ β ꞉ Ordinal 𝓤 , β ⊴ α) ≃ Lower-Set α
simulations-as-lower-sets {𝓤} pt α = φ , qinvs-are-equivs φ (ψ , I , II)
 where
  open images-of-simulations α pt
  φ : (Σ β ꞉ Ordinal 𝓤 , β ⊴ α) → Lower-Set α
  φ (β , f) = image-of-simulation-lower-set β f

  ψ : Lower-Set α → (Σ β ꞉ Ordinal 𝓤 , β ⊴ α)
  ψ S = (lower-set-ordinal α S , lower-set-ordinal-⊴ α S)

  I : ψ ∘ φ ∼ id
  I (β , 𝕗) =
   to-subtype-＝
    (λ γ → ⊴-is-prop-valued γ α)
    (eqtoidₒ (ua 𝓤) fe' _ β
      (≃ₒ-sym β (lower-set-ordinal α (φ (β , 𝕗)))
                (image-of-simulation-ordinal-≃ₒ β 𝕗)))

  II : φ ∘ ψ ∼ id
  II (S , lc) =
   to-subtype-＝ (being-lower-set-is-prop α)
                 (𝕋-to-carrier-section-of-image-as-subset pt {𝓤} ua S)

\end{code}

TODO. Comment

\begin{code}

the-type-of-simulations-is-small : propositional-truncations-exist
                                 → Ω-resizing 𝓤
                                 → (α : Ordinal 𝓤)
                                 → is-small (Σ β ꞉ Ordinal 𝓤 , β ⊴ α)
the-type-of-simulations-is-small {𝓤} pt res α = Lower-Set' , ≃-sym I
 where
  Ω' : 𝓤 ̇
  Ω' = resized (Ω 𝓤) res
  ϕ : Ω' ≃ Ω 𝓤
  ϕ = resizing-condition res
  ψ : (⟨ α ⟩ → Ω') ≃ 𝓟 ⟨ α ⟩
  ψ = →cong fe' fe' (≃-refl ⟨ α ⟩) ϕ

  Lower-Set' : 𝓤 ̇
  Lower-Set' = (Σ S ꞉ (⟨ α ⟩ → Ω') , is-lower-set α (⌜ ψ ⌝ S))

  I = (Σ β ꞉ Ordinal 𝓤 , β ⊴ α) ≃⟨ II ⟩
      Lower-Set α               ≃⟨ III ⟩
      Lower-Set'                ■
   where
    II = simulations-as-lower-sets pt α
    III = ≃-sym (Σ-change-of-variable-≃ (is-lower-set α) ψ)

\end{code}
