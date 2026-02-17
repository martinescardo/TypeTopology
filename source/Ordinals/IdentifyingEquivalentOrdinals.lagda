Written 26 March 2023 by Tom de Jong, following a discussion with Nicolai Kraus
on 24 March  2023.
Revisited and merged into TypeTopology in February 2026.

We show that having an identification of the ordinals (𝟚 , ₀ ≺ ₁) and
(𝟚 , ₁ ≺ ₀) contradicts the K-axiom.

It follows that preunivalence TODO: REF cannot be sufficient to show that the simulation
ordering on the type of ordinals is antisymmetric: The ordinals (𝟚 , ₀ ≺ ₁) and
(𝟚 , ₁ ≺ ₀) are equivalent, while preunivalence is derivable from the K-axiom.

TODO: Make link to Ordinal-is-set-under-preunivalence from Ordinals.Equivalence.

  α ＝ β ----> ⟨ α ⟩ ＝ ⟨ β ⟩
    |                |
    |                |
    v                v
  α ≃ₒ β ----> ⟨ α ⟩ ≃ ⟨ β ⟩

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.IdentifyingEquivalentOrdinals where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Equiv
open import UF.PreUnivalence
open import UF.Sets
open import UF.Subsingletons

open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying

private

-- TODO. Explain why we don't use transport-ordinal-structure or even tansport-well-order from Ordinals.WellOrderTransport.

 idtoeqₒ-naturality : (α β : Ordinal 𝓤) → (p : α ＝ β)
                    → idtoeq ⟨ α ⟩ ⟨ β ⟩ (ap ⟨_⟩ p)
                    ＝ ≃ₒ-gives-≃ α β (idtoeqₒ α β p)
 idtoeqₒ-naturality α β refl = refl

 𝟚ₒ : Ordinal 𝓤₀
 𝟚ₒ = 𝟚 , (_≺_ , p , w , e , t)
  where
   _≺_ : 𝟚 → 𝟚 → 𝓤₀ ̇
   ₀ ≺ ₀ = 𝟘
   ₀ ≺ ₁ = 𝟙
   ₁ ≺ ₀ = 𝟘
   ₁ ≺ ₁ = 𝟘
   p : is-prop-valued _≺_
   p ₀ ₀ = 𝟘-is-prop
   p ₀ ₁ = 𝟙-is-prop
   p ₁ ₀ = 𝟘-is-prop
   p ₁ ₁ = 𝟘-is-prop
   w : is-well-founded _≺_
   w ₀ = acc a
    where
     a : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = 𝟘-elim l
   w ₁ = acc a
    where
     a : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
     a ₀ l = w ₀
     a ₁ l = 𝟘-elim l
   e : is-extensional _≺_
   e ₀ ₀ u v = refl
   e ₀ ₁ u v = 𝟘-elim (v ₀ ⋆)
   e ₁ ₀ u v = 𝟘-elim (u ₀ ⋆)
   e ₁ ₁ u v = refl
   t : is-transitive _≺_
   t ₀ ₀ ₀ k l = l
   t ₀ ₁ ₀ k l = l
   t ₁ ₀ ₀ k l = l
   t ₁ ₁ ₀ k l = l
   t ₀ ₀ ₁ k l = l
   t ₀ ₁ ₁ k l = k
   t ₁ ₀ ₁ k l = k
   t ₁ ₁ ₁ k l = l

 𝟚ₒ' : Ordinal 𝓤₀
 𝟚ₒ' = 𝟚 , (_≺_ , p , w , e , t)
  where
   _≺_ : 𝟚 → 𝟚 → 𝓤₀ ̇
   ₀ ≺ ₀ = 𝟘
   ₀ ≺ ₁ = 𝟘
   ₁ ≺ ₀ = 𝟙
   ₁ ≺ ₁ = 𝟘
   p : is-prop-valued _≺_
   p ₀ ₀ = 𝟘-is-prop
   p ₀ ₁ = 𝟘-is-prop
   p ₁ ₀ = 𝟙-is-prop
   p ₁ ₁ = 𝟘-is-prop
   w : is-well-founded _≺_
   w ₀ = acc a
    where
     a : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = w ₁
   w ₁ = acc a
    where
     a : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = 𝟘-elim l
   e : is-extensional _≺_
   e ₀ ₀ u v = refl
   e ₀ ₁ u v = 𝟘-elim (u ₁ ⋆)
   e ₁ ₀ u v = 𝟘-elim (v ₁ ⋆)
   e ₁ ₁ u v = refl
   t : is-transitive _≺_
   t ₀ ₀ ₀ k l = l
   t ₀ ₁ ₀ k l = k
   t ₁ ₀ ₀ k l = ⋆
   t ₁ ₁ ₀ k l = l
   t ₀ ₀ ₁ k l = l
   t ₀ ₁ ₁ k l = l
   t ₁ ₀ ₁ k l = l
   t ₁ ₁ ₁ k l = l

 𝟚ₒ-≃ₒ-𝟚ₒ' : 𝟚ₒ ≃ₒ 𝟚ₒ'
 𝟚ₒ-≃ₒ-𝟚ₒ' = f , f-preserves-order , f-is-equiv , f-preserves-order'
  where
   f : 𝟚 → 𝟚
   f = complement
   f-preserves-order : is-order-preserving 𝟚ₒ 𝟚ₒ' f
   f-preserves-order ₀ ₁ l = l
   f-preserves-order ₀ ₀ l = 𝟘-elim l
   f-preserves-order ₁ ₀ l = 𝟘-elim l
   f-preserves-order ₁ ₁ l = 𝟘-elim l
   f-is-equiv : is-equiv f
   f-is-equiv = qinvs-are-equivs f (f , complement-involutive , complement-involutive)
   f-preserves-order' : is-order-preserving 𝟚ₒ' 𝟚ₒ f
   f-preserves-order' ₀ ₀ l = 𝟘-elim l
   f-preserves-order' ₀ ₁ l = 𝟘-elim l
   f-preserves-order' ₁ ₀ l = l
   f-preserves-order' ₁ ₁ l = 𝟘-elim l

 complement-is-the-only-ordinal-equivalence-of-𝟚 : (e : 𝟚ₒ ≃ₒ 𝟚ₒ')
                                                 → ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ∼ complement
 complement-is-the-only-ordinal-equivalence-of-𝟚 e ₀ = different-from-₀-equal-₁ h
  where
   f : 𝟚 → 𝟚
   f = ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e
   h : ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ₀ ≠ ₀
   h p = l' (f ₁) (order-equivs-are-order-preserving 𝟚ₒ 𝟚ₒ' (≃ₒ-to-fun-is-order-equiv 𝟚ₒ 𝟚ₒ' e) ₀ ₁ ⋆)
    where
     l : (b : 𝟚) → ¬ (₀ ≺⟨ 𝟚ₒ' ⟩ b)
     l ₀ l = 𝟘-elim l
     l ₁ l = 𝟘-elim l
     l' : (b : 𝟚) → ¬ (f ₀ ≺⟨ 𝟚ₒ' ⟩ b)
     l' b = idtofun _ _ (ap (λ - → ¬ (- ≺⟨ 𝟚ₒ' ⟩ b)) (p ⁻¹)) (l b)
 complement-is-the-only-ordinal-equivalence-of-𝟚 e ₁ = different-from-₁-equal-₀ h
  where
   f : 𝟚 → 𝟚
   f = ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e
   h : ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ₁ ≠ ₁
   h p = l' (f ₀) (order-equivs-are-order-preserving 𝟚ₒ 𝟚ₒ' (≃ₒ-to-fun-is-order-equiv 𝟚ₒ 𝟚ₒ' e) ₀ ₁ ⋆)
    where
     l : (b : 𝟚) → ¬ (b ≺⟨ 𝟚ₒ' ⟩ ₁)
     l ₀ l = 𝟘-elim l
     l ₁ l = 𝟘-elim l
     l' : (b : 𝟚) → ¬ (b ≺⟨ 𝟚ₒ' ⟩ f ₁)
     l' b = idtofun _ _ (ap (λ - → ¬ (b ≺⟨ 𝟚ₒ' ⟩ -)) (p ⁻¹)) (l b)

 identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K : 𝟚ₒ ＝ 𝟚ₒ' → ¬ K-axiom 𝓤₁
 identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K pₒ K = p-is-not-refl (K (𝓤₀ ̇  ) p refl)
  where
   p : 𝟚 ＝ 𝟚
   p = ap ⟨_⟩ pₒ
   f : 𝟚 ≃ 𝟚
   f = idtoeq 𝟚 𝟚 p
   p-is-not-refl : ¬ (p ＝ refl)
   p-is-not-refl e = zero-is-not-one (₀                     ＝⟨ refl ⟩
                                      ⌜ idtoeq 𝟚 𝟚 refl ⌝ ₀ ＝⟨ ap (λ - → ⌜ idtoeq 𝟚 𝟚 - ⌝ ₀) (e ⁻¹) ⟩
                                      ⌜ f ⌝ ₀               ＝⟨ ap (λ - → ⌜ - ⌝ ₀) (idtoeqₒ-naturality 𝟚ₒ 𝟚ₒ' pₒ) ⟩
                                      ⌜ ≃ₒ-gives-≃ 𝟚ₒ 𝟚ₒ' (idtoeqₒ 𝟚ₒ 𝟚ₒ' pₒ) ⌝ ₀ ＝⟨ refl ⟩
                                      ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' (idtoeqₒ 𝟚ₒ 𝟚ₒ' pₒ) ₀ ＝⟨ complement-is-the-only-ordinal-equivalence-of-𝟚 (idtoeqₒ 𝟚ₒ 𝟚ₒ' pₒ) ₀ ⟩
                                      ₁                     ∎)

-- TODO: Explain why we copy this

 private
  _⊴_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
  α ⊴ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-simulation α β f

 antisymmetry-of-⊴ : (𝓤 : Universe) → 𝓤 ⁺ ̇
 antisymmetry-of-⊴ 𝓤 = (α β : Ordinal 𝓤) → α ⊴ β → β ⊴ α → α ＝ β

 -- Perhaps this ought to go into UF.Sets-Properties, but it can't right now
 -- because of cyclic module dependencies (which we could avoid by replacing
 -- ≃-Lift with an inline construction).
 K-axiom-lower : K-axiom (𝓤 ⁺) → K-axiom 𝓤
 K-axiom-lower {𝓤} κ X = I
  where
   open import UF.Sets-Properties
   open import UF.UniverseEmbedding
   I : is-set X
   I = equiv-to-set (≃-Lift (𝓤 ⁺) X) (κ (Lift (𝓤 ⁺) X))

 fact : ¬ (K-axiom 𝓤₁ → 𝟘 {𝓤₀})
      → ¬ (is-preunivalent 𝓤₀ → antisymmetry-of-⊴ 𝓤₀)
 fact K-consistent hyp = K-consistent I
  where
   I : K-axiom 𝓤₁ → 𝟘
   I κ = identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K II κ
    where
     II : 𝟚ₒ ＝ 𝟚ₒ'
     II = hyp (K-gives-preunivalence (K-axiom-lower κ) κ) 𝟚ₒ 𝟚ₒ' II₁ II₂
      where
       II₁ : 𝟚ₒ ⊴ 𝟚ₒ'
       II₁ = (complement ,
              order-equivs-are-simulations 𝟚ₒ 𝟚ₒ' complement (pr₂ 𝟚ₒ-≃ₒ-𝟚ₒ'))
       II₂ : 𝟚ₒ' ⊴ 𝟚ₒ
       II₂ = (complement , order-equivs-are-simulations 𝟚ₒ' 𝟚ₒ complement
                            (pr₂ (≃ₒ-sym 𝟚ₒ 𝟚ₒ' (𝟚ₒ-≃ₒ-𝟚ₒ'))))