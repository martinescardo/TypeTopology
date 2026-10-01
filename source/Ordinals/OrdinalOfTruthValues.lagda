Martin Escardo, 4th October 2018

The ordinal of truth values in a universe 𝓤.
\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module Ordinals.OrdinalOfTruthValues
       (fe : FunExt)
       (𝓤  : Universe)
       (pe : propext 𝓤)
       where


open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Equiv
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

Ωₒ : Ordinal (𝓤 ⁺)
Ωₒ = Ω 𝓤 , _≺_ , pv , w , e , t
 where
  _≺_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ⁺ ̇
  p ≺ q = (p ＝ ⊥) × (q ＝ ⊤)

  pv : is-prop-valued _≺_
  pv p q = ×-is-prop (Ω-is-set (fe 𝓤 𝓤) pe) (Ω-is-set (fe 𝓤 𝓤) pe)

  w : is-well-founded _≺_
  w p = acc s
   where
    t : (q : Ω 𝓤) →  q ≺ ⊥ → is-accessible _≺_ q
    t ⊥ (refl , b) = 𝟘-elim (⊥-is-not-⊤ b)

    ⊥-accessible : is-accessible _≺_ ⊥
    ⊥-accessible = acc t

    s : (q : Ω 𝓤) → q ≺ p → is-accessible _≺_ q
    s ⊥ (refl , b) = ⊥-accessible

  e : is-extensional _≺_
  e p q f g = Ω-ext pe (fe 𝓤 𝓤) φ ψ
   where
    φ : p ＝ ⊤ → q ＝ ⊤
    φ a = pr₂ (f ⊥ (refl , a))

    ψ : q ＝ ⊤ → p ＝ ⊤
    ψ b = pr₂ (g ⊥ (refl , b))

  t : is-transitive _≺_
  t p q r (a , _) (_ , b) = a , b

⊥-is-least : is-least Ωₒ ⊥
⊥-is-least (P , i) (𝟘 , 𝟘-is-prop) (refl , q) = 𝟘-elim (equal-⊤-gives-true 𝟘 𝟘-is-prop q)

⊤-is-largest : is-largest Ωₒ ⊤
⊤-is-largest (.𝟙 , .𝟙-is-prop) (.𝟘 , .𝟘-is-prop) (refl , refl) = refl , refl

¬¬-dense-is-largest' : (p q : Ω 𝓤)
                     → ¬¬ (p holds)
                     → (q ≾⟨ Ωₒ ⟩ p)
¬¬-dense-is-largest' .⊥ .⊤ f (refl , refl) = f 𝟘-elim

open import UF.Univalence

module _ (ua : Univalence) where

 open import Ordinals.OrdinalOfOrdinals ua

 𝟚ₒ-leq-Ωₒ : 𝟚ₒ {𝓥} ⊴ Ωₒ
 𝟚ₒ-leq-Ωₒ = f , i , p
  where
   f : 𝟙 + 𝟙 → Ω 𝓤
   f (inl ⋆) = ⊥
   f (inr ⋆) = ⊤

   i : is-initial-segment 𝟚ₒ Ωₒ f
   i (inl ⋆) q (refl , e) = 𝟘-elim (⊥-is-not-⊤ e)
   i (inr ⋆) q (refl , _) = inl ⋆ , ⋆ , refl

   p : is-order-preserving 𝟚ₒ Ωₒ f
   p (inl ⋆) (inl x) l = 𝟘-elim l
   p (inl ⋆) (inr x) ⋆ = refl , refl
   p (inr ⋆) (inl x) l = 𝟘-elim l
   p (inr ⋆) (inr x) l = 𝟘-elim l

\end{code}

Notice also that being a least element is not in general decidable
because in this example being a least element amounts to being false,
and deciding falsity is equivalent to weak excluded middle.

Added 12 December 2024 by Fredrik Nordvall Forsberg.

We characterise the initial segments of Ωₒ.

\begin{code}

 Ωₒ↓-is-id : (P : Ω 𝓤) → Ωₒ ↓ P ≃ₒ prop-ordinal (P holds) (holds-is-prop P)
 Ωₒ↓-is-id P = e ,
               e-order-preserving ,
               (qinvs-are-equivs e (e⁻¹ , η , ϵ)) ,
               e⁻¹-order-preserving
  where
   Pₒ = prop-ordinal (P holds) (holds-is-prop P)

   e : ⟨ Ωₒ ↓ P ⟩ → P holds
   e (_ , _ , ψ) = equal-⊤-gives-holds P ψ

   e-order-preserving : is-order-preserving (Ωₒ ↓ P) Pₒ e
   e-order-preserving _ (_ , ψ , _) (_ , l) = 𝟘-elim (⊥-is-not-⊤ (ψ ⁻¹ ∙ l))

   e⁻¹ : P holds → ⟨ Ωₒ ↓ P ⟩
   e⁻¹ p = ⊥ , refl , (holds-gives-equal-⊤ pe (fe 𝓤 𝓤) P p)

   e⁻¹-order-preserving : is-order-preserving Pₒ (Ωₒ ↓ P) e⁻¹
   e⁻¹-order-preserving p p' = 𝟘-elim

   η : (e⁻¹ ∘ e) ∼ id
   η (Q , r , _) = to-subtype-＝
                    (λ R → ×-is-prop (Ω-is-set (fe 𝓤 𝓤) pe)
                                     (Ω-is-set (fe 𝓤 𝓤) pe))
                    (r ⁻¹)

   ϵ : (e ∘ e⁻¹) ∼ id
   ϵ p = holds-is-prop P (e (e⁻¹ p)) p

\end{code}
