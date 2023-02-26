Martin Escardo, 29 June 2018, 26th February 2023

Equivalence of ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PreSIP-Examples
open import UF.PreUnivalence
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

module Ordinals.Equivalence where

\end{code}

Characterization of equality of ordinals using the structure identity
principle:

\begin{code}

Ordinal-＝ : FunExt
          → is-univalent 𝓤
          → (α β : Ordinal 𝓤)
          → (α ＝ β)
          ≃ (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
                 , is-equiv f
                 × ((λ x x' → x ≺⟨ α ⟩ x') ＝ (λ x x' → f x ≺⟨ β ⟩ f x')))
Ordinal-＝ {𝓤} fe = generalized-metric-space.characterization-of-M-＝ (𝓤 ̇ )
                     (λ _ → is-well-order)
                     (λ X _<_ → being-well-order-is-prop _<_ fe)
 where
  open import UF.SIP-Examples

\end{code}

Often it is convenient to work with the following alternative notion _≃ₒ_
of ordinal equivalence, which we take as the official one:

\begin{code}

is-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                    → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
is-order-preserving α β f = (x y : ⟨ α ⟩) → x ≺⟨ α ⟩ y → f x ≺⟨ β ⟩ f y

being-order-preserving-is-prop : Fun-Ext
                               → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                 (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-prop (is-order-preserving α β f)
being-order-preserving-is-prop fe α β f =
 Π₃-is-prop fe (λ x y l → Prop-valuedness β (f x) (f y))

is-order-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
is-order-equiv α β f = is-order-preserving α β f
                     × (Σ e ꞉ is-equiv f , is-order-preserving β α (inverse f e))

order-equivs-are-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                    {f : ⟨ α ⟩ → ⟨ β ⟩}
                                  → is-order-equiv α β f
                                  → is-order-preserving α β f
order-equivs-are-order-preserving α β = pr₁


order-equivs-are-equivs : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                          {f : ⟨ α ⟩ → ⟨ β ⟩}
                        → (i : is-order-equiv α β f)
                        → is-equiv f
order-equivs-are-equivs α β = pr₁ ∘ pr₂

_≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≃ₒ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-equiv α β f

\end{code}

See the module OrdinalOfOrdinals for a proof that α ≃ₒ β is
canonically equivalent to α ＝ β. (For historical reasons, that proof
doesn't use the structure identity principle.)

\begin{code}

≃ₒ-refl : (α : Ordinal 𝓤) → α ≃ₒ α
≃ₒ-refl α = id , (λ x y → id) , id-is-equiv ⟨ α ⟩ , (λ x y → id)

≃ₒ-sym : (α : Ordinal 𝓤) (β : Ordinal 𝓥 )
       → α ≃ₒ β → β ≃ₒ α
≃ₒ-sym α β (f , p , e , q) = inverse f e , q , inverses-are-equivs f e , p

≃ₒ-trans : ∀ {𝓤} {𝓥} {𝓦} (α : Ordinal 𝓤) (β : Ordinal 𝓥 ) (γ : Ordinal 𝓦)
         → α ≃ₒ β → β ≃ₒ γ → α ≃ₒ γ
≃ₒ-trans α β γ (f , p , e , q) (f' , p' , e' , q') =
  f' ∘ f ,
  (λ x y l → p' (f x) (f y) (p x y l)) ,
  ∘-is-equiv e e' ,
  (λ x y l → q (inverse f' e' x) (inverse f' e' y) (q' x y l))

≃ₒ-to-fun : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ≃ₒ β → ⟨ α ⟩ → ⟨ β ⟩
≃ₒ-to-fun α β = pr₁

≃ₒ-to-fun-is-order-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (e : α ≃ₒ β)
                         → is-order-equiv α β (≃ₒ-to-fun α β e)
≃ₒ-to-fun-is-order-equiv α β = pr₂

≃ₒ-to-fun-is-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (e : α ≃ₒ β)
                   → is-equiv (≃ₒ-to-fun α β e)
≃ₒ-to-fun-is-equiv α β e = order-equivs-are-equivs α β (≃ₒ-to-fun-is-order-equiv α β e)

inverses-of-order-equivs-are-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                                {f : ⟨ α ⟩ → ⟨ β ⟩}
                                              → (i : is-order-equiv α β f)
                                              → is-order-preserving β α
                                                  (inverse f (order-equivs-are-equivs α β i))
inverses-of-order-equivs-are-order-preserving α β = pr₂ ∘ pr₂

is-order-reflecting : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                    → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
is-order-reflecting α β f = (x y : ⟨ α ⟩) → f x ≺⟨ β ⟩ f y → x ≺⟨ α ⟩ y

being-order-reflecting-is-prop : Fun-Ext
                               → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                 (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-prop (is-order-reflecting α β f)
being-order-reflecting-is-prop fe α β f =
 Π₃-is-prop fe (λ x y l → Prop-valuedness α x y)

order-reflecting-gives-inverse-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                                  (f : ⟨ α ⟩ → ⟨ β ⟩)
                                                → (e : is-equiv f)
                                                → is-order-reflecting α β f
                                                → is-order-preserving β α (inverse f e)
order-reflecting-gives-inverse-order-preserving α β f e r x y l = m
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = inverse f e

  l' : f (g x) ≺⟨ β ⟩ f (g y)
  l' = transport₂ (λ x y → x ≺⟨ β ⟩ y)
        ((inverses-are-sections f e x)⁻¹)
        ((inverses-are-sections f e y)⁻¹) l

  s : f (g x) ≺⟨ β ⟩ f (g y) → g x ≺⟨ α ⟩ g y
  s = r (g x) (g y)

  m : g x ≺⟨ α ⟩ g y
  m = s l'

inverse-order-reflecting-gives-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                                  (f : ⟨ α ⟩ → ⟨ β ⟩)
                                                  (e : is-equiv f)
                                                → is-order-preserving β α (inverse f e)
                                                → is-order-reflecting α β f
inverse-order-reflecting-gives-order-preserving α β f e q x y l = r
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = inverse f e

  s : g (f x) ≺⟨ α ⟩ g (f y)
  s = q (f x) (f y) l

  r : x ≺⟨ α ⟩ y
  r = transport₂ (λ x y → x ≺⟨ α ⟩ y)
       (inverses-are-retractions f e x)
       (inverses-are-retractions f e y) s

order-preserving-reflecting-equivs-are-order-equivs : (α : Ordinal 𝓤)
                                                      (β : Ordinal 𝓥)
                                                      (f : ⟨ α ⟩ → ⟨ β ⟩)
                                                    → is-equiv f
                                                    → is-order-preserving α β f
                                                    → is-order-reflecting α β f
                                                    → is-order-equiv α β f
order-preserving-reflecting-equivs-are-order-equivs α β f e p r =
 p , e , order-reflecting-gives-inverse-order-preserving α β f e r


order-equivs-are-order-reflecting : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                    (f : ⟨ α ⟩ → ⟨ β ⟩)
                                  → is-order-equiv α β f
                                  → is-order-reflecting α β f
order-equivs-are-order-reflecting α β f (_ , e , q) =
 inverse-order-reflecting-gives-order-preserving α β f e q

inverses-of-order-equivs-are-order-reflecting : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                                {f : ⟨ α ⟩ → ⟨ β ⟩}
                                              → (i : is-order-equiv α β f)
                                              → is-order-reflecting β α
                                                  (inverse f (order-equivs-are-equivs α β i))
inverses-of-order-equivs-are-order-reflecting α β {f} (p , e , q) =
 order-equivs-are-order-reflecting β α
  (inverse f e)
  (q , inverses-are-equivs f e , p)

inverses-of-order-equivs-are-order-equivs : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                            {f : ⟨ α ⟩ → ⟨ β ⟩}
                                          → (i : is-order-equiv α β f)
                                          → is-order-equiv β α
                                              (inverse f (order-equivs-are-equivs α β i))
inverses-of-order-equivs-are-order-equivs α β {f} (p , e , q) =
 (q , inverses-are-equivs f e , p)

≃ₒ-to-fun⁻¹ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ≃ₒ β → ⟨ β ⟩ → ⟨ α ⟩
≃ₒ-to-fun⁻¹ α β e = inverse (≃ₒ-to-fun α β e)
                      (order-equivs-are-equivs α β
                        (≃ₒ-to-fun-is-order-equiv α β e))

≃ₒ-to-fun⁻¹-is-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (e : α ≃ₒ β)
                     → is-equiv (≃ₒ-to-fun⁻¹ α β e)
≃ₒ-to-fun⁻¹-is-equiv α β e = inverses-are-equivs (≃ₒ-to-fun α β e)
                                (≃ₒ-to-fun-is-equiv α β e)

order-equivs-preserve-largest : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                              → (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-order-equiv α β f
                              → (x : ⟨ α ⟩)
                              → is-largest α x
                              → is-largest β (f x)
order-equivs-preserve-largest α β f (o , e , p) x ℓ = δ
 where
  f⁻¹ : ⟨ β ⟩ → ⟨ α ⟩
  f⁻¹ = inverse f e

  δ : (y : ⟨ β ⟩) → y ≼⟨ β ⟩ f x
  δ y t l = IV
   where
    I : f⁻¹ t ≺⟨ α ⟩ f⁻¹ y
    I = p t y l

    II : f⁻¹ t ≺⟨ α ⟩ x
    II = ℓ (f⁻¹ y) (f⁻¹ t) I

    III : f (f⁻¹ t) ≺⟨ β ⟩ f x
    III = o (f⁻¹ t) x II

    IV : t ≺⟨ β ⟩ f x
    IV = transport (λ - → - ≺⟨ β ⟩ f x) (inverses-are-sections f e t) III

\end{code}

Added 25th Feb 2023. Alternative definition of ordinal equivalence

\begin{code}

_≃ₐ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≃ₐ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
             , is-equiv f
             × ((x x' : ⟨ α ⟩) → x ≺⟨ α ⟩ x' ⇔ f x ≺⟨ β ⟩ f x')

≃ₐ-coincides-with-≃ₒ : FunExt
                     → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                     → (α ≃ₐ β) ≃ (α ≃ₒ β)
≃ₐ-coincides-with-≃ₒ fe α β =
 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , is-equiv f
      × ((x x' : ⟨ α ⟩) → x ≺⟨ α ⟩ x' ⇔ f x ≺⟨ β ⟩ f x'))     ≃⟨ I ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , is-equiv f
      × (is-order-preserving α β f)
      × (is-order-reflecting α β f))                          ≃⟨ II ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , (Σ e ꞉ is-equiv f
             , (is-order-preserving α β f)
             × (is-order-preserving β α (inverse f e))))      ≃⟨ III ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , (is-order-preserving α β f)
      × (Σ e ꞉ is-equiv f
             , (is-order-preserving β α (inverse f e))))      ■
  where
   I  = Σ-cong (λ f → ×-cong (≃-refl _) Π×-distr₂)
   II = Σ-cong (λ f → Σ-cong (λ e → ×-cong (≃-refl _) (b f e)))
    where
     fe' = FunExt-to-Fun-Ext fe
     b = λ f e → logically-equivalent-props-are-equivalent
                  (being-order-reflecting-is-prop fe' α β f)
                  (being-order-preserving-is-prop fe' β α (inverse f e))
                  (order-reflecting-gives-inverse-order-preserving α β f e)
                  (inverse-order-reflecting-gives-order-preserving α β f e)
   III = Σ-cong (λ f → Σ-flip)

\end{code}

If we only assume preunivalence, meaning that idtoeq is an embedding
(rather than an equivalence), which is implied by each of univalence
and the K axiom, we get that idtoeqₒ is an embedding (rather than an
equivalence). This was suggested to me by Peter Lumbsdaine in August
2022.

\begin{code}

idtoeqₒ-is-embedding : is-preunivalent 𝓤
                     → FunExt
                     → PropExt
                     → (α β : Ordinal 𝓤)
                     → (α ＝ β) ↪ (α ≃ₒ β)
idtoeqₒ-is-embedding {𝓤} pua fe pe α β = II
 where
  open relational-space
        (λ (X : 𝓤 ̇ ) (_<_ : X → X → 𝓤 ̇) → is-well-order _<_)
        (λ (X : 𝓤 ̇ ) (_<_ : X → X → 𝓤 ̇) → being-well-order-is-prop _<_ fe)
        (λ {X R} w {x} {y} → prop-valuedness R w x y)

  I : (α ＝ β) ↪ (α ≅₂ β)
  I = M-embedding₂ pua (fe _ _) (pe _) α β

  II : (α ＝ β) ↪ (α ≃ₒ β)
  II = ≃-gives-↪ (≃ₐ-coincides-with-≃ₒ fe α β)
     ∘↪ I

\end{code}
