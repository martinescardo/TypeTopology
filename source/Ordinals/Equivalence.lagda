Martin Escardo, 29 June 2018, 26th February 2023

Equivalence of ordinals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PreSIP-Examples
open import UF.PreUnivalence
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Univalence
open import UF.Yoneda

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

inverses-of-order-equivs-are-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                                {f : ⟨ α ⟩ → ⟨ β ⟩}
                                              → (i : is-order-equiv α β f)
                                              → is-order-preserving β α
                                                  (inverse f
                                                   (order-equivs-are-equivs α β i))
inverses-of-order-equivs-are-order-preserving α β = pr₂ ∘ pr₂

being-order-equiv-is-prop : Fun-Ext
                          → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                            (f : ⟨ α ⟩ → ⟨ β ⟩)
                          → is-prop (is-order-equiv α β f)
being-order-equiv-is-prop fe α β f = ×-is-prop
                                      (being-order-preserving-is-prop fe α β f)
                                      (Σ-is-prop
                                        (being-equiv-is-prop (λ _ _ → fe) f)
                                        (λ e → being-order-preserving-is-prop fe β α
                                                  (inverse f e)))

\end{code}

Our official definition of ordinal equivalence (see below for
equivalent definitions):

\begin{code}

_≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≃ₒ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-equiv α β f

≃ₒ-refl : (α : Ordinal 𝓤) → α ≃ₒ α
≃ₒ-refl α = id , (λ x y → id) , id-is-equiv ⟨ α ⟩ , (λ x y → id)

idtoeqₒ : (α β : Ordinal 𝓤) → α ＝ β → α ≃ₒ β
idtoeqₒ α α refl = ≃ₒ-refl α

eqtoidₒ : is-univalent 𝓤
        → Fun-Ext
        → (α β : Ordinal 𝓤) → α ≃ₒ β → α ＝ β
eqtoidₒ {𝓤} ua fe α β (f , p , e , q) = γ
 where
  abstract
   A : (Y : 𝓤 ̇ ) → ⟨ α ⟩ ≃ Y → 𝓤 ⁺ ̇
   A Y e = (σ : OrdinalStructure Y)
         → is-order-preserving α (Y , σ) ⌜ e ⌝
         → is-order-preserving (Y , σ) α ⌜ e ⌝⁻¹
         → α ＝ (Y , σ)

   a : A ⟨ α ⟩ (≃-refl ⟨ α ⟩)
   a σ φ ψ = g
    where
     b : (x x' : ⟨ α ⟩) → (x ≺⟨ α ⟩ x') ＝ (x ≺⟨ ⟨ α ⟩ , σ ⟩ x')
     b x x' = univalence-gives-propext ua
               (Prop-valuedness α x x')
               (Prop-valuedness (⟨ α ⟩ , σ) x x')
               (φ x x')
               (ψ x x')

     c : underlying-order α ＝ underlying-order (⟨ α ⟩ , σ)
     c = dfunext fe (λ x → dfunext fe (b x))

     d : structure α ＝ σ
     d = pr₁-lc (λ {_<_} → being-well-order-is-prop _<_ (λ _ _ → fe)) c

     g : α ＝ (⟨ α ⟩ , σ)
     g = to-Σ-＝' d

   γ : α ＝ β
   γ = JEq ua ⟨ α ⟩ A a ⟨ β ⟩ (f , e) (structure β) p q

\end{code}

For historical reasons, the above proof doesn't use the structure
identity principle.

\begin{code}

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

order-equivs-are-simulations : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                               (f : ⟨ α ⟩ → ⟨ β ⟩)
                             → is-order-equiv α β f
                             → is-simulation α β f
order-equivs-are-simulations α β f (p , e , q) = h (equivs-are-qinvs f e) q , p
 where
  h : (d : qinv f)
    → is-order-preserving β α (pr₁ d)
    → is-initial-segment α β f
  h (g , ε , η) q x y l = g y , r , η y
   where
    m : g y ≺⟨ α ⟩ g (f x)
    m = q y (f x) l

    r : g y ≺⟨ α ⟩ x
    r = transport (λ - → g y ≺⟨ α ⟩ -) (ε x) m

≃ₒ-to-fun : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ≃ₒ β → ⟨ α ⟩ → ⟨ β ⟩
≃ₒ-to-fun α β = pr₁

≃ₒ-to-fun-is-order-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (e : α ≃ₒ β)
                         → is-order-equiv α β (≃ₒ-to-fun α β e)
≃ₒ-to-fun-is-order-equiv α β = pr₂

≃ₒ-to-fun-is-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (e : α ≃ₒ β)
                   → is-equiv (≃ₒ-to-fun α β e)
≃ₒ-to-fun-is-equiv α β e = order-equivs-are-equivs α β (≃ₒ-to-fun-is-order-equiv α β e)

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

≃ₒ-gives-≃ : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
           → α ≃ₒ β → ⟨ α ⟩ ≃ ⟨ β ⟩
≃ₒ-gives-≃ α β (f , p , e , q) = (f , e)

≃ₒ-is-prop-valued : Fun-Ext
                  → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                  → is-prop (α ≃ₒ β)
≃ₒ-is-prop-valued fe α β (f , p , e , q) (f' , p' , e' , q')  = γ
  where
   r : f ∼ f'
   r = at-most-one-simulation α β f f'
        (order-equivs-are-simulations α β f  (p  , e ,  q ))
        (order-equivs-are-simulations α β f' (p' , e' , q'))

   γ : (f , p , e , q) ＝ (f' , p' , e' , q')
   γ = to-subtype-＝
        (being-order-equiv-is-prop fe α β)
        (dfunext fe r)

UAₒ : is-univalent 𝓤
    → Fun-Ext
    → (α β : Ordinal 𝓤) → is-equiv (idtoeqₒ α β)
UAₒ {𝓤} ua fe α = nats-with-sections-are-equivs α
                   (idtoeqₒ α)
                   (λ β → (eqtoidₒ ua fe α β , η β))
 where
  η : (β : Ordinal 𝓤) (e : α ≃ₒ β)
    → idtoeqₒ α β (eqtoidₒ ua fe α β e) ＝ e
  η β e = ≃ₒ-is-prop-valued fe α β (idtoeqₒ α β (eqtoidₒ ua fe α β e)) e

idtoeqₒ-eqtoidₒ : (ua : is-univalent 𝓤)
                 → (fe : Fun-Ext)
                 → (α β : Ordinal 𝓤) → (e : α ≃ₒ β)
                 → idtoeqₒ α β (eqtoidₒ ua fe α β e) ＝ e
idtoeqₒ-eqtoidₒ ua fe α β =
 inverses-are-sections (idtoeqₒ α β) (UAₒ ua fe α β)

eqtoidₒ-idtoeqₒ : (ua : is-univalent 𝓤)
                 → (fe : Fun-Ext)
                 → (α β : Ordinal 𝓤) → (p : α ＝ β)
                 → eqtoidₒ ua fe α β (idtoeqₒ α β p) ＝ p
eqtoidₒ-idtoeqₒ ua fe α β =
 inverses-are-retractions (idtoeqₒ α β) (UAₒ ua fe α β)

order-equiv-induction : is-univalent 𝓤
                      → Fun-Ext
                      → (α : Ordinal 𝓤)
                      → (P : (β : Ordinal 𝓤) → (α ≃ₒ β) → 𝓥 ̇ )
                      → P α (≃ₒ-refl α)
                      → (β : Ordinal 𝓤)
                      → (e : α ≃ₒ β)
                      → P β e
order-equiv-induction {𝓤} ua fe α P m β e = III
 where
  I : (β : Ordinal 𝓤) → (e : α ＝ β) → P β (idtoeqₒ α β e)
  I = Jbased α (λ β e → P β (idtoeqₒ α β e)) m

  II : P β (idtoeqₒ α β (eqtoidₒ ua fe α β e))
  II = I β (eqtoidₒ ua fe α β e)

  III : P β e
  III = transport (P β) (idtoeqₒ-eqtoidₒ ua fe α β e) II

the-type-of-ordinals-is-a-set : is-univalent 𝓤
                              → Fun-Ext
                              → is-set (Ordinal 𝓤)
the-type-of-ordinals-is-a-set ua fe {α} {β} = equiv-to-prop
                                               (idtoeqₒ α β , UAₒ ua fe α β)
                                               (≃ₒ-is-prop-valued fe α β)

UAₒ-≃ : is-univalent 𝓤
      → Fun-Ext
      → (α β : Ordinal 𝓤) → (α ＝ β) ≃ (α ≃ₒ β)
UAₒ-≃ ua fe α β = idtoeqₒ α β , UAₒ ua fe α β

the-type-of-ordinals-is-locally-small : is-univalent 𝓤
                                      → Fun-Ext
                                      → is-locally-small (Ordinal 𝓤)
the-type-of-ordinals-is-locally-small ua fe α β =
 (α ≃ₒ β) , ≃-sym (UAₒ-≃ ua fe α β)

\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types that are not sets. Here we have instead used it to
prove that a certain type is a set. But see below for a proof that
uses a weaker assumption.

\begin{code}

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
             × ((x x' : ⟨ α ⟩) → x ≺⟨ α ⟩ x' ↔ f x ≺⟨ β ⟩ f x')

≃ₐ-coincides-with-≃ₒ : FunExt
                     → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                     → (α ≃ₐ β) ≃ (α ≃ₒ β)
≃ₐ-coincides-with-≃ₒ fe α β =
 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , is-equiv f
      × ((x x' : ⟨ α ⟩) → x ≺⟨ α ⟩ x' ↔ f x ≺⟨ β ⟩ f x')) ≃⟨ I ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , is-equiv f
      × (is-order-preserving α β f)
      × (is-order-reflecting α β f))                      ≃⟨ II ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , (Σ e ꞉ is-equiv f
             , (is-order-preserving α β f)
             × (is-order-preserving β α (inv f e))))      ≃⟨ III ⟩

 (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩)
      , (is-order-preserving α β f)
      × (Σ e ꞉ is-equiv f
             , (is-order-preserving β α (inv f e))))      ■
  where
   inv = inverse
   I   = Σ-cong (λ f → ×-cong (≃-refl _) Π×-distr₂)
   II  = Σ-cong (λ f → Σ-cong (λ e → ×-cong (≃-refl _) (b f e)))
    where
     b : (f : ⟨ α ⟩ → ⟨ β ⟩) (e : is-equiv f)
       → is-order-reflecting α β f ≃ is-order-preserving β α (inv f e)
     b f e =
      logically-equivalent-props-are-equivalent
       (being-order-reflecting-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥) α β f)
       (being-order-preserving-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥) β α (inv f e))
       (order-reflecting-gives-inverse-order-preserving α β f e)
       (inverse-order-reflecting-gives-order-preserving α β f e)
   III = Σ-cong (λ f → Σ-flip)

\end{code}

If we only assume preunivalence, meaning that idtoeq is an embedding
(rather than an equivalence), which is implied by each of univalence
and the K axiom, we get that idtoeqₒ is an embedding (rather than an
equivalence). This was suggested to me by Peter Lumsdaine in August
2022.

\begin{code}

idtoeqₒ-embedding : is-preunivalent 𝓤
                  → FunExt
                  → (α β : Ordinal 𝓤)
                  → (α ＝ β) ↪ (α ≃ₒ β)
idtoeqₒ-embedding {𝓤} pua fe α β = II
 where
  open relational-space {𝓤} {𝓤} {𝓤}
        (λ (X : 𝓤 ̇ ) (_<_ : X → X → 𝓤 ̇ ) → is-well-order _<_)
        (λ (X : 𝓤 ̇ ) (_<_ : X → X → 𝓤 ̇ ) → being-well-order-is-prop _<_ fe)
        (λ {X R} w {x} {y} → prop-valuedness R w x y)

  I : (α ＝ β) ↪ (α ≅₂ β)
  I = M-embedding₂-bis pua pua (λ {𝓤} {𝓥} → fe 𝓤 𝓥) α β

  II : (α ＝ β) ↪ (α ≃ₒ β)
  II = ≃-gives-↪ (≃ₐ-coincides-with-≃ₒ fe α β) ∘↪ I

Ordinal-is-set-under-preunivalence : is-preunivalent 𝓤
                                   → FunExt
                                   → is-set (Ordinal 𝓤)
Ordinal-is-set-under-preunivalence {𝓤} pua fe {α} {β} =
 subtypes-of-props-are-props
  ⌊ idtoeqₒ-embedding pua fe α β ⌋
  ⌊ idtoeqₒ-embedding pua fe α β ⌋-is-embedding
  (≃ₒ-is-prop-valued (fe _ _) α β)

\end{code}

NB. The above idtoeqₒ-embedding is constructed by a non-trivial
procedure using preunivalence and function extensionality as
assumptions, and so we may wonder whether it really is idtoeqₒ. It
isn't on the nose, but it is pointwise equal to it on the nose:

\begin{code}

idtoeqₒ-embedding-really-is-idtoeqₒ : (pua : is-preunivalent 𝓤)
                                      (fe : FunExt)
                                      (α β : Ordinal 𝓤)
                                    →  ⌊ idtoeqₒ-embedding pua fe α β ⌋
                                    ∼ idtoeqₒ α β
idtoeqₒ-embedding-really-is-idtoeqₒ pua fe α β refl = refl

\end{code}

And so equal:

\begin{code}

idtoeqₒ-embedding-really-is-idtoeqₒ' : (pua : is-preunivalent 𝓤)
                                       (fe : FunExt)
                                       (α β : Ordinal 𝓤)
                                     →  ⌊ idtoeqₒ-embedding pua fe α β ⌋
                                     ＝ idtoeqₒ α β
idtoeqₒ-embedding-really-is-idtoeqₒ' pua fe α β =
 dfunext (fe _ _) (idtoeqₒ-embedding-really-is-idtoeqₒ pua fe α β)

\end{code}

For convenience, we add the special case of Idtofun for ordinals.

Added 11 December 2024 by Fredrik Nordvall Forsberg and Tom de Jong.

\begin{code}

Idtofunₒ : {α β : Ordinal 𝓤} → α ＝ β → ⟨ α ⟩ → ⟨ β ⟩
Idtofunₒ = transport ⟨_⟩

Idtofunₒ-retraction : {α β : Ordinal 𝓤} (e : α ＝ β)
                    → Idtofunₒ e ∘ Idtofunₒ (e ⁻¹) ∼ id
Idtofunₒ-retraction refl _ = refl

Idtofunₒ-section : {α β : Ordinal 𝓤} (e : α ＝ β)
                 → Idtofunₒ (e ⁻¹) ∘ Idtofunₒ e ∼ id
Idtofunₒ-section refl _ = refl

Idtofunₒ-is-order-equiv : {α β : Ordinal 𝓤} (e : α ＝ β)
                        → is-order-equiv α β (Idtofunₒ e)
Idtofunₒ-is-order-equiv {𝓤} {α} refl =
 id-order-preserving , (id-is-equiv ⟨ α ⟩ , id-order-preserving)
  where
   id-order-preserving : is-order-preserving α α id
   id-order-preserving x y l = l

Idtofunₒ-is-simulation : {α β : Ordinal 𝓤} (e : α ＝ β)
                       → is-simulation α β (Idtofunₒ e)
Idtofunₒ-is-simulation {𝓤} {α} {β} e =
 order-equivs-are-simulations α β (Idtofunₒ e) (Idtofunₒ-is-order-equiv e)

Idtofunₒ-eqtoidₒ : (ua : is-univalent 𝓤) (fe : Fun-Ext)
                   {α β : Ordinal 𝓤} (e : α ≃ₒ β)
                 → Idtofunₒ (eqtoidₒ ua fe α β e) ＝ ≃ₒ-to-fun α β e
Idtofunₒ-eqtoidₒ {𝓤} ua fe {α} {β} e = order-equiv-induction ua fe α P m β e
 where
  P : (β : Ordinal 𝓤) → α ≃ₒ β → 𝓤 ̇
  P β e = Idtofunₒ (eqtoidₒ ua fe α β e) ＝ ≃ₒ-to-fun α β e

  m : P α (≃ₒ-refl α)
  m = Idtofunₒ (eqtoidₒ ua fe α α (≃ₒ-refl α)) ＝⟨ I ⟩
      Idtofunₒ {α = α} refl                    ＝⟨refl⟩
      ≃ₒ-to-fun α α (≃ₒ-refl α)                ∎
   where
    I = ap Idtofunₒ (eqtoidₒ-idtoeqₒ ua fe α α refl)

\end{code}

Originally formalized by Fredrik Nordvall Forsberg. Moved here and refactored
with a shorter proof by Tom de Jong on 18 December 2024.

Surjective simulations are equivalences of ordinals.

\begin{code}

module _
        (pt : propositional-truncations-exist)
       where

 open import UF.ImageAndSurjection pt

 surjective-simulations-are-order-equivs : FunExt
                                         → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                         → (f : ⟨ α ⟩ → ⟨ β ⟩)
                                         → is-simulation α β f
                                         → is-surjection f
                                         → is-order-equiv α β f
 surjective-simulations-are-order-equivs fe α β f f-sim f-surj =
  order-preserving-reflecting-equivs-are-order-equivs α β f
   (surjective-embeddings-are-equivs f
     (simulations-are-embeddings fe α β f f-sim)
     f-surj)
   (simulations-are-order-preserving α β f f-sim)
   (simulations-are-order-reflecting α β f f-sim)

 surjective-simulation-gives-＝ : Fun-Ext
                                → is-univalent 𝓤
                                → (α β : Ordinal 𝓤)
                                → (f : ⟨ α ⟩ → ⟨ β ⟩)
                                → is-simulation α β f
                                → is-surjection f
                                → α ＝ β
 surjective-simulation-gives-＝ fe ua α β f f-sim f-surj =
  eqtoidₒ ua fe α β
   (f ,
    surjective-simulations-are-order-equivs (λ _ _ → fe) α β f f-sim f-surj)

\end{code}

Associativities and precedences.

\begin{code}

infix 0 _≃ₒ_

\end{code}
