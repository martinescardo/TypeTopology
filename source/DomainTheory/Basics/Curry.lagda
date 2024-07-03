Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.Curry
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Exponential pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥
open import DomainTheory.Basics.FunctionComposition pt fe 𝓥
open import DomainTheory.Basics.Products pt fe
open import DomainTheory.Basics.ProductsContinuity pt fe 𝓥
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open DcpoProductsGeneral 𝓥

module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
         (𝓕 : DCPO {𝓦} {𝓦'})
       where

 curryᵈᶜᵖᵒ : DCPO[ (𝓓 ×ᵈᶜᵖᵒ 𝓔) , 𝓕 ] → DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]
 curryᵈᶜᵖᵒ (a , a-is-continuous) = f , f-is-continuous
  where
   f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩
   f = continuous→continuous-in-pr₂ 𝓓 𝓔 𝓕 (a , a-is-continuous)

   f-is-continuous : (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                   → is-sup
                      (underlying-order (𝓔 ⟹ᵈᶜᵖᵒ 𝓕))
                      (f (∐ 𝓓 δ))
                      (f ∘ α)
   f-is-continuous I α δ = u , v
    where
     u : (i : I) → ((f ∘ α) i) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ (f (∐ 𝓓 δ))
     u i e = sup-is-upperbound
              (underlying-order 𝓕)
              (continuity-of-function 𝓓 𝓕 a-fixed-e I α δ)
              i
       where
         a-fixed-e : DCPO[ 𝓓 , 𝓕 ]
         a-fixed-e = continuous→continuous-in-pr₁ 𝓓 𝓔 𝓕
                      (a , a-is-continuous)
                      e

     v : (u₁ : ⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩)
       → ((i : I) → f (α i) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ u₁)
       → f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ u₁
     v u₁ p e = e₃ (underlying-function 𝓔 𝓕 u₁ e) (λ i → p i e)
       where
         a-fixed-e : DCPO[ 𝓓 , 𝓕 ]
         a-fixed-e = continuous→continuous-in-pr₁ 𝓓 𝓔 𝓕
                      (a , a-is-continuous)
                      e

         e₃ : (u₂ : ⟨ 𝓕 ⟩)
            → ((i : I) → (underlying-function 𝓓 𝓕 a-fixed-e) (α i) ⊑⟨ 𝓕 ⟩ u₂)
            → (underlying-function 𝓓 𝓕 a-fixed-e) (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ u₂
         e₃ =  sup-is-lowerbound-of-upperbounds
                (underlying-order 𝓕)
                (continuity-of-function 𝓓 𝓕 a-fixed-e I α δ)

 uncurryᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ] → DCPO[ (𝓓 ×ᵈᶜᵖᵒ 𝓔) , 𝓕 ]
 uncurryᵈᶜᵖᵒ 𝕗@(f , f-is-continuous) =
  g ,
  continuous-in-arguments→continuous 𝓓 𝓔 𝓕
   g
   𝓓→𝓕-is-continuous
   𝓔→𝓕-is-continuous
  where
   f-is-monotone : is-monotone 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) f
   f-is-monotone = monotone-if-continuous 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) 𝕗

   𝓓→𝓕-is-continuous : (e : ⟨ 𝓔 ⟩)
                      → is-continuous 𝓓 𝓕 (λ d → underlying-function 𝓔 𝓕 (f d) e)
   𝓓→𝓕-is-continuous e I α δ = u , v
    where
     u : is-upperbound
          (underlying-order 𝓕)
          (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) e)
          (pointwise-family 𝓔 𝓕 (f ∘ α) e)
     u i = f-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i) e
     v : (z : ⟨ 𝓕 ⟩)
       → ((i : I) → (underlying-function 𝓔 𝓕 ((f ∘ α) i) e) ⊑⟨ 𝓕 ⟩ z)
       → (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) e) ⊑⟨ 𝓕 ⟩ z
     v z p = transport (λ - → - ⊑⟨ 𝓕 ⟩ z) (ii ⁻¹) ∐-is-lowerbound
       where
         ⟨f∘α⟩i-is-directed : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f ∘ α)
         ⟨f∘α⟩i-is-directed = image-is-directed 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) {f}
                               f-is-monotone
                               {I}
                               {α}
                               δ

         ⟨f∘α⟩ie-is-directed : is-Directed 𝓕 (pointwise-family 𝓔 𝓕 (f ∘ α) e)
         ⟨f∘α⟩ie-is-directed = pointwise-family-is-directed 𝓔 𝓕
                                (f ∘ α)
                                ⟨f∘α⟩i-is-directed e

         ∐-is-lowerbound : (∐ 𝓕 ⟨f∘α⟩ie-is-directed) ⊑⟨ 𝓕 ⟩ z
         ∐-is-lowerbound = ∐-is-lowerbound-of-upperbounds 𝓕
                            ⟨f∘α⟩ie-is-directed
                            z
                            p

         i : f (∐ 𝓓 δ) ＝ ∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) ⟨f∘α⟩i-is-directed
         i = continuous-∐-＝ 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , f-is-continuous) δ

         ii : underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) e ＝ ∐ 𝓕 ⟨f∘α⟩ie-is-directed
         ii = ap (λ - → underlying-function 𝓔 𝓕 - e) i

   𝓔→𝓕-is-continuous : (d : ⟨ 𝓓 ⟩)
                     → is-continuous 𝓔 𝓕 (λ e → underlying-function 𝓔 𝓕 (f d) e)
   𝓔→𝓕-is-continuous d = continuity-of-function 𝓔 𝓕 (f d)

   g : ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ → ⟨ 𝓕 ⟩
   g p = underlying-function 𝓔 𝓕 (f (pr₁ p)) (pr₂ p)

module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
         (𝓔 : DCPO⊥ {𝓣} {𝓣'})
         (𝓕 : DCPO⊥ {𝓦} {𝓦'})
       where

 curryᵈᶜᵖᵒ⊥ : DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 , 𝓕 ] → DCPO⊥[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓕 ]
 curryᵈᶜᵖᵒ⊥ f = curryᵈᶜᵖᵒ (𝓓 ⁻) (𝓔 ⁻) ( 𝓕 ⁻) f

 uncurryᵈᶜᵖᵒ⊥ : DCPO⊥[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓕 ] → DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 , 𝓕 ]
 uncurryᵈᶜᵖᵒ⊥ f = uncurryᵈᶜᵖᵒ (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻) f

module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
       where

 eval : DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 , 𝓔 ]
 eval = f , c
  where
   f : ⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   f (g , d) = underlying-function 𝓓 𝓔 g d

   f-is-monotone : is-monotone ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
   f-is-monotone (g₁ , d₁) (g₂ , d₂) (g-⊑ , d-⊑) =
    f (g₁ , d₁) ⊑⟨ 𝓔 ⟩[ monotone-if-continuous 𝓓 𝓔 g₁ d₁ d₂ d-⊑ ]
    f (g₁ , d₂) ⊑⟨ 𝓔 ⟩[ g-⊑ d₂ ]
    f (g₂ , d₂) ∎⟨ 𝓔 ⟩

   c : is-continuous ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
   c = continuous-in-arguments→continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓓 𝓔 f
        continuous₁
        continuous₂
    where
     continuous₁ : (e : ⟨ 𝓓 ⟩)
                 → is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓔 (λ d → f (d , e))
     continuous₁ d I α δ = u , v
      where
       u : is-upperbound
            (underlying-order 𝓔)
            (f (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d))
            (λ z → f (α z , d))
       u i = f-is-monotone
              (α i , d)
              (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d)
              (∐-is-upperbound (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ i , reflexivity 𝓓 d)

       v : (y : ⟨ 𝓔 ⟩)
         → ((i : I) → f (α i , d) ⊑⟨ 𝓔 ⟩ y)
         → f (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d) ⊑⟨ 𝓔 ⟩ y
       v y p = ∐-is-lowerbound-of-upperbounds 𝓔 isdir₁ y p
         where
          isdir₁ : is-Directed 𝓔 (pointwise-family 𝓓 𝓔 α d)
          isdir₁ = pointwise-family-is-directed 𝓓 𝓔 α δ d

     continuous₂ : (d : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ e → f (d , e))
     continuous₂ g I α δ = u , v
      where
       u : is-upperbound
            (underlying-order 𝓔)
            (f (g , ∐ 𝓓 δ))
            (λ z → f (g , α z))
       u i = f-is-monotone
              (g , α i)
              (g , ∐ 𝓓 δ)
              ((reflexivity (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) g) , (∐-is-upperbound 𝓓 δ i))

       v : (y : ⟨ 𝓔 ⟩)
         → ((i : I) → f (g , α i) ⊑⟨ 𝓔 ⟩ y)
         → f (g , ∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ y
       v y p = transport (λ - → - ⊑⟨ 𝓔 ⟩ y) (e ⁻¹) q
        where
         e : f (g , ∐ 𝓓 δ)
           ＝  ∐ 𝓔 (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 g) δ)
         e = continuous-∐-＝ 𝓓 𝓔 g δ

         q : (∐ 𝓔 (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 g) δ))
           ⊑⟨ 𝓔 ⟩ y
         q = ∐-is-lowerbound-of-upperbounds 𝓔
               (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 g) δ)
               y
               p

module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
         (𝓔 : DCPO⊥ {𝓣} {𝓣'})
       where

 eval⊥ : DCPO⊥[ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓔) ×ᵈᶜᵖᵒ⊥ 𝓓 , 𝓔 ]
 eval⊥ = eval (𝓓 ⁻) (𝓔 ⁻)

\end{code}
