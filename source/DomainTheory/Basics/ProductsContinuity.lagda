Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.ProductsContinuity
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Products pt fe
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open DcpoProductsGeneral 𝓥

module _  (𝓓 : DCPO {𝓤} {𝓤'})
          (𝓔 : DCPO {𝓣} {𝓣'})
          (𝓕 : DCPO {𝓦} {𝓦'})
        where

 continuous→continuous-in-pr₁ : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓕 ] → ⟨ 𝓔 ⟩ → DCPO[ 𝓓 , 𝓕 ]
 continuous→continuous-in-pr₁ (f , f-is-continuous) e =
  (λ d → f (d , e)) , continuous
   where
    continuous : is-continuous 𝓓 𝓕 (λ d → f (d , e))
    continuous I α δ = u , v
     where
      u : is-upperbound (underlying-order 𝓕) (f (∐ 𝓓 δ , e)) (λ i → f (α i , e))
      u i = monotone-if-continuous
             (𝓓 ×ᵈᶜᵖᵒ 𝓔)
             𝓕
             (f , f-is-continuous)
             (α i , e)
             (∐ 𝓓 δ , e)
             (∐-is-upperbound 𝓓 δ i , reflexivity 𝓔 e)
      v : (z : ⟨ 𝓕 ⟩)
        → ((i : I) → (f (α i , e)) ⊑⟨ 𝓕 ⟩ z)
        → (f (∐ 𝓓 δ , e)) ⊑⟨ 𝓕 ⟩ z
      v z p = transport
               (λ - → - ⊑⟨ 𝓕 ⟩ z)
               (e₁ ⁻¹)
               (∐-is-lowerbound-of-upperbounds
                 𝓕
                 i→f⟨αi,e⟩-is-directed
                 z
                 z-is-upperbound)
        where
         _→e-is-directed : is-Directed 𝓔 (λ _ → e)
         _→e-is-directed = constant-function-is-directed
                            𝓔
                            (inhabited-if-directed (underlying-order 𝓓) α δ)
                            e

         i→⟨αi,e⟩-is-directed : is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) (λ i → α (pr₁ i) , e)
         i→⟨αi,e⟩-is-directed = ⟨pr₁,pr₂⟩-is-directed 𝓓 𝓔 δ _→e-is-directed

         i→f⟨αi,e⟩-is-directed : is-Directed 𝓕 (λ i → f (α (pr₁ i ) , e))
         i→f⟨αi,e⟩-is-directed =
          image-is-directed
           (𝓓 ×ᵈᶜᵖᵒ 𝓔)
           𝓕
           (monotone-if-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 (f , f-is-continuous))
           i→⟨αi,e⟩-is-directed

         z-is-upperbound : is-upperbound
                             (underlying-order 𝓕)
                             z
                             (λ i → f (α (pr₁ i) , e))
         z-is-upperbound i = p (pr₁ i)
         e₁ : f (∐ 𝓓 δ , e) ＝ ∐ 𝓕 i→f⟨αi,e⟩-is-directed
         e₁ = f (∐ 𝓓 δ , e)                          ＝⟨ i ⟩
              f (∐ 𝓓 δ , ∐ 𝓔 _→e-is-directed)        ＝⟨ ii ⟩
              f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) i→⟨αi,e⟩-is-directed) ＝⟨ iii ⟩
              ∐ 𝓕 i→f⟨αi,e⟩-is-directed              ∎
          where
           i   = ap (λ - → f (∐ 𝓓 δ , -))
                    (constant-is-∐-of-constant-function 𝓔 _→e-is-directed)
           ii  = ap (λ - → f -) (⟨∐,∐⟩＝∐⟨,⟩ 𝓓 𝓔 δ _→e-is-directed)
           iii = continuous-∐-＝
                  (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                  𝓕 (f , f-is-continuous)
                  i→⟨αi,e⟩-is-directed

 continuous→continuous-in-pr₂ : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓕 ] → ⟨ 𝓓 ⟩ → DCPO[ 𝓔 , 𝓕 ]
 continuous→continuous-in-pr₂ 𝕗@(f , f-is-continuous) d =
  (λ e → f (d , e)) , continuous
   where
    continuous : is-continuous 𝓔 𝓕 (λ e → f (d , e))
    continuous I α δ = u , v
      where
        u : is-upperbound (underlying-order 𝓕) (f (d , ∐ 𝓔 δ)) (λ z → f (d , α z))
        u i = monotone-if-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔)
               𝓕
               𝕗
               (d , α i)
               (d , ∐ 𝓔 δ)
               ((reflexivity 𝓓 d) , (∐-is-upperbound 𝓔 δ i))

        v : (z : ⟨ 𝓕 ⟩)
          → ((i : I) → (f (d , α i)) ⊑⟨ 𝓕 ⟩ z)
          → (f (d , ∐ 𝓔 δ)) ⊑⟨ 𝓕 ⟩ z
        v z p = transport
                 (λ - → - ⊑⟨ 𝓕 ⟩ z)
                 (e ⁻¹)
                 (∐-is-lowerbound-of-upperbounds
                   𝓕
                   i→f⟨d,αi⟩-is-directed
                   z
                   z-is-upperbound)
          where
           _→d-is-directed : is-Directed 𝓓 (λ _ → d)
           _→d-is-directed = constant-function-is-directed
                              𝓓
                              (inhabited-if-directed (underlying-order 𝓔) α δ)
                              d

           i→⟨d,αi⟩-is-directed : is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) (λ i → d , α (pr₂ i))
           i→⟨d,αi⟩-is-directed = ⟨pr₁,pr₂⟩-is-directed 𝓓 𝓔 _→d-is-directed δ

           i→f⟨d,αi⟩-is-directed : is-Directed 𝓕 (λ i → f (d , α (pr₂ i)))
           i→f⟨d,αi⟩-is-directed = image-is-directed
                                    (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                                    𝓕
                                    (monotone-if-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 𝕗)
                                    i→⟨d,αi⟩-is-directed

           z-is-upperbound : is-upperbound
                               (underlying-order 𝓕)
                               z
                               (λ i → f (d , α (pr₂ i)))
           z-is-upperbound i = p (pr₂ i)

           e : f (d , ∐ 𝓔 δ) ＝ ∐ 𝓕 i→f⟨d,αi⟩-is-directed
           e = f (d , ∐ 𝓔 δ)                          ＝⟨ i ⟩
               f (∐ 𝓓 _→d-is-directed , ∐ 𝓔 δ)        ＝⟨ ii ⟩
               f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) i→⟨d,αi⟩-is-directed) ＝⟨ iii ⟩
               ∐ 𝓕 i→f⟨d,αi⟩-is-directed              ∎
                  where
                   i   = ap (λ - → f (- , ∐ 𝓔 δ))
                            (constant-is-∐-of-constant-function
                              𝓓 _→d-is-directed)
                   ii  = ap (λ - → f -)
                            (⟨∐,∐⟩＝∐⟨,⟩ 𝓓 𝓔 _→d-is-directed δ)
                   iii = continuous-∐-＝ (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 𝕗 i→⟨d,αi⟩-is-directed

 continuous-in-arguments→continuous : (f : ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ → ⟨ 𝓕 ⟩)
                                    → (∀ e → is-continuous 𝓓 𝓕 (λ d → f (d , e)))
                                    → (∀ d → is-continuous 𝓔 𝓕 (λ e → f (d , e)))
                                    → is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 f
 continuous-in-arguments→continuous f p₁ p₂ I α δ = u , v
  where
   f-is-monotone : is-monotone (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 f
   f-is-monotone x@(x₁ , x₂) y@(y₁ , y₂) (l₁ , l₂) =
    transitivity 𝓕 (f x) (f (x₁ , y₂)) (f y) m₁ m₂
    where
     m₁ : f x ⊑⟨ 𝓕 ⟩ f (x₁ , y₂)
     m₁ = monotone-if-continuous 𝓔 𝓕
          ((λ e → f (x₁ , e)) , p₂ x₁)
          x₂
          y₂
          l₂

     m₂ : f (x₁ , y₂) ⊑⟨ 𝓕 ⟩ f y
     m₂ = monotone-if-continuous 𝓓 𝓕
           ((λ d → f (d , y₂)) , p₁ y₂)
           x₁
           y₁
           l₁

   u : is-upperbound (underlying-order 𝓕) (f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) (f ∘ α)
   u i = transport (λ - → (f ∘ α) i ⊑⟨ 𝓕 ⟩ f -) (∐⟨,⟩＝⟨∐,∐⟩ 𝓓 𝓔 δ ⁻¹) e₁
    where
     d = pr₁∘α-is-Directed 𝓓 𝓔 δ
     e = pr₂∘α-is-Directed 𝓓 𝓔 δ

     e₁ : (f ∘ α) i ⊑⟨ 𝓕 ⟩ f (∐ 𝓓 d , ∐ 𝓔 e)
     e₁ = transitivity 𝓕
           ((f ∘ α) i)
           (f (pr₁ (α i) ,
            ∐ 𝓔 e)) (f (∐ 𝓓 d ,
            ∐ 𝓔 e))
           e₅
           e₄
      where
       e₄ : f (pr₁ (α i) , ∐ 𝓔 e) ⊑⟨ 𝓕 ⟩ f (∐ 𝓓 d , ∐ 𝓔 e)
       e₄ = monotone-if-continuous 𝓓 𝓕
             ((λ x → f (x , ∐ 𝓔 e)) ,
              p₁ (∐ 𝓔 e))
             (pr₁ (α i))
             (∐ 𝓓 d)
             (∐-is-upperbound 𝓓 d i)

       e₅ : f (pr₁ (α i) , pr₂ (α i)) ⊑⟨ 𝓕 ⟩ f (pr₁ (α i) , ∐ 𝓔 e)
       e₅ = monotone-if-continuous 𝓔 𝓕
             ((λ e → f (pr₁ (α i) , e)) , p₂ (pr₁ (α i)))
             (pr₂ (α i))
             (∐ 𝓔 e)
             (∐-is-upperbound 𝓔 e i)

   v : (z : ⟨ 𝓕 ⟩)
     → ((i : I) → f (α i) ⊑⟨ 𝓕 ⟩ z)
     → f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ) ⊑⟨ 𝓕 ⟩ z
   v z p = transport (λ - → - ⊑⟨ 𝓕 ⟩ z) (e₆ ⁻¹) p₃
    where
     d = pr₁∘α-is-Directed 𝓓 𝓔 δ
     e = pr₂∘α-is-Directed 𝓓 𝓔 δ

     de : is-Directed 𝓕 λ i → f (pr₁ (α i) , ∐ 𝓔 e)
     de = image-is-directed 𝓓 𝓕
           (monotone-if-continuous 𝓓 𝓕
             ((λ - → f (- , ∐ 𝓔 e)) ,
              p₁ (∐ 𝓔 e)))
           d

     f∘α-is-directed : is-Directed 𝓕 (f ∘ α)
     f∘α-is-directed = inhabited-if-directed (underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔)) α δ ,
                       order
      where
       order : (i j : I)
             → ∃ k ꞉ I , (underlying-order 𝓕 ((f ∘ α) i) ((f ∘ α) k) ×
                          underlying-order 𝓕 ((f ∘ α) j) ((f ∘ α) k))
       order i j = ∥∥-functor
                    (λ (a , b , c) → a , f-is-monotone (α i) (α a) b ,
                                         f-is-monotone (α j) (α a) c)
                    (semidirected-if-directed
                      (underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔))
                      α
                      δ
                      i
                      j)

     e₆ = f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ) ＝⟨ ii ⟩
          f (∐ 𝓓 d , ∐ 𝓔 e)   ＝⟨ iii ⟩
          ∐ 𝓕 de              ＝⟨ iv ⟩
          ∐ 𝓕 f∘α-is-directed ∎
      where
       ii  = ap (λ - → f -) (∐⟨,⟩＝⟨∐,∐⟩ 𝓓 𝓔 δ)
       iii = continuous-∐-＝ 𝓓 𝓕
              ((λ d → f (d , ∐ 𝓔 e)) ,
               p₁ (∐ 𝓔 e))
              d
       iv  = antisymmetry 𝓕 (∐ 𝓕 de) (∐ 𝓕 f∘α-is-directed) l₁ l₂
        where
         l₂ : ∐ 𝓕 f∘α-is-directed ⊑⟨ 𝓕 ⟩ ∐ 𝓕 de
         l₂ = ∐-is-lowerbound-of-upperbounds 𝓕 f∘α-is-directed (∐ 𝓕 de) u₂
          where
           u₂ : is-upperbound
                 (underlying-order 𝓕)
                 (∐ 𝓕 de)
                 (λ i → f (pr₁ (α i) , pr₂ (α i)))
           u₂ i = transitivity 𝓕
                   (f (α i))
                   (f (pr₁ (α i) , ∐ 𝓔 e))
                   (∐ 𝓕 de)
                   p₄
                   p₅
            where
              p₄ : f (pr₁ (α i) , pr₂ (α i)) ⊑⟨ 𝓕 ⟩ f (pr₁ (α i) , ∐ 𝓔 e)
              p₄ = monotone-if-continuous 𝓔 𝓕
                    ((λ e → f (pr₁ (α i) , e)) ,
                     p₂ (pr₁ (α i)))
                    (pr₂ (α i))
                    (∐ 𝓔 e)
                    (∐-is-upperbound 𝓔 e i)

              p₅ : f (pr₁ (α i) , ∐ 𝓔 e) ⊑⟨ 𝓕 ⟩ ∐ 𝓕 de
              p₅ = ∐-is-upperbound 𝓕 de i

         l₁ : ∐ 𝓕 de ⊑⟨ 𝓕 ⟩ ∐ 𝓕 f∘α-is-directed
         l₁ = ∐-is-lowerbound-of-upperbounds 𝓕 de (∐ 𝓕 f∘α-is-directed) u₂
          where
           u₂ : is-upperbound
                 (underlying-order 𝓕)
                 (∐ 𝓕 f∘α-is-directed)
                 (λ i → f (pr₁ (α i) , ∐ 𝓔 e))
           u₂ i = pr₂ (p₂ (pr₁ (α i))
                   I
                   (pr₂ ∘ α)
                   e)
                   (∐ 𝓕 f∘α-is-directed)
                   upper
             where
              upper : (i₁ : I)
                    → (f (pr₁ (α i) , pr₂ (α i₁))) ⊑⟨ 𝓕 ⟩ (∐ 𝓕 f∘α-is-directed)
              upper j = ∥∥-rec
                         (prop-valuedness 𝓕
                           (f (pr₁ (α i) , pr₂ (α j)))
                           (∐ 𝓕 f∘α-is-directed))
                         p₃
                         (semidirected-if-directed
                           (underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔))
                           α
                           δ
                           i
                           j)
               where
                p₃ : (Σ k ꞉ I , ((α i) ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (α k) ×
                                 (α j) ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (α k)))
                   → (f (pr₁ (α i) , pr₂ (α j))) ⊑⟨ 𝓕 ⟩ (∐ 𝓕 f∘α-is-directed)
                p₃ (k , (a , _) , (_ , b)) =
                 transitivity 𝓕
                  (f (pr₁ (α i) , pr₂ (α j)))
                  ((f ∘ α) k)
                  (∐ 𝓕 f∘α-is-directed)
                  (f-is-monotone
                    (pr₁ (α i) , pr₂ (α j))
                    (α k)
                    (a , b))
                  (∐-is-upperbound 𝓕 f∘α-is-directed k)

     p₃ : ∐ 𝓕 f∘α-is-directed ⊑⟨ 𝓕 ⟩ z
     p₃ = ∐-is-lowerbound-of-upperbounds 𝓕 f∘α-is-directed z p

\end{code}
