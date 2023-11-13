Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt

module DomainTheory.Basics.Products
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

open PropositionalTruncation pt

open import Posets.Poset fe
open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets

open PosetAxioms

\end{code}

First, let's define the product of two DCPOs.

\begin{code}

module DcpoProductsGeneral
        (𝓥 : Universe)
       where

 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.Miscelanea pt fe 𝓥
 open import DomainTheory.Basics.Pointed pt fe 𝓥

 module _ {D : 𝓤 ̇} {E : 𝓤' ̇} where

   _⊑-×_ : (D → D → 𝓣 ̇)
         → (E → E → 𝓣' ̇)
         → (D × E → D × E → 𝓣 ⊔ 𝓣' ̇)
   _⊑-×_ _⊑₁_ _⊑₂_ (a , b) (c , d) = (a ⊑₁ c) × (b ⊑₂ d)

   pr₁∘α-is-directed : {I : 𝓥 ̇}
                     → {α : I → D × E}
                     → (_⊑₁_ : D → D → 𝓣 ̇)
                     → (_⊑₂_ : E → E → 𝓣' ̇)
                     → is-directed (_⊑₁_ ⊑-× _⊑₂_) α
                     → is-directed _⊑₁_ (pr₁ ∘ α)
   pr₁∘α-is-directed {_} {_} {I} {α} _⊑₁_ _⊑₂_ δ =
    inhabited-if-directed (_⊑₁_ ⊑-× _⊑₂_) α δ , o
     where
      o : (i j : I)
        → ∃ k ꞉ I , ((pr₁ ∘ α) i ⊑₁ (pr₁ ∘ α) k ×
                     (pr₁ ∘ α) j ⊑₁ (pr₁ ∘ α) k)
      o i j = ∥∥-functor
               (λ (a , (b , _) , c , _) → a , b , c)
               (semidirected-if-directed (_⊑₁_ ⊑-× _⊑₂_) α δ i j)

   pr₂∘α-is-directed : {I : 𝓥 ̇}
                     → {α : I → D × E}
                     → (_⊑₁_ : D → D → 𝓣 ̇)
                     → (_⊑₂_ : E → E → 𝓣' ̇)
                     → is-directed (_⊑₁_ ⊑-× _⊑₂_) α
                     → is-directed _⊑₂_ (pr₂ ∘ α)
   pr₂∘α-is-directed {_} {_} {I} {α} _⊑₁_ _⊑₂_ δ =
    inhabited-if-directed (_⊑₁_ ⊑-× _⊑₂_) α δ , o
     where
      o : (i j : I)
        → ∃ k ꞉ I , ((pr₂ ∘ α) i ⊑₂ (pr₂ ∘ α) k ×
                     (pr₂ ∘ α) j ⊑₂ (pr₂ ∘ α) k)
      o i j = ∥∥-functor
               (λ (a , (_  , b) , _ , c) → a , b , c)
               (semidirected-if-directed (_⊑₁_ ⊑-× _⊑₂_) α δ i j)

 infixr 30 _×ᵈᶜᵖᵒ_

 _×ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → DCPO {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
 𝓓 ×ᵈᶜᵖᵒ 𝓔 = (⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩) ,
             (underlying-order 𝓓) ⊑-× (underlying-order 𝓔) ,
             axioms
  where
   axioms : dcpo-axioms (underlying-order 𝓓 ⊑-× underlying-order 𝓔)
   axioms = (×-is-set (sethood 𝓓) (sethood 𝓔) , prop , r , t , a) , c
    where
     _⊑𝓓_ = underlying-order 𝓓
     _⊑𝓔_ = underlying-order 𝓔
     _⊑_  = _⊑𝓓_ ⊑-× _⊑𝓔_

     prop : is-prop-valued _⊑_
     prop (x₁ , x₂) (y₁ , y₂) (a₁ , a₂) (b₁ , b₂) =
      to-×-＝
       (prop-valuedness 𝓓 x₁ y₁ a₁ b₁)
       (prop-valuedness 𝓔 x₂ y₂ a₂ b₂)

     r : is-reflexive _⊑_
     r a = reflexivity 𝓓 (pr₁ a) ,
           reflexivity 𝓔 (pr₂ a)

     t : is-transitive _⊑_
     t (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) (u₁ , u₂) (v₁ , v₂) = w₁ , w₂
      where
       w₁ = x₁ ⊑⟨ 𝓓 ⟩[ u₁ ]
            y₁ ⊑⟨ 𝓓 ⟩[ v₁ ]
            z₁ ∎⟨ 𝓓 ⟩

       w₂ = x₂ ⊑⟨ 𝓔 ⟩[ u₂ ]
            y₂ ⊑⟨ 𝓔 ⟩[ v₂ ]
            z₂ ∎⟨ 𝓔 ⟩

     a : is-antisymmetric _⊑_
     a (a , b) (c , d) (a-⊑-c , b-⊑-d) (c-⊑-a , d-⊑-b) =
      to-×-＝
       (antisymmetry 𝓓 a c a-⊑-c c-⊑-a)
       (antisymmetry 𝓔 b d b-⊑-d d-⊑-b)

     c : is-directed-complete _⊑_
     c I α δ = (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) , s
      where
       pr₁∘α-is-dir : is-Directed 𝓓 (pr₁ ∘ α)
       pr₁∘α-is-dir = pr₁∘α-is-directed _⊑𝓓_ _⊑𝓔_ δ

       pr₂∘α-is-dir : is-Directed 𝓔 (pr₂ ∘ α)
       pr₂∘α-is-dir = pr₂∘α-is-directed _⊑𝓓_ _⊑𝓔_ δ

       s : is-sup _⊑_ (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
       s = is-upper , is-least-upper
        where
         is-upper : is-upperbound _⊑_ (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
         is-upper i = (∐-is-upperbound 𝓓 pr₁∘α-is-dir i ,
                       ∐-is-upperbound 𝓔 pr₂∘α-is-dir i)

         is-least-upper : (t : ⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩)
                        → is-upperbound _⊑_ t α
                        → _⊑_ (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) t
         is-least-upper t@(x , y) u = lub-of-x , lub-of-y
           where
            x-is-upperbound : is-upperbound _⊑𝓓_ x (pr₁ ∘ α)
            x-is-upperbound i = pr₁ (u i)

            y-is-upperbound : is-upperbound _⊑𝓔_ y (pr₂ ∘ α)
            y-is-upperbound i = pr₂ (u i)

            lub-of-x = ∐-is-lowerbound-of-upperbounds 𝓓
                        pr₁∘α-is-dir
                        x
                        x-is-upperbound

            lub-of-y = ∐-is-lowerbound-of-upperbounds
                        𝓔
                        pr₂∘α-is-dir
                        y
                        y-is-upperbound
\end{code}

Some useful proofs on products.

\begin{code}

 module _ (𝓓 : DCPO {𝓤} {𝓤'}) where

   constant-function-is-directed : { I : 𝓥 ̇} (h : ∥ I ∥) (d : ⟨ 𝓓 ⟩)
                                 → is-Directed 𝓓 (λ (i : I) → d)
   constant-function-is-directed h d =
    h , λ i j → ∣ i , (reflexivity 𝓓 d , reflexivity 𝓓 d) ∣

   constant-is-∐-of-constant-function : {I : 𝓥 ̇}
                                        {d : ⟨ 𝓓 ⟩}
                                        (δ : is-Directed 𝓓 (λ (i : I) → d))
                                      → d ＝ ∐ 𝓓 δ
   constant-is-∐-of-constant-function {I} {d} δ = antisymmetry 𝓓 d (∐ 𝓓 δ) l₁ l₂
    where
     l₁ : d ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
     l₁ = ∥∥-rec
           (prop-valuedness 𝓓 d (∐ 𝓓 δ))
           (λ (i : I) → ∐-is-upperbound 𝓓 δ i) (pr₁ δ)

     l₂ : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ d
     l₂ = ∐-is-lowerbound-of-upperbounds 𝓓
           δ
           d
           (λ i → reflexivity 𝓓 d)

 module _ (𝓓 : DCPO {𝓤} {𝓤'})
          (𝓔 : DCPO {𝓣} {𝓣'})
        where

   pr₁∘α-is-Directed : {I : 𝓥 ̇}
                       {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
                     → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α
                     → is-Directed 𝓓 (pr₁ ∘ α)
   pr₁∘α-is-Directed {I} {α} δ =
    pr₁∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ

   pr₂∘α-is-Directed : {I : 𝓥 ̇}
                       {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
                     → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α
                     → is-Directed 𝓔 (pr₂ ∘ α)
   pr₂∘α-is-Directed = pr₂∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔)

   ⟨pr₁,pr₂⟩-is-directed : {I : 𝓥 ̇}
                         → {α₁ : I → ⟨ 𝓓 ⟩}
                         → {α₂ : I → ⟨ 𝓔 ⟩}
                         → is-Directed 𝓓 α₁
                         → is-Directed 𝓔 α₂
                         → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                            (λ ((i₁ , i₂) : I × I) → (α₁ i₁ , α₂ i₂))

   ⟨pr₁,pr₂⟩-is-directed δ₁@(h₁ , s₁) δ₂@(h₂ , s₂) =
    (binary-choice h₁ h₂) ,
     λ (i₁ , i₂) (j₁ , j₂)
       → ∥∥-functor
          (λ ((a₁ , b₁ , c₁) , (a₂ , b₂ , c₂)) → (a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂))
          (binary-choice (s₁ i₁ j₁) (s₂ i₂ j₂))

   ∐⟨,⟩＝⟨∐,∐⟩ : {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
               → (δ : is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α)
               → ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ
               ＝ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
   ∐⟨,⟩＝⟨∐,∐⟩ {I} {α} δ =
    antisymmetry (𝓓 ×ᵈᶜᵖᵒ 𝓔)
     (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)
     (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
     ∐⟨,⟩⊑⟨∐,∐⟩
     ⟨∐,∐⟩⊑∐⟨,⟩
     where
       ∐⟨,⟩⊑⟨∐,∐⟩ : ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ
                     ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩
                    (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
       ∐⟨,⟩⊑⟨∐,∐⟩ = ∐-is-lowerbound-of-upperbounds (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                      δ
                      (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
                      ∐,∐-is-upperbound
         where
          ∐,∐-is-upperbound : (i : I)
                            → (α i)
                            ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (∐ 𝓓 (pr₁∘α-is-Directed δ) ,
                                            ∐ 𝓔 (pr₂∘α-is-Directed δ))
          ∐,∐-is-upperbound i = (∐-is-upperbound 𝓓 (pr₁∘α-is-Directed δ) i) ,
                                (∐-is-upperbound 𝓔 (pr₂∘α-is-Directed δ) i)

       ⟨∐,∐⟩⊑∐⟨,⟩ : (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
                  ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)
       ⟨∐,∐⟩⊑∐⟨,⟩ = ⊑₁ , ⊑₂
         where
          ⊑₁ : (∐ 𝓓 (pr₁∘α-is-Directed δ)) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
          ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓓
                (pr₁∘α-is-Directed δ)
                (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
                pr₁-∐⟨,⟩-is-upperbound
           where
            pr₁-∐⟨,⟩-is-upperbound : (i : I)
                                   → ((pr₁ ∘ α) i) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
            pr₁-∐⟨,⟩-is-upperbound i = pr₁ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)

          ⊑₂ : ∐ 𝓔 (pr₂∘α-is-Directed δ) ⊑⟨ 𝓔 ⟩ pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)
          ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓔
                (pr₂∘α-is-Directed δ)
                (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
                pr₂-∐⟨,⟩-is-upperbound
           where
            pr₂-∐⟨,⟩-is-upperbound : (i : I)
                                   → ((pr₂ ∘ α) i) ⊑⟨ 𝓔 ⟩ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
            pr₂-∐⟨,⟩-is-upperbound i = pr₂ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)

   ⟨∐,∐⟩＝∐⟨,⟩ : {I : 𝓥 ̇}
               → {α₁ : I → ⟨ 𝓓 ⟩}
               → {α₂ : I → ⟨ 𝓔 ⟩}
               → (δ₁ : is-Directed 𝓓 α₁)
               → (δ₂ : is-Directed 𝓔 α₂)
               → (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂) ＝ ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
   ⟨∐,∐⟩＝∐⟨,⟩ {I} {α₁} {α₂} δ₁ δ₂ = antisymmetry (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                                      (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
                                      (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                                      (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))
                                      ⟨∐,∐⟩⊑∐⟨,⟩ ∐⟨,⟩⊑⟨∐,∐⟩
     where
       ⟨∐,∐⟩⊑∐⟨,⟩ : (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
                  ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
       ⟨∐,∐⟩⊑∐⟨,⟩ = ⊑₁ , ⊑₂
         where
          ⊑₁ : ∐ 𝓓 δ₁ ⊑⟨ 𝓓 ⟩ pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))
          ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓓
                δ₁
                (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
                p
           where
            p : (i : I)
              → (α₁ i) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
            p i = pr₁ (∐-is-upperbound ((𝓓 ×ᵈᶜᵖᵒ 𝓔))
                        (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
                        (i , i))

          ⊑₂ : ∐ 𝓔 δ₂ ⊑⟨ 𝓔 ⟩ pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))
          ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓔
                δ₂
                (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
                p
           where
            p : (i : I)
              → (α₂ i) ⊑⟨ 𝓔 ⟩ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
            p i = pr₂ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                        (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
                        (i , i))


       ∐⟨,⟩⊑⟨∐,∐⟩ : ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
                  ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
       ∐⟨,⟩⊑⟨∐,∐⟩ = ∐-is-lowerbound-of-upperbounds (𝓓 ×ᵈᶜᵖᵒ 𝓔)
                      (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
                      (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
                      upperbound
         where
          upperbound : (i : I × I)
                     → (α₁ (pr₁ i) , α₂ (pr₂ i)) ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
          upperbound i = ∐-is-upperbound 𝓓 δ₁ (pr₁ i) ,
                         ∐-is-upperbound 𝓔 δ₂ (pr₂ i)

   pr₁-is-continuous : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓓 ]
   pr₁-is-continuous = pr₁ , c
    where
     c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓓 pr₁
     c I α δ = u , v
      where
       u : is-upperbound (underlying-order 𝓓) (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) (pr₁ ∘ α)
       u i = pr₁ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)

       v : (x : ⟨ 𝓓 ⟩)
         → ((i : I) → (pr₁ (α i)) ⊑⟨ 𝓓 ⟩ x)
         → (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) ⊑⟨ 𝓓 ⟩ x
       v x p = transport (λ - → pr₁ - ⊑⟨ 𝓓 ⟩ x) (∐⟨,⟩＝⟨∐,∐⟩ δ) d
        where
         d : pr₁ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ)) ⊑⟨ 𝓓 ⟩ x
         d = ∐-is-lowerbound-of-upperbounds 𝓓 (pr₁∘α-is-Directed δ) x p

   pr₂-is-continuous : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓔 ]
   pr₂-is-continuous = pr₂ , c
    where
     c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓔 pr₂
     c I α δ = u , v
      where
       u : is-upperbound (underlying-order 𝓔) (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) (pr₂ ∘ α)
       u i = pr₂ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)

       v : (y : ⟨ 𝓔 ⟩)
         → ((i : I) → (pr₂ (α i)) ⊑⟨ 𝓔 ⟩ y)
         → (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) ⊑⟨ 𝓔 ⟩ y
       v y p = transport (λ - → pr₂ - ⊑⟨ 𝓔 ⟩ y) (∐⟨,⟩＝⟨∐,∐⟩ δ) e
        where
         e : pr₂ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ)) ⊑⟨ 𝓔 ⟩ y
         e = ∐-is-lowerbound-of-upperbounds 𝓔 (pr₂∘α-is-Directed δ) y p

 infixr 30 _×ᵈᶜᵖᵒ⊥_

 _×ᵈᶜᵖᵒ⊥_ : DCPO⊥ {𝓤} {𝓣}
          → DCPO⊥ {𝓤'} {𝓣'}
          → DCPO⊥ {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 = ((𝓓 ⁻) ×ᵈᶜᵖᵒ (𝓔 ⁻)) , least , p
  where
   least : ⟨ (𝓓 ⁻) ×ᵈᶜᵖᵒ (𝓔 ⁻) ⟩
   least = ⊥ 𝓓 , ⊥ 𝓔

   p : is-least (underlying-order ((𝓓 ⁻) ×ᵈᶜᵖᵒ (𝓔 ⁻))) least
   p x = (⊥-is-least 𝓓 (pr₁ x)) , (⊥-is-least 𝓔 (pr₂ x))

 module _ (𝓓 : DCPO {𝓤} {𝓤'})
          (𝓔 : DCPO {𝓣} {𝓣'})
          (𝓕 : DCPO {𝓦} {𝓦'})
        where

   ×ᵈᶜᵖᵒ-assoc₁ : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕 , (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ]
   ×ᵈᶜᵖᵒ-assoc₁ = f , c
    where
     f : ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩ → ⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩
     f (d , e , f) = (d , e) , f

     f-is-monotone : is-monotone (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) ((𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕) f
     f-is-monotone x y p = ((pr₁ p) , (pr₁ (pr₂ p))) , (pr₂ (pr₂ p))

     c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) ((𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕) f
     c I α δ = u , v
      where
       assoc-∐ : ⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩
       assoc-∐ = (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ) ,
                  (pr₁ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ)))) ,
                 pr₂ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ))

       u : is-upperbound
            (underlying-order ((𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕))
            assoc-∐
            (λ i → ((pr₁ (α i)) , (pr₁ (pr₂ (α i)))) , (pr₂ (pr₂ (α i))))
       u i = (pr₁ p , pr₁ (pr₂ p)) , pr₂ (pr₂ p)
        where
         p = ∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ i

       v : (w : ⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩)
         → ((i : I) → f (α i) ⊑⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩ w)
         → f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ) ⊑⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩ w
       v w@((x , y) , z) p = f-is-monotone (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ) w' l
         where
          w' = x , (y , z)

          w'-is-upperbound : is-upperbound
                              (underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕))
                              w'
                              α
          w'-is-upperbound i = (pr₁ (pr₁ (p i))) , (pr₂ (pr₁ (p i))) , (pr₂ (p i))

          l : ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩ w'
          l = ∐-is-lowerbound-of-upperbounds (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕)
               δ
               w'
               w'-is-upperbound

   to-×-DCPO : DCPO[ 𝓓 , 𝓔 ] →  DCPO[ 𝓓 , 𝓕 ] → DCPO[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ 𝓕 ]
   to-×-DCPO 𝕗@(f , fc) 𝕘@(g , gc) = h , hc
    where
     h : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩
     h d = f d , g d

     h-is-monotone : is-monotone 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
     h-is-monotone x y p = monotone-if-continuous 𝓓 𝓔 𝕗 x y p ,
                           monotone-if-continuous 𝓓 𝓕 𝕘 x y p

     hc : is-continuous 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
     hc I α δ = u , v
      where
       u : is-upperbound (underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕)) (h (∐ 𝓓 δ)) (h ∘ α)
       u i = h-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)

       v : (t : ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩)
         → ((i : I) → (h (α i)) ⊑⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩ t)
         → (h (∐ 𝓓 δ)) ⊑⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩ t
       v t@(y , z) p = lf , lg
        where
         lf : f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ y
         lf = transport (λ - → - ⊑⟨ 𝓔 ⟩ y) (q ⁻¹) l
          where
           ε : is-Directed 𝓔 (f ∘ α)
           ε = image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 𝕗) δ

           q : f (∐ 𝓓 δ) ＝ ∐ 𝓔 ε
           q = continuous-∐-＝ 𝓓 𝓔 𝕗 δ

           l : ∐ 𝓔 ε ⊑⟨ 𝓔 ⟩ y
           l = ∐-is-lowerbound-of-upperbounds 𝓔 ε y (λ i → pr₁ (p i))

         lg : g (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ z
         lg = transport (λ - → - ⊑⟨ 𝓕 ⟩ z) (q ⁻¹) l
          where
           ϕ : is-Directed 𝓕 (g ∘ α)
           ϕ = image-is-directed 𝓓 𝓕 (monotone-if-continuous 𝓓 𝓕 𝕘) δ

           q : g (∐ 𝓓 δ) ＝ ∐ 𝓕 ϕ
           q = continuous-∐-＝ 𝓓 𝓕 𝕘 δ

           l : ∐ 𝓕 ϕ ⊑⟨ 𝓕 ⟩ z
           l = ∐-is-lowerbound-of-upperbounds 𝓕 ϕ z (λ i → pr₂ (p i))

 module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
          (𝓔 : DCPO⊥ {𝓣} {𝓣'})
          (𝓕 : DCPO⊥ {𝓦} {𝓦'})
       where

   ×ᵈᶜᵖᵒ⊥-assoc₁ : DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 ×ᵈᶜᵖᵒ⊥ 𝓕 , (𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔) ×ᵈᶜᵖᵒ⊥ 𝓕 ]
   ×ᵈᶜᵖᵒ⊥-assoc₁ = ×ᵈᶜᵖᵒ-assoc₁ (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻)

   to-×-DCPO⊥ : DCPO⊥[ 𝓓 , 𝓔 ] → DCPO⊥[ 𝓓 , 𝓕 ] → DCPO⊥[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ⊥ 𝓕 ]
   to-×-DCPO⊥ f g = to-×-DCPO (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻) f g

\end{code}
