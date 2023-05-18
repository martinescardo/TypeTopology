Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt

module PCF.DcpoProducts
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

open PropositionalTruncation pt

open import Posets.Poset fe
open import UF.Base
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

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
  open import DomainTheory.ScottModelOfPCF.PCFCombinators pt fe 𝓥

  module _ {D : 𝓤 ̇} {E : 𝓤' ̇} where

    _⊑-×_ : (D → D → 𝓣 ̇)
            → (E → E → 𝓣' ̇)
            → (D × E → D × E → 𝓣 ⊔ 𝓣' ̇)
    _⊑-×_ R₁ R₂ (a , b) (c , d) = R₁ a c × R₂ b d

    pr₁∘α-is-directed : {I : 𝓥 ̇}
                        → {α : I → D × E}
                        → (order₁ : D → D → 𝓣 ̇)
                        → (order₂ : E → E → 𝓣' ̇)
                        → is-directed (order₁ ⊑-× order₂) α
                        → is-directed order₁ (pr₁ ∘ α)
    pr₁∘α-is-directed {_} {_} {I} {α} order₁ order₂ δ = inhabited-if-directed (order₁ ⊑-× order₂) α δ , o
      where
        o : (i j : I) →
              ∃
              (λ k →
                 order₁ ((pr₁ ∘ α) i) ((pr₁ ∘ α) k) ×
                 order₁ ((pr₁ ∘ α) j) ((pr₁ ∘ α) k))
        o i j = ∥∥-functor (λ x → (pr₁ x) , (pr₁ (pr₁ (pr₂ x)) , pr₁ (pr₂ (pr₂ x)))) (semidirected-if-directed (order₁ ⊑-× order₂) α δ i j)

    pr₂∘α-is-directed : {I : 𝓥 ̇}
                        → {α : I → D × E}
                        → (order₁ : D → D → 𝓣 ̇)
                        → (order₂ : E → E → 𝓣' ̇)
                        → is-directed (order₁ ⊑-× order₂) α
                        → is-directed order₂ (pr₂ ∘ α)
    pr₂∘α-is-directed {_} {_} {I} {α} order₁ order₂ δ = inhabited-if-directed (order₁ ⊑-× order₂) α δ , o
      where
        o : (i j : I) →
              ∃
              (λ k →
                 order₂ ((pr₂ ∘ α) i) ((pr₂ ∘ α) k) ×
                 order₂ ((pr₂ ∘ α) j) ((pr₂ ∘ α) k))
        o i j = ∥∥-functor (λ x → (pr₁ x) , (pr₂ (pr₁ (pr₂ x)) , pr₂ (pr₂ (pr₂ x)))) (semidirected-if-directed (order₁ ⊑-× order₂) α δ i j)

  infixr 30 _×ᵈᶜᵖᵒ_

  _×ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → DCPO {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
  𝓓 ×ᵈᶜᵖᵒ 𝓔 = (⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩) ,
                   (underlying-order 𝓓) ⊑-× (underlying-order 𝓔),
                   axioms
    where
      axioms : dcpo-axioms (underlying-order 𝓓 ⊑-× underlying-order 𝓔)
      axioms = ((×-is-set (sethood 𝓓) (sethood 𝓔)) , prop , r , t , a) , c
        where
          𝓓-order = underlying-order 𝓓
          𝓔-order = underlying-order 𝓔
          order = 𝓓-order ⊑-× 𝓔-order

          prop : is-prop-valued order
          prop x y (a , b) (c , d) = to-×-＝ (prop-valuedness 𝓓 (pr₁ x) (pr₁ y) a c)
                                             (prop-valuedness 𝓔 (pr₂ x) (pr₂ y) b d)

          r : is-reflexive order
          r a = (reflexivity 𝓓 (pr₁ a)) , (reflexivity 𝓔 (pr₂ a))

          t : is-transitive order
          t x y z x-⊑-y y-⊑-z = e₁ , e₂
            where
              e₁ : pr₁ x ⊑⟨ 𝓓 ⟩ pr₁ z
              e₁ = pr₁ x ⊑⟨ 𝓓 ⟩[ pr₁ x-⊑-y ]
                   pr₁ y ⊑⟨ 𝓓 ⟩[ pr₁ y-⊑-z ]
                   pr₁ z ∎⟨ 𝓓 ⟩
              e₂ : pr₂ x ⊑⟨ 𝓔 ⟩ pr₂ z
              e₂ = pr₂ x ⊑⟨ 𝓔 ⟩[ pr₂ x-⊑-y ]
                   pr₂ y ⊑⟨ 𝓔 ⟩[ pr₂ y-⊑-z ]
                   pr₂ z ∎⟨ 𝓔 ⟩

          a : is-antisymmetric order
          a (a , b) (c , d) (a-⊑-c , b-⊑-d) (c-⊑-a , d-⊑-b) = to-×-＝ (antisymmetry 𝓓 a c a-⊑-c c-⊑-a)
                                                                       (antisymmetry 𝓔 b d b-⊑-d d-⊑-b)

          c : is-directed-complete order
          c I α δ = (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) , s
            where
              pr₁∘α-is-dir : is-Directed 𝓓 (pr₁ ∘ α)
              pr₁∘α-is-dir = pr₁∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ
              pr₂∘α-is-dir : is-Directed 𝓔 (pr₂ ∘ α)
              pr₂∘α-is-dir = pr₂∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ
              s : is-sup order (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
              s = is-upper , is-least-upper
                where
                  is-upper : is-upperbound order (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
                  is-upper i = (∐-is-upperbound 𝓓 pr₁∘α-is-dir i) , (∐-is-upperbound 𝓔 pr₂∘α-is-dir i)
                  is-least-upper : (u : ⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩)
                                   → is-upperbound order u α
                                   → order (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) u
                  is-least-upper u u-is-upperbound = lub-in-pr₁ , lub-in-pr₂
                    where
                      lub-in-pr₁ = ∐-is-lowerbound-of-upperbounds 𝓓 pr₁∘α-is-dir (pr₁ u) pr₁-u-is-upperbound
                        where
                          pr₁-u-is-upperbound : is-upperbound (underlying-order 𝓓) (pr₁ u) (pr₁ ∘ α)
                          pr₁-u-is-upperbound i = pr₁ (u-is-upperbound i)
                      lub-in-pr₂ = ∐-is-lowerbound-of-upperbounds 𝓔 pr₂∘α-is-dir (pr₂ u) pr₂-u-is-upperbound
                        where
                          pr₂-u-is-upperbound : is-upperbound (underlying-order 𝓔) (pr₂ u) (pr₂ ∘ α)
                          pr₂-u-is-upperbound i = pr₂ (u-is-upperbound i)
\end{code}

Some useful proofs on products...

\begin{code}

  module _ (𝓓 : DCPO {𝓤} {𝓤'})
        where

    constant-function-is-directed : ∀ { I : 𝓥 ̇} (inhabited : ∥ I ∥) (d : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (λ (i : I) → d)
    constant-function-is-directed inhabited d = inhabited , λ i j → ∣ i , ((reflexivity 𝓓 d) , (reflexivity 𝓓 d)) ∣

    constant-is-∐-of-constant-function : ∀ {I : 𝓥 ̇} {d : ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 (λ (i : I) → d)) → d ＝ ∐ 𝓓 δ
    constant-is-∐-of-constant-function {I} {d} δ = antisymmetry 𝓓 d (∐ 𝓓 δ) ⊑₁ ⊑₂
                          where
                            ⊑₁ : d ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                            ⊑₁ = ∥∥-rec (prop-valuedness 𝓓 d (∐ 𝓓 δ)) (λ (i : I) → ∐-is-upperbound 𝓓 δ i) (pr₁ δ)
                            ⊑₂ : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ d
                            ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓓 δ d (λ i → reflexivity 𝓓 d)

  module _ (𝓓 : DCPO {𝓤} {𝓤'})
          (𝓔 : DCPO {𝓣} {𝓣'})
        where

    pr₁∘α-is-Directed : {I : 𝓥 ̇}
                        → {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
                        → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α
                        → is-Directed 𝓓 (pr₁ ∘ α)
    pr₁∘α-is-Directed {I} {α} δ = pr₁∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ

    pr₂∘α-is-Directed : {I : 𝓥 ̇}
                        → {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
                        → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α
                        → is-Directed 𝓔 (pr₂ ∘ α)
    pr₂∘α-is-Directed {I} {α} δ = pr₂∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ

    ⟨pr₁,pr₂⟩-is-directed : {I : 𝓥 ̇}
                            → {α₁ : I → ⟨ 𝓓 ⟩}
                            → {α₂ : I → ⟨ 𝓔 ⟩}
                            → (δ₁ : is-Directed 𝓓 α₁)
                            → (δ₂ : is-Directed 𝓔 α₂)
                            → is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) (λ (i : I × I) → (α₁ (pr₁ i) , α₂ (pr₂ i)))
    ⟨pr₁,pr₂⟩-is-directed δ₁ δ₂ = (binary-choice (pr₁ δ₁) (pr₁ δ₂)) ,
                                      λ i j → ∥∥-functor
                                                  (λ x →
                                                     ((pr₁ (pr₁ x)) , (pr₁ (pr₂ x))) ,
                                                           (((pr₁ (pr₂ (pr₁ x))) , (pr₁ (pr₂ (pr₂ x)))) ,
                                                             ((pr₂ (pr₂ (pr₁ x))) , (pr₂ (pr₂ (pr₂ x))))))
                                                  (binary-choice (pr₂ δ₁ (pr₁ i) (pr₁ j)) (pr₂ δ₂ (pr₂ i) (pr₂ j)))

    ∐⟨,⟩＝⟨∐,∐⟩ : {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩}
                             → (δ : is-Directed (𝓓 ×ᵈᶜᵖᵒ 𝓔) α)
                             → ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ ＝ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
    ∐⟨,⟩＝⟨∐,∐⟩ {I} {α} δ = antisymmetry (𝓓 ×ᵈᶜᵖᵒ 𝓔)
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
                                      ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩
                                    (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
            ∐,∐-is-upperbound i = (∐-is-upperbound 𝓓 (pr₁∘α-is-Directed δ) i) , (∐-is-upperbound 𝓔 (pr₂∘α-is-Directed δ) i)
        ⟨∐,∐⟩⊑∐⟨,⟩ : (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ))
                          ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩
                       (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)
        ⟨∐,∐⟩⊑∐⟨,⟩ = ⊑₁ , ⊑₂
          where
            ⊑₁ : (∐ 𝓓 (pr₁∘α-is-Directed δ)) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
            ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓓 (pr₁∘α-is-Directed δ) (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) pr₁-∐⟨,⟩-is-upperbound
              where
                pr₁-∐⟨,⟩-is-upperbound : (i : I) → ((pr₁ ∘ α) i) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
                pr₁-∐⟨,⟩-is-upperbound i = pr₁ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)
            ⊑₂ : ∐ 𝓔 (pr₂∘α-is-Directed δ) ⊑⟨ 𝓔 ⟩ pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)
            ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓔 (pr₂∘α-is-Directed δ) (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) pr₂-∐⟨,⟩-is-upperbound
              where
                pr₂-∐⟨,⟩-is-upperbound : (i : I) → ((pr₂ ∘ α) i) ⊑⟨ 𝓔 ⟩ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ))
                pr₂-∐⟨,⟩-is-upperbound i = pr₂ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)

    ⟨∐,∐⟩＝∐⟨,⟩ : {I : 𝓥 ̇}
                 → {α₁ : I → ⟨ 𝓓 ⟩}
                 → {α₂ : I → ⟨ 𝓔 ⟩}
                 → (δ₁ : is-Directed 𝓓 α₁)
                 → (δ₂ : is-Directed 𝓔 α₂)
                 → (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂) ＝ ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
    ⟨∐,∐⟩＝∐⟨,⟩ {I} {α₁} {α₂} δ₁ δ₂ = antisymmetry (𝓓 ×ᵈᶜᵖᵒ 𝓔) (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂) (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)) ⟨∐,∐⟩⊑∐⟨,⟩ ∐⟨,⟩⊑⟨∐,∐⟩
      where
        ⟨∐,∐⟩⊑∐⟨,⟩ : (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂) ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)
        ⟨∐,∐⟩⊑∐⟨,⟩ = ⊑₁ , ⊑₂
          where
            ⊑₁ : ∐ 𝓓 δ₁ ⊑⟨ 𝓓 ⟩ pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))
            ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓓 δ₁ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))) p
              where
                p : (i : I) →
                      (α₁ i) ⊑⟨ 𝓓 ⟩ (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
                p i = pr₁ (∐-is-upperbound ((𝓓 ×ᵈᶜᵖᵒ 𝓔)) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂) (i , i))
            ⊑₂ : ∐ 𝓔 δ₂ ⊑⟨ 𝓔 ⟩ pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))
            ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₂ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂))) p
              where
                p : (i : I) →
                      (α₂ i) ⊑⟨ 𝓔 ⟩ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂)))
                p i = pr₂ (∐-is-upperbound ((𝓓 ×ᵈᶜᵖᵒ 𝓔)) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂) (i , i))


        ∐⟨,⟩⊑⟨∐,∐⟩ : ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂) ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
        ∐⟨,⟩⊑⟨∐,∐⟩ = ∐-is-lowerbound-of-upperbounds (𝓓 ×ᵈᶜᵖᵒ 𝓔) (⟨pr₁,pr₂⟩-is-directed δ₁ δ₂) (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂) upperbound
          where
            upperbound : (i : I × I) →
                           underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔) (α₁ (pr₁ i) , α₂ (pr₂ i)) (∐ 𝓓 δ₁ , ∐ 𝓔 δ₂)
            upperbound i = (∐-is-upperbound 𝓓 δ₁ (pr₁ i)) , (∐-is-upperbound 𝓔 δ₂ (pr₂ i))

    pr₁-is-continuous : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓓 ]
    pr₁-is-continuous = pr₁ , c
      where
        c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓓 pr₁
        c I α δ = u , v
          where
            u : is-upperbound (underlying-order 𝓓) (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) (pr₁ ∘ α)
            u i = pr₁ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)
            v : (u₁ : ⟨ 𝓓 ⟩) →
                  ((i : I) → (pr₁ (α i)) ⊑⟨ 𝓓 ⟩ u₁) →
                  (pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) ⊑⟨ 𝓓 ⟩ u₁
            v u₁ p = transport (λ - → pr₁ - ⊑⟨ 𝓓 ⟩ u₁) (∐⟨,⟩＝⟨∐,∐⟩ δ) ⊑₁
              where
                ⊑₁ : pr₁ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ)) ⊑⟨ 𝓓 ⟩ u₁
                ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓓 (pr₁∘α-is-Directed δ) u₁ p

    pr₂-is-continuous : DCPO[ 𝓓 ×ᵈᶜᵖᵒ 𝓔 , 𝓔 ]
    pr₂-is-continuous = pr₂ , c
      where
        c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓔 pr₂
        c I α δ = u , v
          where
            u : is-upperbound (underlying-order 𝓔) (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) (pr₂ ∘ α)
            u i = pr₂ (∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ i)
            v : (u₁ : ⟨ 𝓔 ⟩) →
                  ((i : I) → (pr₂ (α i)) ⊑⟨ 𝓔 ⟩ u₁) →
                  (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔) δ)) ⊑⟨ 𝓔 ⟩ u₁
            v u₁ p = transport (λ - → pr₂ - ⊑⟨ 𝓔 ⟩ u₁) (∐⟨,⟩＝⟨∐,∐⟩ δ) ⊑₁
              where
                ⊑₁ : pr₂ (∐ 𝓓 (pr₁∘α-is-Directed δ) , ∐ 𝓔 (pr₂∘α-is-Directed δ)) ⊑⟨ 𝓔 ⟩ u₁
                ⊑₁ = ∐-is-lowerbound-of-upperbounds 𝓔 (pr₂∘α-is-Directed δ) u₁ p

\end{code}

\begin{code}


  infixr 30 _×ᵈᶜᵖᵒ⊥_

  _×ᵈᶜᵖᵒ⊥_ : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'}
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
            assoc-∐ = ((pr₁ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ)) , (pr₁ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ)))) , (pr₂ (pr₂ (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ)))
            u : is-upperbound (underlying-order ((𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕)) assoc-∐ λ i → ((pr₁ (α i)) , (pr₁ (pr₂ (α i)))) , (pr₂ (pr₂ (α i)))
            u i = (pr₁ proof , pr₁ (pr₂ proof)) , pr₂ (pr₂ proof)
              where
                proof = ∐-is-upperbound (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ i

            v : (u₁ : ⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩) →
                  ((i : I) → f (α i) ⊑⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩ u₁) →
                  f (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ) ⊑⟨ (𝓓 ×ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓕 ⟩ u₁
            v u₁ p = f-is-monotone (∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ) f⁻¹u₁ e₁
              where
                f⁻¹u₁ = pr₁ (pr₁ u₁) , pr₂ (pr₁ u₁) , pr₂ u₁
                e₁ : ∐ (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ ⊑⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩ f⁻¹u₁
                e₁ = ∐-is-lowerbound-of-upperbounds (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕) δ f⁻¹u₁ f⁻¹u₁-is-upperbound
                  where
                    f⁻¹u₁-is-upperbound : is-upperbound (underlying-order (𝓓 ×ᵈᶜᵖᵒ 𝓔 ×ᵈᶜᵖᵒ 𝓕)) f⁻¹u₁ α
                    f⁻¹u₁-is-upperbound i = (pr₁ (pr₁ (p i))) , (pr₂ (pr₁ (p i))) , (pr₂ (p i))

    to-×-DCPO : DCPO[ 𝓓 , 𝓔 ] →  DCPO[ 𝓓 , 𝓕 ] → DCPO[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ 𝓕 ]
    to-×-DCPO f g = h , c
      where
        h : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩
        h d = (underlying-function 𝓓 𝓔 f d) , (underlying-function 𝓓 𝓕 g d)
        h-is-monotone : is-monotone 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
        h-is-monotone x y p = (monotone-if-continuous 𝓓 𝓔 f x y p)
                                , (monotone-if-continuous 𝓓 𝓕 g x y p)
        c : is-continuous 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
        c I α δ = u , v
          where
            u : is-upperbound (underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕)) (h (∐ 𝓓 δ)) (λ i → h (α i))
            u i = h-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
            v : (u₁ : ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩) →
                  ((i : I) → underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕) (h (α i)) u₁) →
                  underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕) (h (∐ 𝓓 δ)) u₁
            v (u₁ , u₂) p = e₁ , e₂
              where
                e₁ : underlying-function 𝓓 𝓔 f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ u₁
                e₁ = transport (λ - → - ⊑⟨ 𝓔 ⟩ u₁) (p₁ ⁻¹) e₃
                  where
                    p₁ : underlying-function 𝓓 𝓔 f (∐ 𝓓 δ) ＝ ∐ 𝓔 (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 f) δ)
                    p₁ = continuous-∐-＝ 𝓓 𝓔 f δ
                    e₃ : ∐ 𝓔 (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 f) δ) ⊑⟨ 𝓔 ⟩ u₁
                    e₃ = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 f) δ) u₁ (λ i → pr₁ (p i))
                e₂ : underlying-function 𝓓 𝓕 g (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ u₂
                e₂ = transport (λ - → - ⊑⟨ 𝓕 ⟩ u₂) (p₁ ⁻¹) e₃
                  where
                    p₁ : underlying-function 𝓓 𝓕 g (∐ 𝓓 δ) ＝ ∐ 𝓕 (image-is-directed 𝓓 𝓕 (monotone-if-continuous 𝓓 𝓕 g) δ)
                    p₁ = continuous-∐-＝ 𝓓 𝓕 g δ
                    e₃ : ∐ 𝓕 (image-is-directed 𝓓 𝓕 (monotone-if-continuous 𝓓 𝓕 g) δ) ⊑⟨ 𝓕 ⟩ u₂
                    e₃ = ∐-is-lowerbound-of-upperbounds 𝓕 (image-is-directed 𝓓 𝓕 (monotone-if-continuous 𝓓 𝓕 g) δ) u₂ (λ i → pr₂ (p i))

  module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
          (𝓔 : DCPO⊥ {𝓣} {𝓣'})
          (𝓕 : DCPO⊥ {𝓦} {𝓦'})
        where

    ×ᵈᶜᵖᵒ⊥-assoc₁ : DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 ×ᵈᶜᵖᵒ⊥ 𝓕 , (𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔) ×ᵈᶜᵖᵒ⊥ 𝓕 ]
    ×ᵈᶜᵖᵒ⊥-assoc₁ = ×ᵈᶜᵖᵒ-assoc₁ (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻)

    to-×-DCPO⊥ : DCPO⊥[ 𝓓 , 𝓔 ] → DCPO⊥[ 𝓓 , 𝓕 ] → DCPO⊥[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ⊥ 𝓕 ]
    to-×-DCPO⊥ f g = to-×-DCPO (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻) f g

\end{code}
