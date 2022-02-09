Tom de Jong, 9 February 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoLiftingGeneralized
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
        (pe : propext 𝓥)
       where

open PropositionalTruncation pt

open import UF-Equiv

open import UF-Miscelanea
open import UF-Subsingletons-FunExt

open import UF-ImageAndSurjection
open ImageAndSurjection pt

open import Lifting 𝓥 hiding (⊥)
open import LiftingIdentityViaSIP 𝓥
open import LiftingMiscelanea 𝓥
open import LiftingMiscelanea-PropExt-FunExt 𝓥 pe fe
-- open import LiftingMonad 𝓥

open import Dcpo pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoLifting pt fe 𝓥 pe renaming (𝓛-DCPO to 𝓛-DCPO-from-set
                                            ; 𝓛-DCPO⊥ to 𝓛-DCPO⊥-from-set)

open import Poset fe

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 𝓛D : 𝓥 ⁺ ⊔ 𝓤 ̇
 𝓛D = 𝓛 ⟨ 𝓓 ⟩

 _⊑_ : 𝓛D → 𝓛D → 𝓥 ⊔ 𝓣 ̇
 (P , φ , _) ⊑ (Q , ψ , _) = Σ f ꞉ (P → Q) , ((p : P) → φ p ⊑⟨ 𝓓 ⟩ ψ (f p))

 ⊑-is-prop-valued : (k l : 𝓛D) → is-prop (k ⊑ l)
 ⊑-is-prop-valued k l =
  Σ-is-prop (Π-is-prop fe (λ p → being-defined-is-prop l))
            (λ f → Π-is-prop fe (λ p → prop-valuedness 𝓓
                                        (value k p) (value l (f p))))

 ⊑-is-reflexive : (l : 𝓛D) → l ⊑ l
 ⊑-is-reflexive l = (id , (λ p → reflexivity 𝓓 (value l p)))

 ⊑-is-transitive : (k l m : 𝓛D) → k ⊑ l → l ⊑ m → k ⊑ m
 ⊑-is-transitive k l m (f , s) (g , t) = (g ∘ f , γ)
  where
   γ : (p : is-defined k) → value k p ⊑⟨ 𝓓 ⟩ value m (g (f p))
   γ p = value k p         ⊑⟨ 𝓓 ⟩[ s p     ]
         value l (f p)     ⊑⟨ 𝓓 ⟩[ t (f p) ]
         value m (g (f p)) ∎⟨ 𝓓 ⟩

 ⊑-is-antisymmetric : (k l : 𝓛D) → k ⊑ l → l ⊑ k → k ≡ l
 ⊑-is-antisymmetric k l (f , s) (g , t) = ⋍-to-≡ γ
  where
   γ : k ⋍ l
   γ = (e , dfunext fe (λ p → antisymmetry 𝓓 (value k p) (value l (⌜ e ⌝ p))
                               (s p) (h p)))
    where
     e : is-defined k ≃ is-defined l
     e = logically-equivalent-props-are-equivalent (being-defined-is-prop k)
                                                   (being-defined-is-prop l) f g
     h : (p : is-defined k) → value l (⌜ e ⌝ p) ⊑⟨ 𝓓 ⟩ value k p
     h p = value l (⌜ e ⌝ p)     ⊑⟨ 𝓓 ⟩[ t (⌜ e ⌝ p) ]
           value k (g (⌜ e ⌝ p)) ⊑⟨ 𝓓 ⟩[ lemma       ]
           value k p             ∎⟨ 𝓓 ⟩
      where
       lemma = ≡-to-⊑ 𝓓 (value-is-constant k (g (⌜ e ⌝ p)) p)

 family-in-dcpo : {I : 𝓥 ̇  } (α : I → 𝓛D) → (Σ i ꞉ I , is-defined (α i)) → ⟨ 𝓓 ⟩
 family-in-dcpo {I} α (i , p) = value (α i) p

 family-in-dcpo-is-semidirected : {I : 𝓥 ̇  } (α : I → 𝓛D)
                                → is-semidirected _⊑_ α
                                → is-semidirected (underlying-order 𝓓)
                                   (family-in-dcpo α)
 family-in-dcpo-is-semidirected {I} α α-semidir (i , pᵢ) (j , pⱼ) =
  ∥∥-functor γ (α-semidir i j)
   where
    γ : (Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))
      → (Σ q ꞉ domain (family-in-dcpo α) ,
               value (α i) pᵢ ⊑⟨ 𝓓 ⟩ value (α (pr₁ q)) (pr₂ q)
             × value (α j) pⱼ ⊑⟨ 𝓓 ⟩ value (α (pr₁ q)) (pr₂ q))
    γ (k , (f , s) , (g , t)) = ((k , f pᵢ) , (s pᵢ) , τ)
     where
      τ = value (α j) pⱼ     ⊑⟨ 𝓓 ⟩[ t pⱼ  ]
          value (α k) (g pⱼ) ⊑⟨ 𝓓 ⟩[ lemma ]
          value (α k) (f pᵢ) ∎⟨ 𝓓 ⟩
       where
        lemma = ≡-to-⊑ 𝓓 (value-is-constant (α k) (g pⱼ) (f pᵢ))

 𝓛-DCPO : DCPO {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓣}
 𝓛-DCPO = (𝓛D , _⊑_ , (lifting-of-set-is-set (sethood 𝓓)
                    , ⊑-is-prop-valued
                    , ⊑-is-reflexive
                    , ⊑-is-transitive
                    , ⊑-is-antisymmetric) ,
                    γ)
  where
   γ : is-directed-complete _⊑_
   γ I α δ = (s , s-is-ub , s-is-lb-of-ubs)
    where
     J : 𝓥 ̇
     J = Σ i ꞉ I , is-defined (α i)
     β : J → ⟨ 𝓓 ⟩
     β = family-in-dcpo α
     ε : ∥ J ∥ → is-Directed 𝓓 β
     ε q = (q , family-in-dcpo-is-semidirected α
                 (semidirected-if-directed _⊑_ α δ))
     s : 𝓛D
     s = ∥ J ∥ , t
      where
       t : (∥ J ∥ → ⟨ 𝓓 ⟩) × is-prop ∥ J ∥
       t = (λ q → ∐ 𝓓 (ε q)) , ∥∥-is-prop
     s-is-ub : (i : I) → α i ⊑ s
     s-is-ub i = (f , (λ qᵢ → ∐-is-upperbound 𝓓 (ε (f qᵢ)) (i , qᵢ)))
      where
       f : is-defined (α i) → ∥ J ∥
       f qᵢ = ∣ i , qᵢ ∣
     s-is-lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ s α
     s-is-lb-of-ubs l l-is-ub = (f , r)
      where
       f : ∥ J ∥ → is-defined l
       f = ∥∥-rec (being-defined-is-prop l) (λ (i , qᵢ) → pr₁ (l-is-ub i) qᵢ)
       r : (q : ∥ J ∥) → ∐ 𝓓 (ε q) ⊑⟨ 𝓓 ⟩ value l (f q)
       r q = ∐-is-lowerbound-of-upperbounds 𝓓 (ε q) (value l (f q)) ub
        where
         ub : (j : J) → β j ⊑⟨ 𝓓 ⟩ value l (f q)
         ub (i , qᵢ) = value (α i) qᵢ               ⊑⟨ 𝓓 ⟩[ pr₂ (l-is-ub i) qᵢ ]
                       value l (pr₁ (l-is-ub i) qᵢ) ⊑⟨ 𝓓 ⟩[ lemma              ]
                       value l (f q)                ∎⟨ 𝓓 ⟩
          where
           lemma = ≡-to-⊑ 𝓓 (value-is-constant l (pr₁ (l-is-ub i) qᵢ) (f q))

 𝓛-DCPO⊥ : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓣}
 𝓛-DCPO⊥ = (𝓛-DCPO , (𝟘 , 𝟘-elim , 𝟘-is-prop)
                   , (λ l → 𝟘-elim , 𝟘-induction))

 η-is-continuous : is-continuous 𝓓 𝓛-DCPO η
 η-is-continuous I α δ = (ub , lb-of-ubs)
  where
   ub : (i : I) → η (α i) ⊑ η (∐ 𝓓 δ)
   ub i = ((λ ⋆ → ⋆) , (λ ⋆ → ∐-is-upperbound 𝓓 δ i))
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓛-DCPO) (η (∐ 𝓓 δ))
                (η ∘ α)
   lb-of-ubs l l-is-ub = ∥∥-rec (prop-valuedness 𝓛-DCPO (η (∐ 𝓓 δ)) l)
                                γ
                                (inhabited-if-Directed 𝓓 α δ)
    where
     q : (i : I) → is-defined l
     q i = pr₁ (l-is-ub i) ⋆
     ub' : (i j : I) → α j ⊑⟨ 𝓓 ⟩ value l (q i)
     ub' i j = α j           ⊑⟨ 𝓓 ⟩[ pr₂ (l-is-ub j) ⋆ ]
               value l (q j) ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (value-is-constant l (q j) (q i)) ]
               value l (q i) ∎⟨ 𝓓 ⟩
     γ : I → η (∐ 𝓓 δ) ⊑ l
     γ i = ((λ ⋆ → q i)
          , (λ ⋆ → ∐-is-lowerbound-of-upperbounds 𝓓 δ (value l (q i)) (ub' i)))

 module _
         (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
         (f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫)
         (f-is-continuous : is-continuous 𝓓 (𝓔 ⁻) f)
        where

  open lifting-is-free-dcpo-on-set (sethood 𝓓) 𝓔 f

  f̃-is-continuous' : is-continuous 𝓛-DCPO (𝓔 ⁻) f̃
  f̃-is-continuous' = {!!}

  f̃-is-strict' : is-strict 𝓛-DCPO⊥ 𝓔 f̃
  f̃-is-strict' = f̃-is-strict

  f̃-after-η-is-f' : f̃ ∘ η ∼ f
  f̃-after-η-is-f' = f̃-after-η-is-f

  f̃-is-unique' : (g : 𝓛D → ⟪ 𝓔 ⟫)
               → is-continuous 𝓛-DCPO (𝓔 ⁻) g
               → is-strict 𝓛-DCPO⊥ 𝓔 g
               → g ∘ η ≡ f
               → g ∼ f̃
  f̃-is-unique' g g-cont = f̃-is-unique g g-cont'
   where
    g-cont' : is-continuous (𝓛-DCPO-from-set (sethood 𝓓)) (𝓔 ⁻) g
    g-cont' = {!!}


{-
 𝓛-gives-the-free-pointed-dcpo-on-a-set :
  ∃! h ꞉ (⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫) , is-continuous (𝓛X ⁻) (𝓓 ⁻) h
                          × is-strict 𝓛X 𝓓 h
                          × (h ∘ η ≡ f)
 𝓛-gives-the-free-pointed-dcpo-on-a-set =
  (f̃ , f̃-is-continuous , f̃-is-strict , (dfunext fe f̃-after-η-is-f)) , γ
   where
    γ : is-central (Σ h ꞉ (⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫) , is-continuous (𝓛X ⁻) (𝓓 ⁻) h
                                           × is-strict 𝓛X 𝓓 h
                                           × (h ∘ η ≡ f))
         (f̃ , f̃-is-continuous , f̃-is-strict , dfunext fe f̃-after-η-is-f)
    γ (g , cont , str , eq) =
     to-subtype-≡ (λ h → ×₃-is-prop (being-continuous-is-prop (𝓛X ⁻) (𝓓 ⁻) h)
                                    (being-strict-is-prop 𝓛X 𝓓 h)
                                    (equiv-to-prop
                                      (≃-funext fe (h ∘ η) f)
                                      (Π-is-prop fe (λ _ → sethood (𝓓 ⁻)))))
                                    ((dfunext fe (f̃-is-unique g cont str eq)) ⁻¹)
-}

module _
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

 X̃ : DCPO {𝓤} {𝓤}
 X̃ = (X , _≡_ , pa , γ)
  where
   open PosetAxioms {𝓤} {𝓤} {X} _≡_
   pa : poset-axioms
   pa = (X-is-set
      , (λ x y → X-is-set)
      , (λ x → refl)
      , (λ x y z → _∙_)
      , (λ x y u v → u))
   γ : is-directed-complete _≡_
   γ I α δ = ∥∥-rec (having-sup-is-prop _≡_ pa α) lemma
                    (inhabited-if-directed _≡_ α δ)
    where
     α-constant : (i j : I) → α i ≡ α j
     α-constant i j = ∥∥-rec X-is-set h (semidirected-if-directed _≡_ α δ i j)
      where
       h : (Σ k ꞉ I , (α i ≡ α k) × (α j ≡ α k)) → α i ≡ α j
       h (k , p , q) = p ∙ q ⁻¹
     lemma : I → has-sup _≡_ α
     lemma i = (α i , ub , lb-of-ubs)
      where
       ub : (j : I) → α j ≡ α i
       ub j = α-constant j i
       lb-of-ubs : is-lowerbound-of-upperbounds _≡_ (α i) α
       lb-of-ubs y y-is-ub = y-is-ub i

 𝓛X̃-≃-𝓛X : 𝓛-DCPO⊥ X̃ ≃ᵈᶜᵖᵒ⊥ 𝓛-DCPO⊥-from-set X-is-set
 𝓛X̃-≃-𝓛X = ≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ (𝓛-DCPO⊥ X̃) (𝓛-DCPO⊥-from-set X-is-set)
                           (id , id , (λ _ → refl) , (λ _ → refl) , {!!} , {!!})

\end{code}
