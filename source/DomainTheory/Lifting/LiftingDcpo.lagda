Tom de Jong, 9 February 2022

We describe how to freely add a least element to a dcpo. This is done by lifting
the underlying set, but when ordering the lifting, we have to take the order on
the original dcpo into account.

We also show that taking the free dcpo on a set X coincides with freely adding a
least element to X when viewed as a discretely-ordered dcpo.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Lifting.LiftingDcpo
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
        (pe : propext 𝓥)
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt

open import Lifting.Lifting 𝓥 hiding (⊥)
open import Lifting.IdentityViaSIP 𝓥
open import Lifting.Miscelanea 𝓥
open import Lifting.Miscelanea-PropExt-FunExt 𝓥 pe fe
                                             renaming ( ⊑'-to-⊑ to ⊑'-to-⊑''
                                                      ; ⊑-to-⊑' to ⊑''-to-⊑')

open import Posets.Poset fe
open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥
open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe
             renaming ( 𝓛-DCPO  to 𝓛-DCPO-on-set ; 𝓛-DCPO⊥ to 𝓛-DCPO⊥-on-set)

\end{code}

We first construct the pointed dcpo.

\begin{code}

module freely-add-⊥
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

 ⊑-is-antisymmetric : (k l : 𝓛D) → k ⊑ l → l ⊑ k → k ＝ l
 ⊑-is-antisymmetric k l (f , s) (g , t) = ⋍-to-＝ γ
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
       lemma = ＝-to-⊑ 𝓓 (value-is-constant k (g (⌜ e ⌝ p)) p)

 family-in-dcpo : {I : 𝓥 ̇ } (α : I → 𝓛D) → (Σ i ꞉ I , is-defined (α i)) → ⟨ 𝓓 ⟩
 family-in-dcpo {I} α (i , p) = value (α i) p

 family-in-dcpo-is-semidirected : {I : 𝓥 ̇ } (α : I → 𝓛D)
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
        lemma = ＝-to-⊑ 𝓓 (value-is-constant (α k) (g pⱼ) (f pᵢ))

 family-in-dcpo-is-directed : {I : 𝓥 ̇ } (α : I → 𝓛D)
                            → is-directed _⊑_ α
                            → ∃ i ꞉ I , is-defined (α i)
                            → is-Directed 𝓓 (family-in-dcpo α)
 family-in-dcpo-is-directed α δ q =
  (q , family-in-dcpo-is-semidirected α (semidirected-if-directed _⊑_ α δ))

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
     ε = family-in-dcpo-is-directed α δ
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
           lemma = ＝-to-⊑ 𝓓 (value-is-constant l (pr₁ (l-is-ub i) qᵢ) (f q))

 𝓛-DCPO⊥ : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓣}
 𝓛-DCPO⊥ = (𝓛-DCPO , (𝟘 , 𝟘-elim , 𝟘-is-prop)
                   , (λ l → 𝟘-elim , 𝟘-induction))

\end{code}

Of course, the map η from the dcpo to the lifted dcpo should be Scott
continuous.

\begin{code}

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
               value l (q j) ⊑⟨ 𝓓 ⟩[ ＝-to-⊑ 𝓓 (value-is-constant l (q j) (q i)) ]
               value l (q i) ∎⟨ 𝓓 ⟩
     γ : I → η (∐ 𝓓 δ) ⊑ l
     γ i = ((λ ⋆ → q i)
          , (λ ⋆ → ∐-is-lowerbound-of-upperbounds 𝓓 δ (value l (q i)) (ub' i)))

 𝓛-order-lemma : {k l : 𝓛D} → k ⊑' l → k ⊑ l
 𝓛-order-lemma {k} {l} k-below-l = (pr₁ claim , (λ p → ＝-to-⊑ 𝓓 (pr₂ claim p)))
  where
   open import Lifting.UnivalentPrecategory 𝓥 ⟨ 𝓓 ⟩ renaming (_⊑_ to _⊑''_)
   claim : k ⊑'' l
   claim = ⊑'-to-⊑'' k-below-l

\end{code}

We now prove that the construction above freely adds a least element to the
dcpo.

\begin{code}

 module _
         (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
         (f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫)
         (f-is-continuous : is-continuous 𝓓 (𝓔 ⁻) f)
        where

  open lifting-is-free-pointed-dcpo-on-set (sethood 𝓓) 𝓔 f

  f̃-is-monotone : is-monotone 𝓛-DCPO (𝓔 ⁻) f̃
  f̃-is-monotone k l k-below-l = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (f ∘ value k)
                                 (being-defined-is-prop k) (f̃ l) lem
   where
    lem : (p : is-defined k) → f (value k p) ⊑⟪ 𝓔 ⟫ f̃ l
    lem p = f (value k p) ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
            f (value l q) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
            f̃ l           ∎⟪ 𝓔 ⟫
     where
      q : is-defined l
      q = pr₁ k-below-l p
      ⦅1⦆ = monotone-if-continuous 𝓓 (𝓔 ⁻) (f , f-is-continuous)
             (value k p) (value l q) (pr₂ k-below-l p)
      ⦅2⦆ = ∐ˢˢ-is-upperbound 𝓔 (f ∘ value l) (being-defined-is-prop l) q

  f̃-is-continuous' : is-continuous 𝓛-DCPO (𝓔 ⁻) f̃
  f̃-is-continuous' = continuity-criterion 𝓛-DCPO (𝓔 ⁻) f̃ f̃-is-monotone γ
   where
    γ : (I : 𝓥 ̇ )(α : I → ⟨ 𝓛-DCPO ⟩) (δ : is-Directed 𝓛-DCPO α)
      → f̃ (∐ 𝓛-DCPO {I} {α} δ) ⊑⟪ 𝓔 ⟫
        ∐ (𝓔 ⁻) (image-is-directed 𝓛-DCPO (𝓔 ⁻) f̃-is-monotone {I} {α} δ)
    γ I α δ = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (f ∘ value s)
               (being-defined-is-prop s) (∐ (𝓔 ⁻) ε) lem
     where
      s : ⟨ 𝓛-DCPO ⟩
      s = ∐ 𝓛-DCPO {I} {α} δ
      ε : is-Directed (𝓔 ⁻) (f̃ ∘ α)
      ε = image-is-directed 𝓛-DCPO (𝓔 ⁻) f̃-is-monotone {I} {α} δ
      lem : (q : is-defined s) → f (value s q) ⊑⟪ 𝓔 ⟫ ∐ (𝓔 ⁻) ε
      lem q = f (value s q) ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
              f (∐ 𝓓 δ')    ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
              ∐ (𝓔 ⁻) ε'    ⊑⟪ 𝓔 ⟫[ ⦅3⦆ ]
              ∐ (𝓔 ⁻) ε     ∎⟪ 𝓔 ⟫
       where
        δ' : is-Directed 𝓓 (family-in-dcpo α)
        δ' = family-in-dcpo-is-directed α δ q
        ε' : is-Directed (𝓔 ⁻) (f ∘ family-in-dcpo α)
        ε' = image-is-directed' 𝓓 (𝓔 ⁻) (f , f-is-continuous) δ'
        ⦅1⦆ = reflexivity (𝓔 ⁻) (f (∐ 𝓓 δ'))
        ⦅2⦆ = continuous-∐-⊑ 𝓓 (𝓔 ⁻) (f , f-is-continuous) δ'
        ⦅3⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) ε' (∐ (𝓔 ⁻) ε) claim
         where
          claim : ((i , p) : (Σ i ꞉ I , is-defined (α i)))
                → (f (value (α i) p)) ⊑⟪ 𝓔 ⟫ ∐ (𝓔 ⁻) ε
          claim (i , p) = (f (value (α i) p)) ⊑⟪ 𝓔 ⟫[ ⦅†⦆ ]
                          f̃ (α i)             ⊑⟪ 𝓔 ⟫[ ⦅‡⦆ ]
                          ∐ (𝓔 ⁻) ε           ∎⟪ 𝓔 ⟫
           where
            ⦅†⦆ = ∐ˢˢ-is-upperbound 𝓔 (f ∘ value (α i))
                   (being-defined-is-prop (α i)) p
            ⦅‡⦆ = ∐-is-upperbound (𝓔 ⁻) ε i

  f̃-is-strict' : is-strict 𝓛-DCPO⊥ 𝓔 f̃
  f̃-is-strict' = f̃-is-strict

  f̃-after-η-is-f' : f̃ ∘ η ∼ f
  f̃-after-η-is-f' = f̃-after-η-is-f

  𝓛-DCPOₛ : DCPO
  𝓛-DCPOₛ = 𝓛-DCPO-on-set (sethood 𝓓)

  𝓛-monotone-lemma : (g : 𝓛D → ⟪ 𝓔 ⟫)
                   → is-monotone 𝓛-DCPO  (𝓔 ⁻) g
                   → is-monotone 𝓛-DCPOₛ (𝓔 ⁻) g
  𝓛-monotone-lemma g g-mon k l k-below-l = g-mon k l (𝓛-order-lemma k-below-l)

  𝓛-directed-lemma : {I : 𝓥 ̇ } {α : I → 𝓛D}
                   → is-Directed 𝓛-DCPOₛ α
                   → is-Directed 𝓛-DCPO α
  𝓛-directed-lemma {I} {α} δ = (inhabited-if-Directed 𝓛-DCPOₛ α δ , σ)
   where
    σ : is-semidirected _⊑_ α
    σ i j = ∥∥-functor γ (semidirected-if-Directed 𝓛-DCPOₛ α δ i j)
     where
      γ : (Σ k ꞉ I , (α i ⊑' α k) × (α j ⊑' α k))
        → (Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))
      γ (k , u , v) = (k , 𝓛-order-lemma u , 𝓛-order-lemma v)

  𝓛-sup-lemma : {I : 𝓥 ̇ } {α : I → 𝓛D} (δ : is-Directed 𝓛-DCPOₛ α)
              → ∐ 𝓛-DCPOₛ δ ＝ ∐ 𝓛-DCPO {I} {α} (𝓛-directed-lemma δ)
  𝓛-sup-lemma {I} {α} δ = ⋍-to-＝ (e , dfunext fe γ)
   where
    ε : is-Directed 𝓛-DCPO α
    ε = 𝓛-directed-lemma δ
    e : is-defined (∐ 𝓛-DCPOₛ δ) ≃ is-defined (∐ 𝓛-DCPO {I} {α} ε)
    e = ≃-refl (∃ i ꞉ I , is-defined (α i))
    γ : (q : is-defined (∐ 𝓛-DCPO {I} {α} ε))
      → value (∐ 𝓛-DCPOₛ δ) q ＝ value (∐ 𝓛-DCPO {I} {α} ε) (⌜ e ⌝ q)
    γ q = ∥∥-rec (sethood 𝓓) goal q
     where
      goal : (Σ i ꞉ I , is-defined (α i))
           → value (∐ 𝓛-DCPOₛ δ) q ＝ value (∐ 𝓛-DCPO {I} {α} ε) (⌜ e ⌝ q)
      goal (i , qᵢ) = value (∐ 𝓛-DCPOₛ δ) q                ＝⟨ ⦅1⦆  ⟩
                      value (α i) qᵢ                       ＝⟨ ⦅2⦆  ⟩
                      ∐ 𝓓 ε'                               ＝⟨ refl ⟩
                      value (∐ 𝓛-DCPO {I} {α} ε) (⌜ e ⌝ q) ∎
       where
        ε' : is-Directed 𝓓 (family-in-dcpo α)
        ε' = family-in-dcpo-is-directed α ε q
        ⦅1⦆ = (＝-of-values-from-＝ (family-defined-somewhere-sup-＝
                                   (sethood 𝓓) δ i qᵢ)) ⁻¹
        ⦅2⦆ = antisymmetry 𝓓 (value (α i) qᵢ) (∐ 𝓓 ε') ⦅†⦆ ⦅‡⦆
         where
          ⦅†⦆ : value (α i) qᵢ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε'
          ⦅†⦆ = ∐-is-upperbound 𝓓 ε' (i , qᵢ)
          ⦅‡⦆ : ∐ 𝓓 ε' ⊑⟨ 𝓓 ⟩ value (α i) qᵢ
          ⦅‡⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 ε' (value (α i) qᵢ) ub
           where
            ub : ((j , qⱼ) : Σ i' ꞉ I , is-defined (α i'))
               → value (α j) qⱼ ⊑⟨ 𝓓 ⟩ value (α i) qᵢ
            ub (j , qⱼ) = ＝-to-⊑ 𝓓 (＝-of-values-from-＝ (lemma j qⱼ))
             where
              lemma : (j : I) (qⱼ : is-defined (α j)) → α j ＝ α i
              lemma j qⱼ =
               ∥∥-rec (lifting-of-set-is-set (sethood 𝓓)) claim
                      (semidirected-if-Directed 𝓛-DCPOₛ α δ i j)
               where
                claim : (Σ k ꞉ I , (α i ⊑' α k) × (α j ⊑' α k)) → α j ＝ α i
                claim (k , u , v) = v qⱼ ∙ (u qᵢ) ⁻¹

  𝓛-continuity-lemma : (g : 𝓛D → ⟪ 𝓔 ⟫)
                     → is-continuous 𝓛-DCPO  (𝓔 ⁻) g
                     → is-continuous 𝓛-DCPOₛ (𝓔 ⁻) g
  𝓛-continuity-lemma g g-cont = continuity-criterion' 𝓛-DCPOₛ (𝓔 ⁻) g g-mon lemma
   where
    g-mon : is-monotone 𝓛-DCPOₛ (𝓔 ⁻) g
    g-mon = 𝓛-monotone-lemma g (monotone-if-continuous 𝓛-DCPO (𝓔 ⁻) (g , g-cont))
    lemma : (I : 𝓥 ̇ )(α : I → 𝓛D) (δ : is-Directed 𝓛-DCPOₛ α)
          → is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                                         (g (∐ 𝓛-DCPOₛ δ)) (g ∘ α)
    lemma I α δ = transport T claim
                   (sup-is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                                                     (g-cont I α ε))
     where
      T : 𝓛D → 𝓥 ⊔ 𝓤' ⊔ 𝓣' ̇
      T - = is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻)) (g -) (g ∘ α)
      ε : is-Directed 𝓛-DCPO α
      ε = 𝓛-directed-lemma δ
      claim : ∐ 𝓛-DCPO {I} {α} ε ＝ ∐ 𝓛-DCPOₛ {I} {α} δ
      claim = (𝓛-sup-lemma δ) ⁻¹

  f̃-is-unique' : (g : 𝓛D → ⟪ 𝓔 ⟫)
               → is-continuous 𝓛-DCPO (𝓔 ⁻) g
               → is-strict 𝓛-DCPO⊥ 𝓔 g
               → g ∘ η ＝ f
               → g ∼ f̃
  f̃-is-unique' g g-cont = f̃-is-unique g g-cont'
   where
    g-cont' : is-continuous (𝓛-DCPO-on-set (sethood 𝓓)) (𝓔 ⁻) g
    g-cont' = 𝓛-continuity-lemma g g-cont

  𝓛-gives-the-free-pointed-dcpo-on-a-dcpo :
   ∃! h ꞉ (⟪ 𝓛-DCPO⊥ ⟫ → ⟪ 𝓔 ⟫) , is-continuous (𝓛-DCPO⊥ ⁻) (𝓔 ⁻) h
                                × is-strict 𝓛-DCPO⊥ 𝓔 h
                                × (h ∘ η ＝ f)
  𝓛-gives-the-free-pointed-dcpo-on-a-dcpo =
   (f̃ , f̃-is-continuous' , f̃-is-strict' , (dfunext fe f̃-after-η-is-f')) , γ
    where
     γ : is-central (Σ h ꞉ (⟪ 𝓛-DCPO⊥ ⟫ → ⟪ 𝓔 ⟫)
                         , is-continuous (𝓛-DCPO⊥ ⁻) (𝓔 ⁻) h
                         × is-strict 𝓛-DCPO⊥ 𝓔 h
                         × (h ∘ η ＝ f))
          (f̃ , f̃-is-continuous' , f̃-is-strict' , dfunext fe f̃-after-η-is-f')
     γ (g , cont , str , eq) =
      to-subtype-＝ (λ h → ×₃-is-prop
                           (being-continuous-is-prop (𝓛-DCPO⊥ ⁻) (𝓔 ⁻) h)
                           (being-strict-is-prop 𝓛-DCPO⊥ 𝓔 h)
                           (equiv-to-prop
                             (≃-funext fe (h ∘ η) f)
                             (Π-is-prop fe (λ _ → sethood (𝓔 ⁻)))))
                           ((dfunext fe (f̃-is-unique' g cont str eq)) ⁻¹)

\end{code}

Finally, we show that taking the free dcpo on a set X coincides with freely
adding a least element to X when viewed as a discretely-ordered dcpo. This also
follows abstractly from the fact that we can compose adjunctions, but we give a
direct proof.

\begin{code}

module _
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

 X̃ : DCPO {𝓤} {𝓤}
 X̃ = (X , _＝_ , pa , γ)
  where
   open PosetAxioms {𝓤} {𝓤} {X} _＝_
   pa : poset-axioms
   pa = (X-is-set
      , (λ x y → X-is-set)
      , (λ x → refl)
      , (λ x y z → _∙_)
      , (λ x y u v → u))
   γ : is-directed-complete _＝_
   γ I α δ = ∥∥-rec (having-sup-is-prop _＝_ pa α) lemma
                    (inhabited-if-directed _＝_ α δ)
    where
     α-constant : (i j : I) → α i ＝ α j
     α-constant i j = ∥∥-rec X-is-set h (semidirected-if-directed _＝_ α δ i j)
      where
       h : (Σ k ꞉ I , (α i ＝ α k) × (α j ＝ α k)) → α i ＝ α j
       h (k , p , q) = p ∙ q ⁻¹
     lemma : I → has-sup _＝_ α
     lemma i = (α i , ub , lb-of-ubs)
      where
       ub : (j : I) → α j ＝ α i
       ub j = α-constant j i
       lb-of-ubs : is-lowerbound-of-upperbounds _＝_ (α i) α
       lb-of-ubs y y-is-ub = y-is-ub i

 module _ where
  open freely-add-⊥ X̃

  𝓛-order-lemma-converse : {k l : 𝓛 X} → k ⊑ l → k ⊑' l
  𝓛-order-lemma-converse {k} {l} k-below-l = ⊑''-to-⊑' k-below-l

 open freely-add-⊥

 liftings-coincide : 𝓛-DCPO⊥ X̃ ≃ᵈᶜᵖᵒ⊥ 𝓛-DCPO⊥-on-set X-is-set
 liftings-coincide = ≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ (𝓛-DCPO⊥ X̃) 𝓛-DCPO⊥-X
                           (id , id , (λ _ → refl) , (λ _ → refl) ,
                            cont₁ , cont₂)
  where
   𝓛-DCPO⊥-X : DCPO⊥
   𝓛-DCPO⊥-X = 𝓛-DCPO⊥-on-set X-is-set
   cont₁ : is-continuous (𝓛-DCPO⊥ X̃ ⁻) (𝓛-DCPO⊥-X ⁻) id
   cont₁ I α δ = (ub , lb-of-ubs)
    where
     ub : (i : I) → α i ⊑' ∐ (𝓛-DCPO⊥ X̃ ⁻) {I} {α} δ
     ub i = (𝓛-order-lemma-converse (∐-is-upperbound (𝓛-DCPO⊥ X̃ ⁻) {I} {α} δ i))
     lb-of-ubs : is-lowerbound-of-upperbounds _⊑'_ (∐ (𝓛-DCPO⊥ X̃ ⁻) {I} {α} δ) α
     lb-of-ubs l l-is-ub = 𝓛-order-lemma-converse
                            (∐-is-lowerbound-of-upperbounds (𝓛-DCPO⊥ X̃ ⁻) {I} {α}
                            δ l
                            (λ i → 𝓛-order-lemma X̃ (l-is-ub i)))
   cont₂ : is-continuous (𝓛-DCPO⊥-X ⁻) (𝓛-DCPO⊥ X̃ ⁻) id
   cont₂ = 𝓛-continuity-lemma X̃ (𝓛-DCPO⊥ X̃) η (η-is-continuous X̃)
            id (id-is-continuous (𝓛-DCPO⊥ X̃ ⁻))

\end{code}
