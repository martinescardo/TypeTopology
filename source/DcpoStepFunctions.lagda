Tom de Jong, 22 & 23 February 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

open import UF-Subsingletons

module DcpoStepFunctions
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥
open import DcpoBases pt pe fe 𝓥
open import DcpoContinuous pt fe 𝓥
open import DcpoExponential pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 is-bounded : {I : 𝓦 ̇  } (α : I → ⟨ 𝓓 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 is-bounded {𝓦} {I} α = ∃ x ꞉ ⟨ 𝓓 ⟩ , is-upperbound (underlying-order 𝓓) x α

 record is-bounded-complete : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ⋁ : {I : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} → is-bounded α → ⟨ 𝓓 ⟩
   ⋁-is-sup : {I : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} (b : is-bounded α)
            → is-sup (underlying-order 𝓓) (⋁ b) α

  ⋁-is-upperbound : {I : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} (b : is-bounded α)
                  → is-upperbound (underlying-order 𝓓) (⋁ b) α
  ⋁-is-upperbound b = sup-is-upperbound (underlying-order 𝓓) (⋁-is-sup b)

  ⋁-is-lowerbound-of-upperbounds : {I : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} (b : is-bounded α)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (⋁ b) α
  ⋁-is-lowerbound-of-upperbounds b =
   sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (⋁-is-sup b)

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {I : 𝓦 ̇  } {J : 𝓦' ̇  }
        (ρ : I ≃ J)
        (α : I → ⟨ 𝓓 ⟩)
       where

 reindexed-family-is-bounded : is-bounded 𝓓 α
                             → is-bounded 𝓓 (reindexed-family 𝓓 ρ α)
 reindexed-family-is-bounded = ∥∥-functor γ
  where
   γ : (Σ x ꞉ ⟨ 𝓓 ⟩ , is-upperbound (underlying-order 𝓓) x α)
     → (Σ x ꞉ ⟨ 𝓓 ⟩ , is-upperbound (underlying-order 𝓓) x
                       (reindexed-family 𝓓 ρ α))
   γ (x , x-is-ub) = (x , (λ j → x-is-ub (⌜ ρ ⌝⁻¹ j)))

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (𝓔-bounded-complete : is-bounded-complete 𝓔)
       where

 open is-bounded-complete 𝓔-bounded-complete

 pointwise-family-is-bounded : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                               (b : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) α)
                               (x : ⟨ 𝓓 ⟩)
                             → is-bounded 𝓔 (pointwise-family 𝓓 𝓔 α x)
 pointwise-family-is-bounded α b x = ∥∥-functor γ b
  where
   γ : (Σ f ꞉ DCPO[ 𝓓 , 𝓔 ] , is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)) f α)
     → (Σ y ꞉ ⟨ 𝓔 ⟩ , is-upperbound (underlying-order 𝓔) y
                       (pointwise-family 𝓓 𝓔 α x))
   γ ((f , _) , f-is-ub) = (f x , (λ i → f-is-ub i x))

 bounded-continuous-functions-sup : {I : 𝓥 ̇  } (α : I → DCPO[ 𝓓 , 𝓔 ])
                                  → is-bounded (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) α
                                  → DCPO[ 𝓓 , 𝓔 ]
 bounded-continuous-functions-sup {I} α b = (f , c)
  where
   f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   f x = ⋁ (pointwise-family-is-bounded α b x)
   c : is-continuous 𝓓 𝓔 f
   c J β δ = (ub , lb-of-ubs)
    where
     ub : is-upperbound (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ β)
     ub i = ⋁-is-lowerbound-of-upperbounds
             (pointwise-family-is-bounded α b (β i)) (f (∐ 𝓓 δ)) γ
      where
       γ : is-upperbound (underlying-order 𝓔) (f (∐ 𝓓 δ))
            (pointwise-family 𝓓 𝓔 α (β i))
       γ j = [ 𝓓 , 𝓔 ]⟨ α j ⟩ (β i)   ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
             [ 𝓓 , 𝓔 ]⟨ α j ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
             f (∐ 𝓓 δ)                 ∎⟨ 𝓔 ⟩
        where
         ⦅1⦆ = monotone-if-continuous 𝓓 𝓔 (α j) (β i) (∐ 𝓓 δ)
               (∐-is-upperbound 𝓓 δ i)
         ⦅2⦆ = ⋁-is-upperbound (pointwise-family-is-bounded α b (∐ 𝓓 δ)) j
     lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓔) (f (∐ 𝓓 δ))
                  (f ∘ β)
     lb-of-ubs y y-is-ub =
      ⋁-is-lowerbound-of-upperbounds (pointwise-family-is-bounded α b (∐ 𝓓 δ))
       y γ
        where
         γ : is-upperbound (underlying-order 𝓔) y
              (pointwise-family 𝓓 𝓔 α (∐ 𝓓 δ))
         γ i = [ 𝓓 , 𝓔 ]⟨ α i ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
               ∐ 𝓔 ε                    ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
               y                        ∎⟨ 𝓔 ⟩
          where
           ε : is-Directed 𝓔 ([ 𝓓 , 𝓔 ]⟨ α i ⟩ ∘ β)
           ε = image-is-directed' 𝓓 𝓔 (α i) δ
           ⦅1⦆ = continuous-∐-⊑ 𝓓 𝓔 (α i) δ
           ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓔 ε y h
            where
             h : is-upperbound (underlying-order 𝓔) y ([ 𝓓 , 𝓔 ]⟨ α i ⟩ ∘ β)
             h j = [ 𝓓 , 𝓔 ]⟨ α i ⟩ (β j) ⊑⟨ 𝓔 ⟩[ ⦅†⦆ ]
                   f (β j)                 ⊑⟨ 𝓔 ⟩[ y-is-ub j ]
                   y                       ∎⟨ 𝓔 ⟩
              where
               ⦅†⦆ = ⋁-is-upperbound (pointwise-family-is-bounded α b (β j)) i

 exponential-is-bounded-complete : is-bounded-complete (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
 exponential-is-bounded-complete = record {
     ⋁        = λ {I} {α} → bounded-continuous-functions-sup α
   ; ⋁-is-sup = λ {I} {α} → lem α
  }
   where
    lem : {I : 𝓥 ̇  } (α : I → DCPO[ 𝓓 , 𝓔 ])
        → (b : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) α)
        → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
           (bounded-continuous-functions-sup α b) α
    lem {I} α b = (ub , lb-of-ubs)
     where
      ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
            (bounded-continuous-functions-sup α b) α
      ub i x = ⋁-is-upperbound (pointwise-family-is-bounded α b x) i
      lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
                   (bounded-continuous-functions-sup α b) α
      lb-of-ubs g g-is-ub x =
       ⋁-is-lowerbound-of-upperbounds (pointwise-family-is-bounded α b x)
                                      ([ 𝓓 , 𝓔 ]⟨ g ⟩ x) (λ i → g-is-ub i x)

module _
        (𝓓 : DCPO {𝓤}  {𝓣})
        (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
        (𝓓-is-locally-small : is-locally-small 𝓓)
       where

 -- TODO: Factor this out somehow
 {- - - - - - - - - - - - - - - - -}
 _⊑ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
 _⊑ₛ_ = pr₁ 𝓓-is-locally-small

 ⊑ₛ-≃-⊑ : {x y : ⟨ 𝓓 ⟩} → x ⊑ₛ y ≃ x ⊑⟨ 𝓓 ⟩ y
 ⊑ₛ-≃-⊑ {x} {y} = pr₂ 𝓓-is-locally-small x y

 ⊑ₛ-is-prop-valued : (x y : ⟨ 𝓓 ⟩) → is-prop (x ⊑ₛ y)
 ⊑ₛ-is-prop-valued x y = equiv-to-prop ⊑ₛ-≃-⊑ (prop-valuedness 𝓓 x y)

 ⦅_⇒_⦆ : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫ → ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
 ⦅ d ⇒ e ⦆ x = ∐ˢˢ 𝓔 α (⊑ₛ-is-prop-valued d x)
  where
   α : d ⊑ₛ x → ⟪ 𝓔 ⟫
   α _ = e

 transitivityₛ : (x : ⟨ 𝓓 ⟩) {y z : ⟨ 𝓓 ⟩}
               → x ⊑ₛ y → y ⊑ₛ z → x ⊑ₛ z
 transitivityₛ x {y} {z} u v = ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹
                                (transitivity 𝓓 x y z
                                              (⌜ ⊑ₛ-≃-⊑ ⌝ u)
                                              (⌜ ⊑ₛ-≃-⊑ ⌝ v))

 syntax transitivityₛ x u v = x ⊑ₛ[ u ] v
 infixr 0 transitivityₛ

 reflexivityₛ : (x : ⟨ 𝓓 ⟩) → x ⊑ₛ x
 reflexivityₛ x = ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 x)

 syntax reflexivityₛ x = x ∎ₛ
 infix 1 reflexivityₛ
 {- - - - - - - - - - - - - - - - -}

 -- TODO: Rename to "single-step"?
 step-function-index : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ →  𝓥 ̇
 step-function-index d x = d ⊑ₛ x

 step-function-index-is-prop : {d x : ⟨ 𝓓 ⟩} → is-prop (step-function-index d x)
 step-function-index-is-prop {d} {x} = ⊑ₛ-is-prop-valued d x

 step-function-family : (d x : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
                      → step-function-index d x → ⟪ 𝓔 ⟫
 step-function-family d x e _ = e

 single-step-function-is-continuous : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
                                    → is-compact 𝓓 d
                                    → is-continuous 𝓓 (𝓔 ⁻) ⦅ d ⇒ e ⦆
 single-step-function-is-continuous d e d-is-compact I α δ = (ub , lb-of-ubs)
  where
   ub : (i : I) → ⦅ d ⇒ e ⦆ (α i) ⊑⟪ 𝓔 ⟫ ⦅ d ⇒ e ⦆ (∐ 𝓓 δ)
   ub i = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
           step-function-index-is-prop (⦅ d ⇒ e ⦆ (∐ 𝓓 δ))
           (λ p → ∐ˢˢ-is-upperbound 𝓔 (λ _ → e) step-function-index-is-prop
                  (d     ⊑ₛ[ p ]
                   α i   ⊑ₛ[ ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (∐-is-upperbound 𝓓 δ i) ]
                   ∐ 𝓓 δ ∎ₛ))
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                (⦅ d ⇒ e ⦆ (∐ 𝓓 δ)) (⦅ d ⇒ e ⦆ ∘ α)
   lb-of-ubs y y-is-ub = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
                          step-function-index-is-prop y γ
    where
     γ : (p : d ⊑ₛ ∐ 𝓓 δ) → e ⊑⟪ 𝓔 ⟫ y
     γ p = ∥∥-rec (prop-valuedness (𝓔 ⁻) e y)
            lemma (d-is-compact I α δ (⌜ ⊑ₛ-≃-⊑ ⌝ p))
      where
       lemma : (Σ i ꞉ I , d ⊑⟨ 𝓓 ⟩ α i)
             → e ⊑⟪ 𝓔 ⟫ y
       lemma (i , u) = e               ⊑⟪ 𝓔 ⟫[ v ]
                       ⦅ d ⇒ e ⦆ (α i) ⊑⟪ 𝓔 ⟫[ y-is-ub i ]
                       y               ∎⟪ 𝓔 ⟫
        where
         v = ∐ˢˢ-is-upperbound 𝓔 (λ _ → e) step-function-index-is-prop
              (⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ u)

 ⦅_⇒_⦆[_] : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
          → is-compact 𝓓 d
          → DCPO[ 𝓓 , 𝓔 ⁻ ]
 ⦅_⇒_⦆[_] d e d-is-compact =
  (⦅ d ⇒ e ⦆ , single-step-function-is-continuous d e d-is-compact)

 -- TODO: Separate the implications?
 -- TODO: Write out ⊑ so as to drop the compactness assumption?
 below-single-step-function-criterion : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫) (κ : is-compact 𝓓 d)
                                        (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
                                      → ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
                                      ⇔ e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d
 below-single-step-function-criterion d e κ f = ⦅1⦆ , ⦅2⦆
  where
   ⦅1⦆ : ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
       → e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d
   ⦅1⦆ u = e                  ⊑⟪ 𝓔 ⟫[ v ]
           ⦅ d ⇒ e ⦆ d        ⊑⟪ 𝓔 ⟫[ u d ]
           [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d ∎⟪ 𝓔 ⟫
    where
     v = ∐ˢˢ-is-upperbound 𝓔 (λ _ → e) step-function-index-is-prop
          (⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 d))
   ⦅2⦆ : e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d
      → ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
   ⦅2⦆ u x = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
              step-function-index-is-prop
              ([ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ x) γ
    where
     γ : (p : d ⊑ₛ x) → e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ x
     γ p = e                  ⊑⟪ 𝓔 ⟫[ u ]
           [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d ⊑⟪ 𝓔 ⟫[ v ]
           [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ x ∎⟪ 𝓔 ⟫
      where
       v = monotone-if-continuous 𝓓 (𝓔 ⁻) f d x (⌜ ⊑ₛ-≃-⊑ ⌝ p)

 single-step-function-is-compact : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
                                   (κ : is-compact 𝓓 d)
                                 → is-compact (𝓔 ⁻) e
                                 → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) ⦅ d ⇒ e ⦆[ κ ]
 single-step-function-is-compact d e κ e-is-compact I g δ e-below-∐g =
  ∥∥-functor lemma
             (e-is-compact I (pointwise-family 𝓓 (𝓔 ⁻) g d)
                           (pointwise-family-is-directed 𝓓 (𝓔 ⁻) g δ d) claim)
   where
    claim : e ⊑⟪ 𝓔 ⟫ ∐ (𝓔 ⁻) (pointwise-family-is-directed 𝓓 (𝓔 ⁻) g δ d)
    claim = lr-implication
             (below-single-step-function-criterion
               d e κ (∐ (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) {I} {g} δ))
             e-below-∐g
    lemma : (Σ i ꞉ I , e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ g i ⟩ d)
          → (Σ i ꞉ I , ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ g i)
    lemma (i , u) = (i , v)
     where
      v : ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ g i
      v = rl-implication
           (below-single-step-function-criterion d e κ (g i)) u


 module _
         (Bᴰ Bᴱ : 𝓥 ̇  )
         (βᴰ : Bᴰ → ⟨ 𝓓 ⟩)
         (βᴱ : Bᴱ → ⟪ 𝓔 ⟫)
         (κᴰ : is-small-compact-basis 𝓓     βᴰ)
         (κᴱ : is-small-compact-basis (𝓔 ⁻) βᴱ)
        where

  open is-small-compact-basis κᴱ

  single-step-functions-below-function : (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
                                       → 𝓥 ̇
  single-step-functions-below-function f =
   Σ d ꞉ Bᴰ , Σ e ꞉ Bᴱ , e ⊑ᴮₛ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ (βᴰ d)

  single-step-functions-below-function-family :
     (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
   → single-step-functions-below-function f → DCPO[ 𝓓 , 𝓔 ⁻ ]
  single-step-functions-below-function-family f (d , e , _) =
   ⦅ βᴰ d ⇒ βᴱ e ⦆[ is-small-compact-basis.basis-is-compact κᴰ d ]

  sup-of-single-step-functions :
     (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
   → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
            (single-step-functions-below-function-family f)
  sup-of-single-step-functions 𝕗@(f , _) = (ub , lb-of-ubs)
   where
    ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
          (single-step-functions-below-function-family 𝕗)
    ub (d , e , u) =
     rl-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                      (is-small-compact-basis.basis-is-compact κᴰ d) 𝕗)
                      (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)

    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
                 (single-step-functions-below-function-family 𝕗)
    lb-of-ubs 𝕘@(g , _) g-is-ub x = goal
     where
      claim₁ : (d : Bᴰ) (e : Bᴱ) → e ⊑ᴮₛ f (βᴰ d) → βᴱ e ⊑⟪ 𝓔 ⟫ g (βᴰ d)
      claim₁ d e u =
       lr-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                        (is-small-compact-basis.basis-is-compact κᴰ d) 𝕘)
                        (g-is-ub (d , e , u))
      claim₂ : (d : Bᴰ) → f (βᴰ d) ⊑⟪ 𝓔 ⟫ g (βᴰ d)
      claim₂ d = f (βᴰ d)                             ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
                 ∐ (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d))) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
                 g (βᴰ d)                             ∎⟪ 𝓔 ⟫
       where
        ⦅1⦆ = ↓ᴮₛ-∐-⊒ (f (βᴰ d))
        ⦅2⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d)))
               (g (βᴰ d)) (λ (e , v) → claim₁ d e v)

      δ : is-Directed 𝓓 (is-small-compact-basis.↓ιₛ κᴰ x)
      δ = is-small-compact-basis.↓ᴮₛ-is-directed κᴰ x
      ε : is-Directed (𝓔 ⁻) (f ∘ is-small-compact-basis.↓ιₛ κᴰ x)
      ε = image-is-directed' 𝓓 (𝓔 ⁻) 𝕗 δ
      goal : f x ⊑⟪ 𝓔 ⟫ g x
      goal = f x       ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
             f (∐ 𝓓 δ) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
             ∐ (𝓔 ⁻) ε ⊑⟪ 𝓔 ⟫[ ⦅3⦆ ]
             g x       ∎⟪ 𝓔 ⟫
       where
        ⦅1⦆ = ≡-to-⊒ (𝓔 ⁻) (ap f (is-small-compact-basis.↓ᴮₛ-∐-≡ κᴰ x))
        ⦅2⦆ = continuous-∐-⊑ 𝓓 (𝓔 ⁻) 𝕗 δ
        ⦅3⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) ε (g x) γ
         where
          γ : is-upperbound (underlying-order (𝓔 ⁻)) (g x)
               (f ∘ is-small-compact-basis.↓ιₛ κᴰ x)
          γ (d , u) = f (βᴰ d) ⊑⟪ 𝓔 ⟫[ claim₂ d ]
                      g (βᴰ d) ⊑⟪ 𝓔 ⟫[ v        ]
                      g x      ∎⟪ 𝓔 ⟫
           where
            v = monotone-if-continuous 𝓓 (𝓔 ⁻) 𝕘 (βᴰ d) x
                 (⌜ is-small-compact-basis.⊑ᴮₛ-≃-⊑ᴮ κᴰ ⌝ u)

  open import Fin
  open import SpartanMLTT-List hiding (⟨_⟩)

  list-of-single-step-functions-bounded-by : (l : List (Bᴰ × Bᴱ)) (e : Bᴱ)
                                           → 𝓥 ̇
  list-of-single-step-functions-bounded-by l e =
   (i : Fin (length l)) → e̅ i ⊑ᴮₛ βᴱ e
    where
     e̅ : Fin (length l) → Bᴱ
     e̅ i = pr₂ (pr₂ l !! i)

  list-of-single-step-functions-is-bounded : (l : List (Bᴰ × Bᴱ)) → 𝓥 ̇
  list-of-single-step-functions-is-bounded l =
   ∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e

  B : 𝓥 ̇
  B = Σ l ꞉ List (Bᴰ × Bᴱ) , ∃ e ꞉ Bᴱ
                           , list-of-single-step-functions-bounded-by l e

  module _
          (𝓔-bounded-complete : is-bounded-complete (𝓔 ⁻))
         where

   open is-bounded-complete (exponential-is-bounded-complete 𝓓 (𝓔 ⁻)
                              𝓔-bounded-complete)

   module _
           (l : List (Bᴰ × Bᴱ))
          where
    private
     n : ℕ
     n = length l

    d̅ : Fin n → Bᴰ
    d̅ i = pr₁ (pr₂ l !! i)

    e̅ : Fin n → Bᴱ
    e̅ i = pr₂ (pr₂ l !! i)

    d̅s-are-compact : (i : Fin n) → is-compact 𝓓 (βᴰ (d̅ i))
    d̅s-are-compact i = is-small-compact-basis.basis-is-compact κᴰ (d̅ i)

    list-of-single-step-functions-family : Fin n → DCPO[ 𝓓 , 𝓔 ⁻ ]
    list-of-single-step-functions-family i =
     ⦅ βᴰ (d̅ i) ⇒ βᴱ (e̅ i) ⦆[ d̅s-are-compact i ]

    list-of-single-step-functions-family-is-bounded :
       list-of-single-step-functions-is-bounded l
     → is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) list-of-single-step-functions-family
    list-of-single-step-functions-family-is-bounded = ∥∥-functor γ
     where
       α : Fin n → DCPO[ 𝓓 , 𝓔 ⁻ ]
       α = list-of-single-step-functions-family
       γ : (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e)
         → (Σ f ꞉ DCPO[ 𝓓 , 𝓔 ⁻ ] , is-upperbound (_hom-⊑_ 𝓓 (𝓔 ⁻)) f α)
       γ (e , e-bounded) = ((f , f-is-continuous) , f-is-ub-of-α')
        where
         f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
         f _ = βᴱ e
         f-is-continuous : is-continuous 𝓓 (𝓔 ⁻) f
         f-is-continuous = constant-functions-are-continuous 𝓓 (𝓔 ⁻)
         f-is-ub-of-α' : (i : domain α) (x : ⟨ 𝓓 ⟩)
                       → [ 𝓓 , 𝓔 ⁻ ]⟨ α i ⟩ x ⊑⟪ 𝓔 ⟫ f x
         f-is-ub-of-α' i =
          rl-implication (below-single-step-function-criterion
                           (βᴰ (d̅ i)) (βᴱ (e̅ i))
                           (d̅s-are-compact i)
                           (f , f-is-continuous)) h
          where
           h : βᴱ (e̅ i) ⊑⟪ 𝓔 ⟫ βᴱ e
           h = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ (e-bounded i)

    open import UF-UniverseEmbedding

    list-of-single-step-functions-small-family : Lift 𝓥 (Fin n) → DCPO[ 𝓓 , 𝓔 ⁻ ]
    list-of-single-step-functions-small-family =
     reindexed-family (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (≃-Lift 𝓥 (Fin n))
                      list-of-single-step-functions-family

    list-of-single-step-functions-small-family-is-bounded :
       list-of-single-step-functions-is-bounded l
     → is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) list-of-single-step-functions-small-family
    list-of-single-step-functions-small-family-is-bounded b =
     reindexed-family-is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (≃-Lift 𝓥 (Fin n))
      list-of-single-step-functions-family
      (list-of-single-step-functions-family-is-bounded b)


   β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
   β (l , b) = ⋁ {_} {list-of-single-step-functions-small-family l}
                     (list-of-single-step-functions-small-family-is-bounded l b)

{-constantly-⊥ : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
   constantly-⊥ _ = ⊥ 𝓔

   constantly-⊥⁺ : DCPO[ 𝓓 , 𝓔 ⁻ ]
   constantly-⊥⁺ = (constantly-⊥ , constant-functions-are-continuous 𝓓 (𝓔 ⁻)) -}

   []-is-bounded : ∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by [] e
   []-is-bounded = ∥∥-functor γ
                    (small-compact-basis-contains-all-compact-elements (𝓔 ⁻)
                      βᴱ κᴱ (⊥ 𝓔) (⊥-is-compact 𝓔))
    where
     γ : (Σ e ꞉ Bᴱ , βᴱ e ≡ ⊥ 𝓔)
       → (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by [] e)
     γ (e , _) = (e , 𝟘-induction)

   β-of-[]-is-⊥ : β ([] , []-is-bounded) ≡ ⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)
   β-of-[]-is-⊥ =
    ≡-to-⊥-criterion (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)
     (⋁-is-lowerbound-of-upperbounds {_}
       {list-of-single-step-functions-small-family []}
       (list-of-single-step-functions-small-family-is-bounded [] []-is-bounded)
       (⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)) (λ i → 𝟘-elim (pr₁ i)))

   Bs-are-compact : (b : B) → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β b)
   Bs-are-compact (l , b) =  lemma l b
    where
     A : List (Bᴰ × Bᴱ) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
     A l = (b : (∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e))
         → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β (l , b))
     lemma : (l : List (Bᴰ × Bᴱ)) → A l
     lemma = List-induction A base {!!}
      where
       base : A []
       base bnd = transport (is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) claim
                            (⊥-is-compact (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔))
        where
         claim = ⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)      ≡⟨ β-of-[]-is-⊥ ⁻¹ ⟩
                 -- This is where we use --experimental-lossy-unification
                 β ([] , []-is-bounded) ≡⟨ ap β (to-subtype-≡ (λ _ → ∃-is-prop) refl) ⟩
                 β ([] , bnd)           ∎



{-
  -- We assume that 𝓔 has binary joins of compact elements
  -- TODO: Think more about this
  module _
          (∨ : (x y : ⟪ 𝓔 ⟫) → is-compact (𝓔 ⁻) x → is-compact (𝓔 ⁻) y → ⟪ 𝓔 ⟫)
          (∨-is-upperbound₁ : (x y : ⟪ 𝓔 ⟫)
                              (c₁ : is-compact (𝓔 ⁻) x)
                              (c₂ : is-compact (𝓔 ⁻) y)
                            → x ⊑⟪ 𝓔 ⟫ ∨ x y c₁ c₂ )
          (∨-is-upperbound₁ : (x y : ⟪ 𝓔 ⟫)
                              (c₁ : is-compact (𝓔 ⁻) x)
                              (c₂ : is-compact (𝓔 ⁻) y)
                            → x ⊑⟪ 𝓔 ⟫ ∨ x y c₁ c₂ )
         where

   β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
   β []            = (λ _ → ⊥ 𝓔) , constant-functions-are-continuous 𝓓 (𝓔 ⁻) (⊥ 𝓔)
   β ((d , e) ∷ l) = {!!}
-}

\end{code}
