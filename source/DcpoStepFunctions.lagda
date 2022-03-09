Tom de Jong, late February, early March 2022.

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

open PropositionalTruncation pt hiding (_∨_)

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥 hiding (⊥ ; ⊥-is-least)
open import DcpoBases pt pe fe 𝓥
open import DcpoContinuous pt fe 𝓥
open import DcpoExponential pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

\end{code}

TODO: Write comment

\begin{code}

-- Now the stuff on (single-)step functions

module _
        (𝓓 : DCPO {𝓤}  {𝓣})
        (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
        (𝓓-is-locally-small : is-locally-small 𝓓)
       where

 -- TODO: Factor this out somehow (with Record?)
 {- - - - - - - - - - - - - - - - -}
 _⊑ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
 _⊑ₛ_ = pr₁ 𝓓-is-locally-small

 ⊑ₛ-≃-⊑ : {x y : ⟨ 𝓓 ⟩} → x ⊑ₛ y ≃ x ⊑⟨ 𝓓 ⟩ y
 ⊑ₛ-≃-⊑ {x} {y} = pr₂ 𝓓-is-locally-small x y

 ⊑ₛ-is-prop-valued : (x y : ⟨ 𝓓 ⟩) → is-prop (x ⊑ₛ y)
 ⊑ₛ-is-prop-valued x y = equiv-to-prop ⊑ₛ-≃-⊑ (prop-valuedness 𝓓 x y)

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

 ⦅_⇒_⦆ : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫ → ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
 ⦅ d ⇒ e ⦆ x = ∐ˢˢ 𝓔 α (⊑ₛ-is-prop-valued d x)
  where
   α : d ⊑ₛ x → ⟪ 𝓔 ⟫
   α _ = e

 single-step-function-index : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ →  𝓥 ̇
 single-step-function-index d x = d ⊑ₛ x

 single-step-function-index-is-prop : {d x : ⟨ 𝓓 ⟩}
                                    → is-prop (single-step-function-index d x)
 single-step-function-index-is-prop {d} {x} = ⊑ₛ-is-prop-valued d x

 single-step-function-family : {d x : ⟨ 𝓓 ⟩} (e : ⟪ 𝓔 ⟫)
                             → single-step-function-index d x → ⟪ 𝓔 ⟫
 single-step-function-family e _ = e

 single-step-function-is-continuous : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
                                    → is-compact 𝓓 d
                                    → is-continuous 𝓓 (𝓔 ⁻) ⦅ d ⇒ e ⦆
 single-step-function-is-continuous d e d-is-compact I α δ = (ub , lb-of-ubs)
  where
   ub : (i : I) → ⦅ d ⇒ e ⦆ (α i) ⊑⟪ 𝓔 ⟫ ⦅ d ⇒ e ⦆ (∐ 𝓓 δ)
   ub i = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
           single-step-function-index-is-prop (⦅ d ⇒ e ⦆ (∐ 𝓓 δ))
           (λ p → ∐ˢˢ-is-upperbound 𝓔 (λ _ → e)
                   single-step-function-index-is-prop
                   (d     ⊑ₛ[ p ]
                    α i   ⊑ₛ[ ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (∐-is-upperbound 𝓓 δ i) ]
                    ∐ 𝓓 δ ∎ₛ))
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                (⦅ d ⇒ e ⦆ (∐ 𝓓 δ)) (⦅ d ⇒ e ⦆ ∘ α)
   lb-of-ubs y y-is-ub = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
                          single-step-function-index-is-prop y γ
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
         v = ∐ˢˢ-is-upperbound 𝓔 (λ _ → e) single-step-function-index-is-prop
              (⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ u)

 ⦅_⇒_⦆[_] : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫)
          → is-compact 𝓓 d
          → DCPO[ 𝓓 , 𝓔 ⁻ ]
 ⦅_⇒_⦆[_] d e d-is-compact =
  (⦅ d ⇒ e ⦆ , single-step-function-is-continuous d e d-is-compact)

 -- TODO: Separate the implications?
 -- TODO: Write out ⊑ so as to drop the compactness assumption?
 -- TODO: Make more things abstract?
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
     v = ∐ˢˢ-is-upperbound 𝓔 (λ _ → e) single-step-function-index-is-prop
          (⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 d))
   ⦅2⦆ : e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d
      → ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
   ⦅2⦆ u x = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓔 (λ _ → e)
              single-step-function-index-is-prop
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

  -- TODO: Change name
  pre-β : Bᴰ × Bᴱ → DCPO[ 𝓓 , 𝓔 ⁻ ]
  pre-β (d , e) = ⦅ βᴰ d ⇒ βᴱ e ⦆[ basis-is-compact d ]
   where
    open is-small-compact-basis κᴰ

  module _
          (𝓔-is-sup-complete : is-sup-complete (𝓔 ⁻))
          (f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫)
          (f-is-continuous : is-continuous 𝓓 (𝓔 ⁻) f)
         where

   𝕗 : DCPO[ 𝓓 , 𝓔 ⁻ ]
   𝕗 = f , f-is-continuous

   open is-sup-complete 𝓔-is-sup-complete

   single-step-functions-below-function :
    (Σ p ꞉ (Bᴰ × Bᴱ) , pre-β p ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ 𝕗) → DCPO[ 𝓓 , 𝓔 ⁻ ]
   single-step-functions-below-function = pre-β ∘ pr₁

   single-step-functions-below-function-sup :
    is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
           single-step-functions-below-function
   single-step-functions-below-function-sup = (ub , lb-of-ubs)
    where
     ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
           single-step-functions-below-function
     ub = pr₂
     lb-of-ubs :
      is-lowerbound-of-upperbounds (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
       single-step-functions-below-function
     lb-of-ubs 𝕘@(g , _) g-is-ub x = goal
      where
       module _ where
        open is-small-compact-basis κᴱ
        claim₁ : (d : Bᴰ) (e : Bᴱ) → e ⊑ᴮₛ f (βᴰ d) → βᴱ e ⊑⟪ 𝓔 ⟫ g (βᴰ d)
        claim₁ d e u =
         lr-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                          (is-small-compact-basis.basis-is-compact κᴰ d) 𝕘)
                          (g-is-ub ((d , e) , v))
          where
           v : pre-β (d , e) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ 𝕗
           v = rl-implication
                (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                  (is-small-compact-basis.basis-is-compact κᴰ d) 𝕗)
                (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)
        claim₂ : (d : Bᴰ) → f (βᴰ d) ⊑⟪ 𝓔 ⟫ g (βᴰ d)
        claim₂ d = f (βᴰ d)                             ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
                   ∐ (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d))) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
                   g (βᴰ d)                             ∎⟪ 𝓔 ⟫
         where
          ⦅1⦆ = ↓ᴮₛ-∐-⊒ (f (βᴰ d))
          ⦅2⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d)))
                 (g (βᴰ d)) (λ (e , v) → claim₁ d e v)

       open is-small-compact-basis κᴰ
       δ : is-Directed 𝓓 (↓ιₛ x)
       δ = ↓ᴮₛ-is-directed x
       ε : is-Directed (𝓔 ⁻) (f ∘ ↓ιₛ x)
       ε = image-is-directed' 𝓓 (𝓔 ⁻) 𝕗 δ

       goal : f x ⊑⟪ 𝓔 ⟫ g x
       goal = f x       ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
              f (∐ 𝓓 δ) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
              ∐ (𝓔 ⁻) ε ⊑⟪ 𝓔 ⟫[ ⦅3⦆ ]
              g x       ∎⟪ 𝓔 ⟫
        where
         ⦅1⦆ = ≡-to-⊒ (𝓔 ⁻) (ap f (↓ᴮₛ-∐-≡ x))
         ⦅2⦆ = continuous-∐-⊑ 𝓓 (𝓔 ⁻) 𝕗 δ
         ⦅3⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) ε (g x) γ
          where
           γ : is-upperbound (underlying-order (𝓔 ⁻)) (g x) (f ∘ ↓ιₛ x)
           γ (d , u) = f (βᴰ d) ⊑⟪ 𝓔 ⟫[ claim₂ d ]
                       g (βᴰ d) ⊑⟪ 𝓔 ⟫[ v        ]
                       g x      ∎⟪ 𝓔 ⟫
            where
             v = monotone-if-continuous 𝓓 (𝓔 ⁻) 𝕘 (βᴰ d) x (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)

  module _
          (𝓔-is-sup-complete : is-sup-complete (𝓔 ⁻))
         where

   private
    exp-is-sup-complete : is-sup-complete (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
    exp-is-sup-complete = exponential-is-sup-complete 𝓓 (𝓔 ⁻) 𝓔-is-sup-complete

   open sup-complete-dcpo (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete
   open directify-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete

   private
    B : 𝓥 ̇
    B = domain (directify pre-β)
    β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
    β = directify pre-β

   exponential-has-small-compact-basis : is-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β
   exponential-has-small-compact-basis = record {
      basis-is-compact = ⦅1⦆
    ; ⊑ᴮ-is-small      = ⦅2⦆
    ; ↓ᴮ-is-directed   = ⦅3⦆
    ; ↓ᴮ-is-sup        = ⦅4⦆
    }
     where
      ⦅1⦆ : (b : B) → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β b)
      ⦅1⦆ = directify-is-compact pre-β
            (λ (d , e) → single-step-function-is-compact (βᴰ d) (βᴱ e)
                          (is-small-compact-basis.basis-is-compact κᴰ d)
                          (is-small-compact-basis.basis-is-compact κᴱ e))
      ⦅2⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩) (b : B)
          → is-small (β b ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f)
      ⦅2⦆ f b = ⌜ local-smallness-equivalent-definitions (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) ⌝
                 exp-is-locally-small (β b) f
       where
        exp-is-locally-small : is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
        exp-is-locally-small =
         locally-small-exponential-criterion 𝓓 (𝓔 ⁻)
          ∣ Bᴰ , βᴰ , compact-basis-is-basis 𝓓 βᴰ κᴰ ∣ -- TODO: Improve these "projections"
          (locally-small-if-small-basis (𝓔 ⁻) βᴱ
            (compact-basis-is-basis (𝓔 ⁻) βᴱ κᴱ))
        _⊑'_ : DCPO[ 𝓓 , 𝓔 ⁻ ] → DCPO[ 𝓓 , 𝓔 ⁻ ] → 𝓥 ̇
        _⊑'_ = pr₁ exp-is-locally-small
      ⦅3⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩)
          → is-Directed (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (↓ι (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β f)
      ⦅3⦆ f = directify-↓-is-directed pre-β {f}
      ⦅4⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩)
          → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
             (↓ι (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β f)
      ⦅4⦆ (f , f-is-cts) =
       directify-↓-sup pre-β
        (single-step-functions-below-function-sup 𝓔-is-sup-complete
        f f-is-cts)

   exponential-has-specified-small-compact-basis :
    has-specified-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
   exponential-has-specified-small-compact-basis =
    (B , β , exponential-has-small-compact-basis)

\end{code}

TODO: Write comment on proof strategy

Exponentials of dcpos with small bases...

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {Bᴰ : 𝓥 ̇  }
        (βᴰ : Bᴰ → ⟨ 𝓓 ⟩)
        (βᴰ-is-small-basis : is-small-basis 𝓓 βᴰ)
        (𝓓-is-sup-complete : is-sup-complete 𝓓)
       where

 open import IdealCompletion-Properties pt fe pe 𝓥
 open Idl-algebraic 𝓓 βᴰ βᴰ-is-small-basis

 -- TODO: How to prove that Idl-DCPO is sup-complete?
 -- Seem to need that the basis is closed under binary joins...


module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        {Bᴰ Bᴱ : 𝓥 ̇  }
        (βᴰ : Bᴰ → ⟨ 𝓓 ⟩)
        (βᴱ : Bᴱ → ⟨ 𝓔 ⟩)
        (βᴰ-is-small-basis : is-small-basis 𝓓 βᴰ)
        (βᴱ-is-small-basis : is-small-basis 𝓔 βᴱ)
        (𝓔-is-sup-complete : is-sup-complete 𝓔)
       where

 open import IdealCompletion-Properties pt fe pe 𝓥

 private
  module _ where
   open Idl-algebraic 𝓓 βᴰ βᴰ-is-small-basis
   𝓓' : DCPO {𝓥 ⁺} {𝓥}
   𝓓' = Idl-DCPO
   𝓓-continuous-retract-of-𝓓' : 𝓓 continuous-retract-of 𝓓'
   𝓓-continuous-retract-of-𝓓' = Idl-continuous-retract
  module _ where
   open Idl-algebraic 𝓔 βᴱ βᴱ-is-small-basis
   𝓔' : DCPO {𝓥 ⁺} {𝓥}
   𝓔' = Idl-DCPO
   𝓔-continuous-retract-of-𝓔' : 𝓔 continuous-retract-of 𝓔'
   𝓔-continuous-retract-of-𝓔' = Idl-continuous-retract

  exp-continuous-retract : (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) continuous-retract-of (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
  exp-continuous-retract = record {
     s               = s
   ; r               = r
   ; r-s-equation    = r-s-equation
   ; s-is-continuous = s-is-cts
   ; r-is-continuous = r-is-cts
   }
    where
     module _ where
      open _continuous-retract-of_ 𝓓-continuous-retract-of-𝓓'
      sᴰ = s
      rᴰ = r
      sᴰ-is-cts = s-is-continuous
      rᴰ-is-cts = r-is-continuous
      rᴰ-sᴰ-equation = r-s-equation
     module _ where
      open _continuous-retract-of_ 𝓔-continuous-retract-of-𝓔'
      sᴱ = s
      rᴱ = r
      sᴱ-is-cts = s-is-continuous
      rᴱ-is-cts = r-is-continuous
      rᴱ-sᴱ-equation = r-s-equation
     s : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩ → ⟨ 𝓓' ⟹ᵈᶜᵖᵒ 𝓔' ⟩
     s f = DCPO-∘₃ 𝓓' 𝓓 𝓔 𝓔' (rᴰ , rᴰ-is-cts) f (sᴱ , sᴱ-is-cts)
     r : ⟨ 𝓓' ⟹ᵈᶜᵖᵒ 𝓔' ⟩ → ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩
     r g = DCPO-∘₃ 𝓓 𝓓' 𝓔' 𝓔 (sᴰ , sᴰ-is-cts) g (rᴱ , rᴱ-is-cts)
     r-s-equation : r ∘ s ∼ id
     r-s-equation (f , _) = to-continuous-function-≡ 𝓓 𝓔 γ
      where
       γ : rᴱ ∘ sᴱ ∘ f ∘ rᴰ ∘ sᴰ ∼ f
       γ x = (rᴱ ∘ sᴱ ∘ f ∘ rᴰ ∘ sᴰ) x ≡⟨ rᴱ-sᴱ-equation ((f ∘ rᴰ ∘ sᴰ) x) ⟩
             (f ∘ rᴰ ∘ sᴰ) x           ≡⟨ ap f (rᴰ-sᴰ-equation x) ⟩
             f x                       ∎
     s-is-cts : is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') s
     s-is-cts = DCPO-∘₃-is-continuous₂ 𝓓' 𝓓 𝓔 𝓔'
                 (rᴰ , rᴰ-is-cts) (sᴱ , sᴱ-is-cts)
     r-is-cts : is-continuous (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) r
     r-is-cts = DCPO-∘₃-is-continuous₂ 𝓓 𝓓' 𝓔' 𝓔
                 (sᴰ , sᴰ-is-cts) (rᴱ , rᴱ-is-cts)

  exp-has-small-compact-basis : has-specified-small-compact-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
  exp-has-small-compact-basis =
   exponential-has-specified-small-compact-basis 𝓓' (𝓔' , {!!})
    {!!} B' {!!} β' {!!} {!!} {!!} {!!}
     where
      module _ where
       open Idl-algebraic 𝓓 βᴰ βᴰ-is-small-basis
       B' : 𝓥 ̇
       B' = pr₁ (Idl-has-specified-small-compact-basis (λ _ → ⊑ᴮ-is-reflexive))
       β' : {!!}
       β' = pr₁ (pr₂ (Idl-has-specified-small-compact-basis
                       (λ _ → ⊑ᴮ-is-reflexive)))

 exponential-has-small-basis : has-specified-small-basis (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
 exponential-has-small-basis = B , r ∘ β ,
  small-basis-from-continuous-retract (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
   exp-continuous-retract β (compact-basis-is-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') β
    ((pr₂ (pr₂ (exp-has-small-compact-basis))))) -- TODO: Clean up
  where
   open _continuous-retract-of_ exp-continuous-retract
   B : 𝓥 ̇
   B = pr₁ exp-has-small-compact-basis
   β : B → DCPO[ 𝓓' , 𝓔' ]
   β = pr₁ (pr₂ exp-has-small-compact-basis)

\end{code}
