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

-- TODO: Move this to DcpoMiscelanea, but think about hiding (⊥ ; ⊥-is-least)
module _ -- TODO: Name this module so to avoid giving the sup-completeness all the time?
        (𝓓 : DCPO {𝓤} {𝓣'})
        (𝓓-is-sup-complete : is-sup-complete 𝓓)
       where

 open is-sup-complete 𝓓-is-sup-complete

 open import List

 ⊥ : ⟨ 𝓓 ⟩
 ⊥ = ⋁ 𝟘-elim

 ⊥-is-least : is-least (underlying-order 𝓓) ⊥
 ⊥-is-least x = ⋁-is-lowerbound-of-upperbounds 𝟘-elim x 𝟘-induction

 ∨-family : (x y : ⟨ 𝓓 ⟩) → 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
 ∨-family x y (inl _) = x
 ∨-family x y (inr _) = y

 _∨_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩
 x ∨ y = ⋁ (∨-family x y)

 infix 100 _∨_

 ∨-is-upperbound₁ : {x y : ⟨ 𝓓 ⟩} → x ⊑⟨ 𝓓 ⟩ x ∨ y
 ∨-is-upperbound₁ {x} {y} = ⋁-is-upperbound (∨-family x y) (inl ⋆)

 ∨-is-upperbound₂ : {x y : ⟨ 𝓓 ⟩} → y ⊑⟨ 𝓓 ⟩ x ∨ y
 ∨-is-upperbound₂ {x} {y} = ⋁-is-upperbound (∨-family x y) (inr ⋆)

 ∨-is-lowerbound-of-upperbounds : {x y z : ⟨ 𝓓 ⟩}
                                → x ⊑⟨ 𝓓 ⟩ z → y ⊑⟨ 𝓓 ⟩ z
                                → x ∨ y ⊑⟨ 𝓓 ⟩ z
 ∨-is-lowerbound-of-upperbounds {x} {y} {z} u v =
  ⋁-is-lowerbound-of-upperbounds (∨-family x y) z γ
   where
    γ : is-upperbound (underlying-order 𝓓) z (∨-family x y)
    γ (inl _) = u
    γ (inr _) = v

 module _
         {I : 𝓦 ̇  }
         (α : I → ⟨ 𝓓 ⟩)
        where

  directify : List I → ⟨ 𝓓 ⟩
  directify []      = ⊥
  directify (x ∷ l) = α x ∨ directify l

  -- directy α is directed (hence the name), but we don't seem to need that fact

  directify-↓ : (x : ⟨ 𝓓 ⟩) → (Σ l ꞉ List I , directify l ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
  directify-↓ x = directify ∘ pr₁

  directify-is-compact : ((i : I) → is-compact 𝓓 (α i))
                       → (l : List I) → is-compact 𝓓 (directify l)
  directify-is-compact αs-are-compact []      =
   ⊥-is-compact (𝓓 , ⊥ , ⊥-is-least)
  directify-is-compact αs-are-compact (i ∷ l) =
   binary-join-is-compact 𝓓 ∨-is-upperbound₁ ∨-is-upperbound₂
    (λ d → ∨-is-lowerbound-of-upperbounds) (αs-are-compact i) IH
    where
     IH : is-compact 𝓓 (directify l)
     IH = directify-is-compact αs-are-compact l

  directify-↓-is-compact : {x : ⟨ 𝓓 ⟩} → ((i : I) → is-compact 𝓓 (α i))
                         → (j : domain (directify-↓ x))
                         → is-compact 𝓓 (directify-↓ x j)
  directify-↓-is-compact αs-are-compact j =
   directify-is-compact αs-are-compact (pr₁ j)

  directify-↓-is-inhabited : {x : ⟨ 𝓓 ⟩} → ∥ domain (directify-↓ x) ∥
  directify-↓-is-inhabited {x} = ∣ [] , ⊥-is-least x ∣

  ++-is-upperbound₁ : (l k : List I) → directify l ⊑⟨ 𝓓 ⟩ directify (l ++ k)
  ++-is-upperbound₁ []      k = ⊥-is-least (directify ([] ++ k))
  ++-is-upperbound₁ (i ∷ l) k =
   ∨-is-lowerbound-of-upperbounds ∨-is-upperbound₁
    (directify l              ⊑⟨ 𝓓 ⟩[ ++-is-upperbound₁ l k ]
     directify (l ++ k)       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
     α i ∨ directify (l ++ k) ∎⟨ 𝓓 ⟩)

  ++-is-upperbound₂ : (l k : List I) → directify k ⊑⟨ 𝓓 ⟩ directify (l ++ k)
  ++-is-upperbound₂ []      k = reflexivity 𝓓 (directify k)
  ++-is-upperbound₂ (i ∷ l) k =
   directify k              ⊑⟨ 𝓓 ⟩[ ++-is-upperbound₂ l k ]
   directify (l ++ k)       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
   α i ∨ directify (l ++ k) ∎⟨ 𝓓 ⟩

  ++-is-lowerbound-of-upperbounds : (l k : List I) {x : ⟨ 𝓓 ⟩}
                                  → directify l ⊑⟨ 𝓓 ⟩ x
                                  → directify k ⊑⟨ 𝓓 ⟩ x
                                  → directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
  ++-is-lowerbound-of-upperbounds []      k {x} u v = v
  ++-is-lowerbound-of-upperbounds (i ∷ l) k {x} u v =
   ∨-is-lowerbound-of-upperbounds ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ = α i              ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
          α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
          x                 ∎⟨ 𝓓 ⟩
     ⦅2⦆ : directify (l ++ k) ⊑⟨ 𝓓 ⟩ x
     ⦅2⦆ = ++-is-lowerbound-of-upperbounds l k ⦅2'⦆ v
      where
       ⦅2'⦆ = directify l      ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₂ ]
             α i ∨ directify l ⊑⟨ 𝓓 ⟩[ u ]
             x                 ∎⟨ 𝓓 ⟩

  directify-↓-is-semidirected : {x : ⟨ 𝓓 ⟩} → is-Semidirected 𝓓 (directify-↓ x)
  directify-↓-is-semidirected (l , l-below-x) (k , k-below-x) =
   ∣ ((l ++ k) , ++-is-lowerbound-of-upperbounds l k l-below-x k-below-x)
               , (++-is-upperbound₁ l k) , (++-is-upperbound₂ l k) ∣

  -- TODO: Make explicit?
  directify-↓-is-directed : {x : ⟨ 𝓓 ⟩} → is-Directed 𝓓 (directify-↓ x)
  directify-↓-is-directed =
   (directify-↓-is-inhabited , directify-↓-is-semidirected)

  directify-↓-upperbound : {x : ⟨ 𝓓 ⟩}
                         → is-upperbound (underlying-order 𝓓) x (directify-↓ x)
  directify-↓-upperbound = pr₂

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   family-↓ : (Σ i ꞉ I , α i ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩
   family-↓ = α ∘ pr₁

   directify-↓-sup : is-sup (underlying-order 𝓓) x family-↓
                   → is-sup (underlying-order 𝓓) x (directify-↓ x)
   directify-↓-sup (x-ub , x-lb-of-ubs) = (directify-↓-upperbound , γ)
    where
     γ : is-lowerbound-of-upperbounds (underlying-order 𝓓) x (directify-↓ x)
     γ y y-is-ub = x-lb-of-ubs y claim
      where
       claim : is-upperbound (underlying-order 𝓓) y family-↓
       claim (i , αᵢ-below-x) =
        α i                       ⊑⟨ 𝓓 ⟩[ ∨-is-upperbound₁ ]
        directify-↓ x ([ i ] , u) ⊑⟨ 𝓓 ⟩[ y-is-ub ([ i ] , u) ]
        y                         ∎⟨ 𝓓 ⟩
         where
          u : α i ∨ ⊥ ⊑⟨ 𝓓 ⟩ x
          u = ∨-is-lowerbound-of-upperbounds αᵢ-below-x (⊥-is-least x)

\end{code}

TODO: Write comment

\begin{code}

 module _
         (𝓓-is-locally-small : is-locally-small 𝓓)
         {I : 𝓥 ̇  }
         (α : I → ⟨ 𝓓 ⟩)
        where

  private
   _⊑ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
   _⊑ₛ_ = pr₁ 𝓓-is-locally-small -- TODO: Think about making local smallness a record

  directify-↓-small : (x : ⟨ 𝓓 ⟩) → (Σ l ꞉ List I , directify α l ⊑ₛ x) → ⟨ 𝓓 ⟩
  directify-↓-small x = directify α ∘ pr₁

  module _
          {x : ⟨ 𝓓 ⟩}
         where

   directify-↓-small-≃ : domain (directify-↓ α x) ≃ domain (directify-↓-small x)
   directify-↓-small-≃ =
    Σ-cong (λ l → ≃-sym (pr₂ 𝓓-is-locally-small (directify α l) x))

   directify-↓-small-sup : is-sup (underlying-order 𝓓) x (family-↓ α)
                         → is-sup (underlying-order 𝓓) x (directify-↓-small x)
   directify-↓-small-sup x-is-sup =
    reindexed-family-sup 𝓓 directify-↓-small-≃
     (directify-↓ α x) x (directify-↓-sup α x-is-sup)

   directify-↓-small-is-directed : is-Directed 𝓓 (directify-↓-small x)
   directify-↓-small-is-directed =
    reindexed-family-is-directed 𝓓 directify-↓-small-≃
     (directify-↓ α x) (directify-↓-is-directed α)



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

    B : 𝓥 ̇
    B = domain (directify (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete pre-β)

    β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
    β = directify (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete pre-β

   exponential-has-small-compact-basis : is-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β
   exponential-has-small-compact-basis = record {
      basis-is-compact = ⦅1⦆
    ; ⊑ᴮ-is-small      = ⦅2⦆
    ; ↓ᴮ-is-directed   = ⦅3⦆
    ; ↓ᴮ-is-sup        = ⦅4⦆
    }
     where
      ⦅1⦆ : (b : B) → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β b)
      ⦅1⦆ = directify-is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete
            pre-β (λ (d , e) → single-step-function-is-compact
                                (βᴰ d) (βᴱ e)
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
      ⦅3⦆ f = directify-↓-is-directed (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete
              pre-β {f}
      ⦅4⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩)
          → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
             (↓ι (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β f)
      ⦅4⦆ (f , f-is-cts) =
       directify-↓-sup (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete pre-β
        (single-step-functions-below-function-sup 𝓔-is-sup-complete
        f f-is-cts)

   exponential-has-specified-small-compact-basis :
    has-specified-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
   exponential-has-specified-small-compact-basis =
    (B , β , exponential-has-small-compact-basis)

\end{code}
