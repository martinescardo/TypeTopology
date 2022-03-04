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

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 record is-sup-complete : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ⋁ : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩
   ⋁-is-sup : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) (⋁ α) α

  ⋁-is-upperbound : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩)
                  → is-upperbound (underlying-order 𝓓) (⋁ α) α
  ⋁-is-upperbound α = sup-is-upperbound (underlying-order 𝓓) (⋁-is-sup α)

  ⋁-is-lowerbound-of-upperbounds : {I : 𝓥 ̇  } (α : I → ⟨ 𝓓 ⟩)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (⋁ α) α
  ⋁-is-lowerbound-of-upperbounds α =
   sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (⋁-is-sup α)

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (𝓔-is-sup-complete : is-sup-complete 𝓔)
       where

 open is-sup-complete 𝓔-is-sup-complete

 sup-of-continuous-functions : {I : 𝓥 ̇  } → (I → DCPO[ 𝓓 , 𝓔 ]) → DCPO[ 𝓓 , 𝓔 ]
 sup-of-continuous-functions {I} α = (f , c)
  where
   f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   f x = ⋁ (pointwise-family 𝓓 𝓔 α x)
   c : is-continuous 𝓓 𝓔 f
   c J β δ = (ub , lb-of-ubs)
    where
     ub : is-upperbound (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ β)
     ub i = ⋁-is-lowerbound-of-upperbounds
             (pointwise-family 𝓓 𝓔 α (β i)) (f (∐ 𝓓 δ)) γ
      where
       γ : is-upperbound (underlying-order 𝓔) (f (∐ 𝓓 δ))
            (pointwise-family 𝓓 𝓔 α (β i))
       γ j = [ 𝓓 , 𝓔 ]⟨ α j ⟩ (β i)   ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
             [ 𝓓 , 𝓔 ]⟨ α j ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
             f (∐ 𝓓 δ)                 ∎⟨ 𝓔 ⟩
        where
         ⦅1⦆ = monotone-if-continuous 𝓓 𝓔 (α j) (β i) (∐ 𝓓 δ)
               (∐-is-upperbound 𝓓 δ i)
         ⦅2⦆ = ⋁-is-upperbound (pointwise-family 𝓓 𝓔 α (∐ 𝓓 δ)) j
     lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓔) (f (∐ 𝓓 δ))
                  (f ∘ β)
     lb-of-ubs y y-is-ub =
      ⋁-is-lowerbound-of-upperbounds (pointwise-family 𝓓 𝓔 α (∐ 𝓓 δ))
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
               ⦅†⦆ = ⋁-is-upperbound (pointwise-family 𝓓 𝓔 α (β j)) i

 exponential-is-bounded-complete : is-sup-complete (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
 exponential-is-bounded-complete = record {
     ⋁        = λ {I} α → sup-of-continuous-functions α
   ; ⋁-is-sup = λ {I} → lemma
  }
   where
    lemma : {I : 𝓥 ̇  } (α : I → DCPO[ 𝓓 , 𝓔 ])
          → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
             (sup-of-continuous-functions α) α
    lemma {I} α = (ub , lb-of-ubs)
     where
      ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
            (sup-of-continuous-functions α) α
      ub i x = ⋁-is-upperbound (pointwise-family 𝓓 𝓔 α x) i
      lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔))
                   (sup-of-continuous-functions α) α
      lb-of-ubs g g-is-ub x =
       ⋁-is-lowerbound-of-upperbounds (pointwise-family 𝓓 𝓔 α x)
                                      ([ 𝓓 , 𝓔 ]⟨ g ⟩ x) (λ i → g-is-ub i x)

module _
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

 -- TODO: Factor this out somehow
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

   B : 𝓥 ̇
   B = domain (directify {!𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)!} {!!} pre-β)


--   open is-small-compact-basis κᴱ




--   single-step-functions-below-function : (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
--                                        → 𝓥 ̇
--   single-step-functions-below-function f =
--    Σ d ꞉ Bᴰ , Σ e ꞉ Bᴱ , e ⊑ᴮₛ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ (βᴰ d)

--   single-step-functions-below-function-family :
--      (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
--    → single-step-functions-below-function f → DCPO[ 𝓓 , 𝓔 ⁻ ]
--   single-step-functions-below-function-family f (d , e , _) =
--    ⦅ βᴰ d ⇒ βᴱ e ⦆[ is-small-compact-basis.basis-is-compact κᴰ d ]

--   sup-of-single-step-functions :
--      (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
--    → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--             (single-step-functions-below-function-family f)
--   sup-of-single-step-functions 𝕗@(f , _) = (ub , lb-of-ubs)
--    where
--     ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
--           (single-step-functions-below-function-family 𝕗)
--     ub (d , e , u) =
--      rl-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
--                       (is-small-compact-basis.basis-is-compact κᴰ d) 𝕗)
--                       (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)

--     lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) 𝕗
--                  (single-step-functions-below-function-family 𝕗)
--     lb-of-ubs 𝕘@(g , _) g-is-ub x = goal
--      where
--       claim₁ : (d : Bᴰ) (e : Bᴱ) → e ⊑ᴮₛ f (βᴰ d) → βᴱ e ⊑⟪ 𝓔 ⟫ g (βᴰ d)
--       claim₁ d e u =
--        lr-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
--                         (is-small-compact-basis.basis-is-compact κᴰ d) 𝕘)
--                         (g-is-ub (d , e , u))
--       claim₂ : (d : Bᴰ) → f (βᴰ d) ⊑⟪ 𝓔 ⟫ g (βᴰ d)
--       claim₂ d = f (βᴰ d)                             ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
--                  ∐ (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d))) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
--                  g (βᴰ d)                             ∎⟪ 𝓔 ⟫
--        where
--         ⦅1⦆ = ↓ᴮₛ-∐-⊒ (f (βᴰ d))
--         ⦅2⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d)))
--                (g (βᴰ d)) (λ (e , v) → claim₁ d e v)

--       δ : is-Directed 𝓓 (is-small-compact-basis.↓ιₛ κᴰ x)
--       δ = is-small-compact-basis.↓ᴮₛ-is-directed κᴰ x
--       ε : is-Directed (𝓔 ⁻) (f ∘ is-small-compact-basis.↓ιₛ κᴰ x)
--       ε = image-is-directed' 𝓓 (𝓔 ⁻) 𝕗 δ
--       goal : f x ⊑⟪ 𝓔 ⟫ g x
--       goal = f x       ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
--              f (∐ 𝓓 δ) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
--              ∐ (𝓔 ⁻) ε ⊑⟪ 𝓔 ⟫[ ⦅3⦆ ]
--              g x       ∎⟪ 𝓔 ⟫
--        where
--         ⦅1⦆ = ≡-to-⊒ (𝓔 ⁻) (ap f (is-small-compact-basis.↓ᴮₛ-∐-≡ κᴰ x))
--         ⦅2⦆ = continuous-∐-⊑ 𝓓 (𝓔 ⁻) 𝕗 δ
--         ⦅3⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) ε (g x) γ
--          where
--           γ : is-upperbound (underlying-order (𝓔 ⁻)) (g x)
--                (f ∘ is-small-compact-basis.↓ιₛ κᴰ x)
--           γ (d , u) = f (βᴰ d) ⊑⟪ 𝓔 ⟫[ claim₂ d ]
--                       g (βᴰ d) ⊑⟪ 𝓔 ⟫[ v        ]
--                       g x      ∎⟪ 𝓔 ⟫
--            where
--             v = monotone-if-continuous 𝓓 (𝓔 ⁻) 𝕘 (βᴰ d) x
--                  (⌜ is-small-compact-basis.⊑ᴮₛ-≃-⊑ᴮ κᴰ ⌝ u)

--   open import Fin
--   open import SpartanMLTT-List hiding (⟨_⟩)

--   list-of-single-step-functions-bounded-by : (l : List (Bᴰ × Bᴱ)) (e : Bᴱ)
--                                            → 𝓥 ̇
--   list-of-single-step-functions-bounded-by l e =
--    (i : Fin (length l)) → e̅ i ⊑ᴮₛ βᴱ e
--     where
--      e̅ : Fin (length l) → Bᴱ
--      e̅ i = pr₂ (pr₂ l !! i)

--   list-of-single-step-functions-is-bounded : (l : List (Bᴰ × Bᴱ)) → 𝓥 ̇
--   list-of-single-step-functions-is-bounded l =
--    ∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e

--   B : 𝓥 ̇
--   B = Σ l ꞉ List (Bᴰ × Bᴱ) , ∃ e ꞉ Bᴱ
--                            , list-of-single-step-functions-bounded-by l e

--   module _
--           (𝓔-bounded-complete : is-bounded-complete (𝓔 ⁻))
--          where

--    open is-bounded-complete (exponential-is-bounded-complete 𝓓 (𝓔 ⁻)
--                               𝓔-bounded-complete)
--    open import UF-UniverseEmbedding

--    module _
--            (l : List (Bᴰ × Bᴱ))
--           where
--     private
--      n : ℕ
--      n = length l

--     d̅ : Fin n → Bᴰ
--     d̅ i = pr₁ (pr₂ l !! i)

--     e̅ : Fin n → Bᴱ
--     e̅ i = pr₂ (pr₂ l !! i)

--     d̅s-are-compact : (i : Fin n) → is-compact 𝓓 (βᴰ (d̅ i))
--     d̅s-are-compact i = is-small-compact-basis.basis-is-compact κᴰ (d̅ i)

--     -- TODO: Add e̅s-are-compact too?

--     list-of-single-step-functions-family : Fin n → DCPO[ 𝓓 , 𝓔 ⁻ ]
--     list-of-single-step-functions-family i =
--      ⦅ βᴰ (d̅ i) ⇒ βᴱ (e̅ i) ⦆[ d̅s-are-compact i ]

--     list-of-single-step-functions-family-is-bounded :
--        list-of-single-step-functions-is-bounded l
--      → is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) list-of-single-step-functions-family
--     list-of-single-step-functions-family-is-bounded = ∥∥-functor γ
--      where
--        α : Fin n → DCPO[ 𝓓 , 𝓔 ⁻ ]
--        α = list-of-single-step-functions-family
--        γ : (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e)
--          → (Σ f ꞉ DCPO[ 𝓓 , 𝓔 ⁻ ] , is-upperbound (_hom-⊑_ 𝓓 (𝓔 ⁻)) f α)
--        γ (e , e-bounded) = ((f , f-is-continuous) , f-is-ub-of-α')
--         where
--          f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
--          f _ = βᴱ e
--          f-is-continuous : is-continuous 𝓓 (𝓔 ⁻) f
--          f-is-continuous = constant-functions-are-continuous 𝓓 (𝓔 ⁻)
--          f-is-ub-of-α' : (i : domain α) (x : ⟨ 𝓓 ⟩)
--                        → [ 𝓓 , 𝓔 ⁻ ]⟨ α i ⟩ x ⊑⟪ 𝓔 ⟫ f x
--          f-is-ub-of-α' i =
--           rl-implication (below-single-step-function-criterion
--                            (βᴰ (d̅ i)) (βᴱ (e̅ i))
--                            (d̅s-are-compact i)
--                            (f , f-is-continuous)) h
--           where
--            h : βᴱ (e̅ i) ⊑⟪ 𝓔 ⟫ βᴱ e
--            h = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ (e-bounded i)

--     list-of-single-step-functions-small-family : Lift 𝓥 (Fin n) → DCPO[ 𝓓 , 𝓔 ⁻ ]
--     list-of-single-step-functions-small-family =
--      reindexed-family (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (≃-Lift 𝓥 (Fin n))
--                       list-of-single-step-functions-family

--     list-of-single-step-functions-small-family-is-bounded :
--        list-of-single-step-functions-is-bounded l
--      → is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) list-of-single-step-functions-small-family
--     list-of-single-step-functions-small-family-is-bounded b =
--      reindexed-family-is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (≃-Lift 𝓥 (Fin n))
--       list-of-single-step-functions-family
--       (list-of-single-step-functions-family-is-bounded b)


--    β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
--    β (l , b) = ⋁ {_} {list-of-single-step-functions-small-family l}
--                      (list-of-single-step-functions-small-family-is-bounded l b)

-- {-constantly-⊥ : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫
--    constantly-⊥ _ = ⊥ 𝓔

--    constantly-⊥⁺ : DCPO[ 𝓓 , 𝓔 ⁻ ]
--    constantly-⊥⁺ = (constantly-⊥ , constant-functions-are-continuous 𝓓 (𝓔 ⁻)) -}

--    []-is-bounded : ∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by [] e
--    []-is-bounded = ∥∥-functor γ
--                     (small-compact-basis-contains-all-compact-elements (𝓔 ⁻)
--                       βᴱ κᴱ (⊥ 𝓔) (⊥-is-compact 𝓔))
--     where
--      γ : (Σ e ꞉ Bᴱ , βᴱ e ≡ ⊥ 𝓔)
--        → (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by [] e)
--      γ (e , _) = (e , 𝟘-induction)

--    β-of-[]-is-⊥ : β ([] , []-is-bounded) ≡ ⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)
--    β-of-[]-is-⊥ =
--     ≡-to-⊥-criterion (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)
--      (⋁-is-lowerbound-of-upperbounds {_}
--        {list-of-single-step-functions-small-family []}
--        (list-of-single-step-functions-small-family-is-bounded [] []-is-bounded)
--        (⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)) (λ i → 𝟘-elim (pr₁ i)))

--    Bs-are-compact : (b : B) → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β b)
--    Bs-are-compact (l , b) =  lemma l b
--     where
--      A : List (Bᴰ × Bᴱ) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
--      A l = (b : list-of-single-step-functions-is-bounded l)
--          → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β (l , b))
--      lemma : (l : List (Bᴰ × Bᴱ)) → A l
--      lemma = List-induction A base step
--       where
--        base : A []
--        base bnd = transport (is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) claim
--                             (⊥-is-compact (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔))
--         where
--          claim = ⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔)      ≡⟨ β-of-[]-is-⊥ ⁻¹ ⟩
--                  -- This is where we use --experimental-lossy-unification
--                  β ([] , []-is-bounded) ≡⟨ ap β (to-subtype-≡ (λ _ → ∃-is-prop) refl) ⟩
--                  β ([] , bnd)           ∎
--        step : (x : Bᴰ × Bᴱ) (l : List (Bᴰ × Bᴱ)) → A l → A (x ∷ l)
--        step (d₀ , e₀) l IH l⁺-is-bounded =
--         binary-join-is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) ⦅1⦆ ⦅2⦆ ⦅3⦆
--          d₀⇒e₀-is-compact βl-is-compact
--          where
--           l⁺ : List (Bᴰ × Bᴱ)
--           l⁺ = (d₀ , e₀) ∷ l
--           l-is-bounded : list-of-single-step-functions-is-bounded l
--           l-is-bounded = ∥∥-functor γ l⁺-is-bounded
--            where
--             γ : (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by
--                              ((d₀ :: e₀) ∷ l) e)
--               → (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e)
--             γ (e , e-ub) = (e , e-ub ∘ fsucc)
--           βl-is-compact : is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β (l , l-is-bounded))
--           βl-is-compact = IH l-is-bounded
--           d₀-is-compact : is-compact 𝓓 (βᴰ d₀)
--           d₀-is-compact = d̅s-are-compact l⁺ fzero
--           e₀-is-compact : is-compact (𝓔 ⁻) (βᴱ e₀)
--           e₀-is-compact = is-small-compact-basis.basis-is-compact κᴱ e₀
--           d₀⇒e₀-is-compact : is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
--                               (⦅ βᴰ d₀ ⇒ βᴱ e₀ ⦆[ d₀-is-compact ])
--           d₀⇒e₀-is-compact = single-step-function-is-compact (βᴰ d₀) (βᴱ e₀)
--                               d₀-is-compact e₀-is-compact

--           l-is-bounded-family : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
--                                  (list-of-single-step-functions-small-family l)
--           l-is-bounded-family =
--            list-of-single-step-functions-small-family-is-bounded l l-is-bounded
--           l⁺-is-bounded-family : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
--                                   (list-of-single-step-functions-small-family l⁺)
--           l⁺-is-bounded-family =
--            list-of-single-step-functions-small-family-is-bounded l⁺ l⁺-is-bounded

--           -- TODO: Clean this up
--           ⦅1⦆ : ⦅ βᴰ d₀ ⇒ βᴱ e₀ ⦆[ d₀-is-compact ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩
--                β (l⁺ , l⁺-is-bounded)
--           ⦅1⦆ = ⋁-is-upperbound l⁺-is-bounded-family (⌜ ≃-Lift 𝓥 _ ⌝ fzero)
--           ⦅2⦆ : β (l , l-is-bounded) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ β (l⁺ , l⁺-is-bounded)
--           ⦅2⦆ = ⋁-is-lowerbound-of-upperbounds l-is-bounded-family
--                 (β (l⁺ , l⁺-is-bounded))
--                 (λ i → ⋁-is-upperbound l⁺-is-bounded-family (⌜ ≃-Lift 𝓥 _ ⌝ (fsucc (⌜ Lift-≃ 𝓥 _ ⌝ i))))
--           ⦅3⦆ : (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
--               → ⦅ βᴰ d₀ ⇒ βᴱ e₀ ⦆[ d₀-is-compact ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
--               → β (l , l-is-bounded) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
--               → β (l⁺ , l⁺-is-bounded) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
--           ⦅3⦆ f f-ub₁ f-ub₂ = ⋁-is-lowerbound-of-upperbounds l⁺-is-bounded-family f h
--            where
--             lem : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                    (list-of-single-step-functions-family l⁺)
--             lem 𝟎       = f-ub₁
--             lem (suc i) x = pr₁ (list-of-single-step-functions-family l⁺ (suc i)) x ⊑⟪ 𝓔 ⟫[ ⋁-is-upperbound l-is-bounded-family (⌜ ≃-Lift 𝓥 _ ⌝ i) x ]
--                             pr₁ (β (l , l-is-bounded)) x ⊑⟪ 𝓔 ⟫[ f-ub₂ x ]
--                             pr₁ f x ∎⟪ 𝓔 ⟫
--             h : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                  (list-of-single-step-functions-small-family l⁺)
--             h i = lem (⌜ Lift-≃ 𝓥 _ ⌝ i)

--    module _
--            (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
--           where

--     _hom-⊑ₛ_ : DCPO[ 𝓓 , 𝓔 ⁻ ] → DCPO[ 𝓓 , 𝓔 ⁻ ] → 𝓥 ̇
--     _hom-⊑ₛ_ = pr₁ (locally-small-exponential-criterion 𝓓 (𝓔 ⁻)
--                    ∣ Bᴰ , βᴰ , compact-basis-is-basis 𝓓 βᴰ κᴰ ∣
--                    -- TODO: Add this as separate lemma?
--                    (locally-small-if-small-basis (𝓔 ⁻) βᴱ (compact-basis-is-basis (𝓔 ⁻) βᴱ κᴱ)))

--     -- TODO: Rename and clean up
--     test-family-index : 𝓥 ⊔ 𝓤 ⊔ 𝓣' ̇  -- We make this small later, using hom-⊑ₛ
--     test-family-index = Σ b ꞉ B , β b ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩  f

--     test-family : test-family-index → DCPO[ 𝓓 , 𝓔 ⁻ ]
--     test-family = β ∘ pr₁

--     sup-of-test-family : is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f test-family
--     sup-of-test-family = (ub , lb-of-ubs)
--      where
--       ub : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f test-family
--       ub i = pr₂ i
--       lb-of-ubs : is-lowerbound-of-upperbounds
--                    (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f test-family
--       lb-of-ubs g g-is-ub = sup-is-lowerbound-of-upperbounds
--                              (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)))
--                              (sup-of-single-step-functions f) g
--                              foo
--        where
--         foo : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) g
--                (single-step-functions-below-function-family f)
--         foo (d , e , below-f) x =
--          pr₁ (⦅ βᴰ d ⇒ βᴱ e ⦆[ d̅s-are-compact [ d , e ] 𝟎 ]) x ⊑⟪ 𝓔 ⟫[ ⋁-is-upperbound ccc (⌜ ≃-Lift 𝓥 _ ⌝ 𝟎) x ]
--          pr₁ (β ([ d , e ] , ∣ e , bbb ∣)) x ⊑⟪ 𝓔 ⟫[ g-is-ub (([ d , e ] , ∣ e , bbb ∣) , zzz) x ]
--          pr₁ g x ∎⟪ 𝓔 ⟫
--           where
--            bbb : list-of-single-step-functions-bounded-by [ d , e ] e -- TODO: Factor this out
--            bbb 𝟎 = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝⁻¹ (reflexivity (𝓔 ⁻) (βᴱ e))
--            ccc : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
--                    (list-of-single-step-functions-small-family [ d , e ])
--            ccc = (list-of-single-step-functions-small-family-is-bounded [ d , e ] ∣ e , bbb ∣)
--            zzz : underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β ([ d , e ] :: ∣ e :: bbb ∣)) f
--            zzz = ⋁-is-lowerbound-of-upperbounds ccc f yyy
--             where
--              ppp : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                     (list-of-single-step-functions-family [ d , e ])
--              ppp 𝟎 = rl-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
--                       (d̅s-are-compact [ d , e ] 𝟎) f) (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ below-f)
--              yyy : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                     (list-of-single-step-functions-small-family [ d , e ])
--              yyy i = ppp (⌜ Lift-≃ 𝓥 _ ⌝ i)

--     test-family-index-inhabited : ∥ Bᴰ ∥ → ∥ test-family-index ∥
--     test-family-index-inhabited = ∥∥-rec ∥∥-is-prop γ
--      where
--       γ : Bᴰ → ∥ test-family-index ∥
--       γ d = ∥∥-functor h (small-compact-basis-contains-all-compact-elements (𝓔 ⁻) βᴱ κᴱ (⊥ 𝓔) (⊥-is-compact 𝓔))
--        where
--         h : Σ (λ b → βᴱ b ≡ ⊥ 𝓔) → test-family-index
--         h (e :: refl) = (([ d , e ] , ∣ e , bbb ∣) , zzz)
--          where
--           bbb : list-of-single-step-functions-bounded-by [ d , e ] e -- TODO: Factor this out
--           bbb 𝟎 = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝⁻¹ (reflexivity (𝓔 ⁻) (βᴱ e))
--           ccc : is-bounded (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
--                   (list-of-single-step-functions-small-family [ d , e ])
--           ccc = (list-of-single-step-functions-small-family-is-bounded [ d , e ] ∣ e , bbb ∣)
--           zzz : underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β ([ d , e ] :: ∣ e :: bbb ∣)) f
--           zzz = ⋁-is-lowerbound-of-upperbounds ccc f yyy
--            where
--             ppp : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                    (list-of-single-step-functions-family [ d , e ])
--             ppp 𝟎 = rl-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
--                      (d̅s-are-compact [ d , e ] 𝟎) f) (⊥-is-least 𝓔 ([ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ (βᴰ d))) -- (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ below-f)
--             yyy : is-upperbound (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
--                    (list-of-single-step-functions-small-family [ d , e ])
--             yyy i = ppp (⌜ Lift-≃ 𝓥 _ ⌝ i)

--     test-family-semidirected : is-Semidirected (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) test-family
--     test-family-semidirected ((l , l-is-bounded) , l-below-f)
--                              ((k , k-is-bounded) , k-below-f) = {!!}
--      where
--       {- l++k : Vec (Bᴰ × Bᴱ) (n ∔ m)
--       l++k = l ++ k -}
--       l++k : List (Bᴰ × Bᴱ)
--       l++k = (length l ∔ length k , pr₂ l ++ pr₂ k)
--       l++k-is-bounded : list-of-single-step-functions-is-bounded l++k
--       l++k-is-bounded = ∥∥-rec₂ ∃-is-prop {!!} l-is-bounded k-is-bounded
--        where
--         {-

--         The problem is that while we have eˡ and eᵏ bounding l and k, which are
--         both bounded by f, the functions (λ _ → eˡ) and (λ _ → eᵏ) are not
--         necessarily bounded by f.

--         -}
--         {-
--         h : (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l e)
--           → (Σ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by k e)
--           → (∃ e ꞉ Bᴱ , list-of-single-step-functions-bounded-by l++k e)
--         h = {!!} -} {- (eˡ , eˡ-ub) (eᵏ , eᵏ-ub) =
--          ∥∥-functor {!!}
--                     (small-compact-basis-contains-all-compact-elements (𝓔 ⁻) βᴱ κᴱ y y-is-compact)
--           where
--            y : ⟪ 𝓔 ⟫
--            y = is-bounded-complete.⋁ 𝓔-bounded-complete {!!}
--            y-is-compact : {!!}
--            y-is-compact = {!!} -}
--       l++k-below-f : β (l++k , l++k-is-bounded) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
--       l++k-below-f = {!!} -- TODO: Prove a general lemma on (β l++k)

--       -- list-of-single-step-functions-bounded-by

-- \end{code}
