Tom de Jong, late February, early March 2022.

We use single step functions to construct a small compact basis on the
exponential of dcpos Eᴰ where D and E have small compact bases and E is
sup-complete. This is used in DomainTheory.Bilimits.Dinfinity.lagda to show that
Scott's D∞ has a small compact basis, and hence is algebraic.

We can prove a similar result for dcpos with a small bases that are not
necessarily algebraic, but the formalization of this argument is not entirely
complete, as it depends on a lemma on the sup-completeness of the ideal
completion, see below for details.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}
-- The flag --lossy-unification roughly reduces the timechecking
-- time by 50%.

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

open import UF.Subsingletons

module DomainTheory.BasesAndContinuity.StepFunctions
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt hiding (_∨_)

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
open import DomainTheory.Basics.Exponential pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥 hiding (⊥ ; ⊥-is-least)
open import DomainTheory.Basics.SupComplete pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

\end{code}

We introduce single step functions to show that sup-complete algebraic dcpos are
closed under exponentials, cf. Exercise II-2.31 in "Continuous Lattices and
Domains" by Gierz et al.

Classically, a single step function
⦅ d ⇒ e ⦆ is given like this:
 x ↦ e if d ⊑ x
     ⊥ otherwise

Constructively, we can't expect to make this case distinction, so we define
single step functions using subsingleton suprema instead.

\begin{code}

module _
        (𝓓 : DCPO {𝓤}  {𝓣})
        (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
        (𝓓-is-locally-small : is-locally-small 𝓓)
       where

 open is-locally-small 𝓓-is-locally-small

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

 below-single-step-function-criterion : (d : ⟨ 𝓓 ⟩) (e : ⟪ 𝓔 ⟫) (κ : is-compact 𝓓 d)
                                        (f : DCPO[ 𝓓 , 𝓔 ⁻ ])
                                      → ⦅ d ⇒ e ⦆[ κ ] ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ f
                                      ↔ e ⊑⟪ 𝓔 ⟫ [ 𝓓 , 𝓔 ⁻ ]⟨ f ⟩ d
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

\end{code}

We now work towards constructing a small compact basis for the exponential
𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻). We start with a family of single step functions that we will
later directify by taking finite joins.

\begin{code}

 module _
         (Bᴰ Bᴱ : 𝓥 ̇ )
         (βᴰ : Bᴰ → ⟨ 𝓓 ⟩)
         (βᴱ : Bᴱ → ⟪ 𝓔 ⟫)
         (κᴰ : is-small-compact-basis 𝓓     βᴰ)
         (κᴱ : is-small-compact-basis (𝓔 ⁻) βᴱ)
        where

  single-step-functions : Bᴰ × Bᴱ → DCPO[ 𝓓 , 𝓔 ⁻ ]
  single-step-functions (d , e) = ⦅ βᴰ d ⇒ βᴱ e ⦆[ basis-is-compact d ]
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
      (Σ p ꞉ (Bᴰ × Bᴱ) , single-step-functions p ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ 𝕗)
    → DCPO[ 𝓓 , 𝓔 ⁻ ]
   single-step-functions-below-function = single-step-functions ∘ pr₁

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
     lb-of-ubs 𝕘@(g , _) g-is-ub x = fx-below-gx
      where
       module _ where
        open is-small-compact-basis κᴱ
        claim₁ : (d : Bᴰ) (e : Bᴱ) → e ⊑ᴮₛ f (βᴰ d) → βᴱ e ⊑⟪ 𝓔 ⟫ g (βᴰ d)
        claim₁ d e u =
         lr-implication (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                          (is-small-compact-basis.basis-is-compact κᴰ d) 𝕘)
                          (g-is-ub ((d , e) , v))
          where
           v : single-step-functions (d , e) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩ 𝕗
           v = rl-implication
                (below-single-step-function-criterion (βᴰ d) (βᴱ e)
                  (is-small-compact-basis.basis-is-compact κᴰ d) 𝕗)
                (⊑ᴮₛ-to-⊑ᴮ u)
        claim₂ : (d : Bᴰ) → f (βᴰ d) ⊑⟪ 𝓔 ⟫ g (βᴰ d)
        claim₂ d = f (βᴰ d)                             ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
                   ∐ (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d))) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
                   g (βᴰ d)                             ∎⟪ 𝓔 ⟫
         where
          ⦅1⦆ = ↓ᴮₛ-∐-⊒ (f (βᴰ d))
          ⦅2⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) (↓ᴮₛ-is-directed (f (βᴰ d)))
                 (g (βᴰ d)) (λ (e , v) → claim₁ d e v)

       open is-small-compact-basis κᴰ
       δ : is-Directed 𝓓 (↓-inclusionₛ x)
       δ = ↓ᴮₛ-is-directed x
       ε : is-Directed (𝓔 ⁻) (f ∘ ↓-inclusionₛ x)
       ε = image-is-directed' 𝓓 (𝓔 ⁻) 𝕗 δ

       fx-below-gx : f x ⊑⟪ 𝓔 ⟫ g x
       fx-below-gx = f x       ⊑⟪ 𝓔 ⟫[ ⦅1⦆ ]
                     f (∐ 𝓓 δ) ⊑⟪ 𝓔 ⟫[ ⦅2⦆ ]
                     ∐ (𝓔 ⁻) ε ⊑⟪ 𝓔 ⟫[ ⦅3⦆ ]
                     g x       ∎⟪ 𝓔 ⟫
        where
         ⦅1⦆ = ＝-to-⊒ (𝓔 ⁻) (ap f (↓ᴮₛ-∐-＝ x))
         ⦅2⦆ = continuous-∐-⊑ 𝓓 (𝓔 ⁻) 𝕗 δ
         ⦅3⦆ = ∐-is-lowerbound-of-upperbounds (𝓔 ⁻) ε (g x) γ
          where
           γ : is-upperbound (underlying-order (𝓔 ⁻)) (g x) (f ∘ ↓-inclusionₛ x)
           γ (d , u) = f (βᴰ d) ⊑⟪ 𝓔 ⟫[ claim₂ d ]
                       g (βᴰ d) ⊑⟪ 𝓔 ⟫[ v        ]
                       g x      ∎⟪ 𝓔 ⟫
            where
             v = monotone-if-continuous 𝓓 (𝓔 ⁻) 𝕘 (βᴰ d) x (⊑ᴮₛ-to-⊑ᴮ u)

\end{code}

Now we are in position to show that the exponential has a small compact basis.

\begin{code}

  module _
          (𝓔-is-sup-complete : is-sup-complete (𝓔 ⁻))
         where

   private
    exp-is-sup-complete : is-sup-complete (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
    exp-is-sup-complete = exponential-is-sup-complete 𝓓 (𝓔 ⁻) 𝓔-is-sup-complete

   open sup-complete-dcpo (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) exp-is-sup-complete

   private
    B : 𝓥 ̇
    B = domain (directify single-step-functions)
    β : B → DCPO[ 𝓓 , 𝓔 ⁻ ]
    β = directify single-step-functions

   exponential-has-small-compact-basis : Prop-Ext
                                       → is-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β
   exponential-has-small-compact-basis pe =
    record
     { basis-is-compact = ⦅1⦆
     ; ⊑ᴮ-is-small      = ⦅2⦆
     ; ↓ᴮ-is-directed   = ⦅3⦆
     ; ↓ᴮ-is-sup        = ⦅4⦆
     }
     where
      ⦅1⦆ : (b : B) → is-compact (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (β b)
      ⦅1⦆ = directify-is-compact single-step-functions
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
         locally-small-exponential-criterion pe 𝓓 (𝓔 ⁻)
          ∣ Bᴰ , βᴰ , compact-basis-is-basis 𝓓 βᴰ κᴰ ∣
          (locally-small-if-small-compact-basis (𝓔 ⁻) βᴱ κᴱ)
      ⦅3⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩)
          → is-Directed (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) (↓-inclusion (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β f)
      ⦅3⦆ f = directify-↓-is-directed single-step-functions {f}
      ⦅4⦆ : (f : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻) ⟩)
          → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))) f
             (↓-inclusion (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻)) β f)
      ⦅4⦆ (f , f-is-cts) =
       directify-↓-sup single-step-functions {f , f-is-cts}
        (single-step-functions-below-function-sup 𝓔-is-sup-complete
        f f-is-cts)

   exponential-has-specified-small-compact-basis : Prop-Ext
    → has-specified-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
   exponential-has-specified-small-compact-basis pe =
    (B , β , exponential-has-small-compact-basis pe)

   exponential-is-structurally-algebraic : Prop-Ext
                                         → structurally-algebraic (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
   exponential-is-structurally-algebraic pe =
    structurally-algebraic-if-specified-small-compact-basis (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
     (exponential-has-specified-small-compact-basis pe)

   exponential-is-algebraic : Prop-Ext → is-algebraic-dcpo (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⁻))
   exponential-is-algebraic pe = ∣ exponential-is-structurally-algebraic pe ∣

\end{code}

The fact that sup-complete (algebraic) dcpos with small compact bases are closed
under exponentials can be used to show that the same holds for sup-complete
(continuous) dcpos with small bases.

The proof outline, which Martín Escardó explained to me, is as follows:

Start with dcpos 𝓓 and 𝓔 with small bases βᴰ : Bᴰ → 𝓓 and βᴱ : Bᴱ → 𝓔. Then
𝓓 and 𝓔 are continuous retracts of dcpos 𝓓' and 𝓔' respectively both with small
compact bases, using the ideal completions of the bases.

Moreover, these retracts induce a continuous retract of the exponentials:
(𝓓 ⟹ᵈᶜᵖᵒ 𝓔) is a continuous retract of (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
and the latter is algebraic with a small compact basis by the above. Finally, we
can use the continuous retract to give a small basis on (𝓓 ⟹ᵈᶜᵖᵒ 𝓔).

NB: The above proof outline depends on the fact that 𝓔' and (hence)
(𝓓' ⟹ᵈᶜᵖᵒ 𝓔') are sup-complete. This can be shown by using the concrete
definition of 𝓔' as the ideal completion of βᴱ. This step has not been
formalized (yet), but all the other steps in the outline have.

TODO: Formalize the proof that Idl(βᴱ,⊑) is is sup-complete. It looks like it
will be helpful to prove separately that we can close bases under finite joins.

\begin{code}

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        {Bᴰ Bᴱ : 𝓥 ̇ }
        (βᴰ : Bᴰ → ⟨ 𝓓 ⟩)
        (βᴱ : Bᴱ → ⟨ 𝓔 ⟩)
        (βᴰ-is-small-basis : is-small-basis 𝓓 βᴰ)
        (βᴱ-is-small-basis : is-small-basis 𝓔 βᴱ)
        (𝓔-is-sup-complete : is-sup-complete 𝓔)
       where

 open import DomainTheory.IdealCompletion.Retracts pt fe pe 𝓥

 private
  module _ where
   open Idl-continuous-retract-of-algebraic 𝓓 βᴰ βᴰ-is-small-basis
   𝓓' : DCPO {𝓥 ⁺} {𝓥}
   𝓓' = Idl-DCPO
   𝓓-continuous-retract-of-𝓓' : 𝓓 continuous-retract-of 𝓓'
   𝓓-continuous-retract-of-𝓓' = Idl-continuous-retract
  module _ where
   open Idl-continuous-retract-of-algebraic 𝓔 βᴱ βᴱ-is-small-basis
   𝓔' : DCPO {𝓥 ⁺} {𝓥}
   𝓔' = Idl-DCPO
   𝓔-continuous-retract-of-𝓔' : 𝓔 continuous-retract-of 𝓔'
   𝓔-continuous-retract-of-𝓔' = Idl-continuous-retract

  exp-continuous-retract : (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) continuous-retract-of (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
  exp-continuous-retract =
   record
    { s               = s
    ; r               = r
    ; s-section-of-r    = s-section-of-r
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
      rᴰ-sᴰ-equation = s-section-of-r
     module _ where
      open _continuous-retract-of_ 𝓔-continuous-retract-of-𝓔'
      sᴱ = s
      rᴱ = r
      sᴱ-is-cts = s-is-continuous
      rᴱ-is-cts = r-is-continuous
      rᴱ-sᴱ-equation = s-section-of-r
     s : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩ → ⟨ 𝓓' ⟹ᵈᶜᵖᵒ 𝓔' ⟩
     s f = DCPO-∘₃ 𝓓' 𝓓 𝓔 𝓔' (rᴰ , rᴰ-is-cts) f (sᴱ , sᴱ-is-cts)
     r : ⟨ 𝓓' ⟹ᵈᶜᵖᵒ 𝓔' ⟩ → ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩
     r g = DCPO-∘₃ 𝓓 𝓓' 𝓔' 𝓔 (sᴰ , sᴰ-is-cts) g (rᴱ , rᴱ-is-cts)
     s-section-of-r : r ∘ s ∼ id
     s-section-of-r (f , _) = to-continuous-function-＝ 𝓓 𝓔 γ
      where
       γ : rᴱ ∘ sᴱ ∘ f ∘ rᴰ ∘ sᴰ ∼ f
       γ x = (rᴱ ∘ sᴱ ∘ f ∘ rᴰ ∘ sᴰ) x ＝⟨ rᴱ-sᴱ-equation ((f ∘ rᴰ ∘ sᴰ) x) ⟩
             (f ∘ rᴰ ∘ sᴰ) x           ＝⟨ ap f (rᴰ-sᴰ-equation x) ⟩
             f x                       ∎
     s-is-cts : is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') s
     s-is-cts = DCPO-∘₃-is-continuous₂ 𝓓' 𝓓 𝓔 𝓔'
                 (rᴰ , rᴰ-is-cts) (sᴱ , sᴱ-is-cts)
     r-is-cts : is-continuous (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) r
     r-is-cts = DCPO-∘₃-is-continuous₂ 𝓓 𝓓' 𝓔' 𝓔
                 (sᴰ , sᴰ-is-cts) (rᴱ , rᴱ-is-cts)

\end{code}

Sup-completeness of 𝓔' is the only remaining hole in the formalization of the
argument outlined above.

\begin{code}

{- TODO
  𝓔'-is-sup-complete : is-sup-complete 𝓔'
  𝓔'-is-sup-complete = {!!}
-}

\end{code}

We assume sup-completeness of 𝓔' here to illustrate that the remainder of the
argument is fully formalized.

\begin{code}

  module _
          (𝓔'-is-sup-complete : is-sup-complete 𝓔')
         where

   open sup-complete-dcpo 𝓔' 𝓔'-is-sup-complete

   exp-has-small-compact-basis : has-specified-small-compact-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
   exp-has-small-compact-basis =
    exponential-has-specified-small-compact-basis 𝓓' (𝓔' , ⊥ , ⊥-is-least)
     (locally-small-if-small-compact-basis 𝓓' βᴰ' κᴰ')
     Bᴰ' Bᴱ' βᴰ' βᴱ' κᴰ' κᴱ' 𝓔'-is-sup-complete pe
      where
       module _ where
        open Idl-continuous-retract-of-algebraic 𝓓 βᴰ βᴰ-is-small-basis
        small-compact-basisᴰ' : has-specified-small-compact-basis 𝓓'
        small-compact-basisᴰ' = Idl-has-specified-small-compact-basis
                                 (λ _ → ⊑ᴮ-is-reflexive)
        Bᴰ' : 𝓥 ̇
        Bᴰ' = pr₁ small-compact-basisᴰ'
        βᴰ' : Bᴰ' → ⟨ 𝓓' ⟩
        βᴰ' = pr₁ (pr₂ small-compact-basisᴰ')
        κᴰ' : is-small-compact-basis 𝓓' βᴰ'
        κᴰ' = pr₂ (pr₂ small-compact-basisᴰ')
       module _ where
        open Idl-continuous-retract-of-algebraic 𝓔 βᴱ βᴱ-is-small-basis
        small-compact-basisᴱ' : has-specified-small-compact-basis 𝓔'
        small-compact-basisᴱ' = Idl-has-specified-small-compact-basis
                                 (λ _ → ⊑ᴮ-is-reflexive)
        Bᴱ' : 𝓥 ̇
        Bᴱ' = pr₁ small-compact-basisᴱ'
        βᴱ' : Bᴱ' → ⟨ 𝓔' ⟩
        βᴱ' = pr₁ (pr₂ small-compact-basisᴱ')
        κᴱ' : is-small-compact-basis 𝓔' βᴱ'
        κᴱ' = pr₂ (pr₂ small-compact-basisᴱ')

   exponential-has-small-basis : has-specified-small-basis (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
   exponential-has-small-basis = B , r ∘ β ,
    small-basis-from-continuous-retract (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
     exp-continuous-retract pe β (compact-basis-is-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') β κ)
    where
     open _continuous-retract-of_ exp-continuous-retract
     exp-small-compact-basis : has-specified-small-compact-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔')
     exp-small-compact-basis = exp-has-small-compact-basis
     B : 𝓥 ̇
     B = pr₁ exp-has-small-compact-basis
     β : B → DCPO[ 𝓓' , 𝓔' ]
     β = pr₁ (pr₂ exp-has-small-compact-basis)
     κ : is-small-compact-basis (𝓓' ⟹ᵈᶜᵖᵒ 𝓔') β
     κ = pr₂ (pr₂ exp-has-small-compact-basis)

\end{code}
