Tom de Jong, 4 & 5 April 2022.

Set Replacement is derivable from the existence of quotients in the
presence of propositional truncations or function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Quotient.GivesSetReplacement where

open import MLTT.Spartan

open import Quotient.Type
open import Quotient.GivesPropTrunc

open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons

module _
        (sq : set-quotients-exist)
        (pt : propositional-truncations-exist)
       where

 open general-set-quotients-exist sq
 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 module set-replacement-construction
         {X : 𝓤 ̇ }
         {Y : 𝓦 ̇ }
         (f : X → Y)
         (Y-is-loc-small : Y is-locally 𝓥 small)
         (Y-is-set : is-set Y)
        where

  _≈_ : X → X → 𝓦 ̇
  x ≈ x' = f x ＝ f x'

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued x x' = Y-is-set

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive x = refl

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric x x' p = p ⁻¹

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive _ _ _ p q = p ∙ q

  ≈-is-equiv-rel : is-equiv-relation _≈_
  ≈-is-equiv-rel = ≈-is-prop-valued , ≈-is-reflexive  ,
                   ≈-is-symmetric   , ≈-is-transitive

 \end{code}

 Using that Y is locally 𝓥 small, we resize _≈_ to a 𝓥-valued equivalence
 relation.

 \begin{code}

  _≈⁻_ : X → X → 𝓥 ̇
  x ≈⁻ x' = pr₁ (Y-is-loc-small (f x) (f x'))

  ≈⁻-≃-≈ : {x x' : X} → x ≈⁻ x' ≃ x ≈ x'
  ≈⁻-≃-≈ {x} {x'} = pr₂ (Y-is-loc-small (f x) (f x'))

  ≈⁻-is-prop-valued : is-prop-valued _≈⁻_
  ≈⁻-is-prop-valued x x' = equiv-to-prop ≈⁻-≃-≈ (≈-is-prop-valued x x')

  ≈⁻-is-reflexive : reflexive _≈⁻_
  ≈⁻-is-reflexive x = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-reflexive x)

  ≈⁻-is-symmetric : symmetric _≈⁻_
  ≈⁻-is-symmetric x x' p = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-symmetric x x' (⌜ ≈⁻-≃-≈ ⌝ p))

  ≈⁻-is-transitive : transitive _≈⁻_
  ≈⁻-is-transitive x x' x'' p q =
   ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-transitive x x' x'' (⌜ ≈⁻-≃-≈ ⌝ p) (⌜ ≈⁻-≃-≈ ⌝ q))

  ≈⁻-is-equiv-rel : is-equiv-relation _≈⁻_
  ≈⁻-is-equiv-rel = ≈⁻-is-prop-valued , ≈⁻-is-reflexive  ,
                    ≈⁻-is-symmetric   , ≈⁻-is-transitive

  ≋ : EqRel X
  ≋ = _≈_ , ≈-is-equiv-rel

  X/≈ : 𝓤 ⊔ 𝓦 ̇
  X/≈ = (X / ≋)

  X/≈⁻ : 𝓤 ⊔ 𝓥 ̇
  X/≈⁻ = (X / (_≈⁻_ , ≈⁻-is-equiv-rel))

  [_] : X → X/≈
  [_] = η/ ≋

  X/≈-≃-X/≈⁻ : X/≈ ≃ X/≈⁻
  X/≈-≃-X/≈⁻ = quotients-equivalent X ≋ (_≈⁻_ , ≈⁻-is-equiv-rel)
                                        (⌜ ≈⁻-≃-≈ ⌝⁻¹ , ⌜ ≈⁻-≃-≈ ⌝)

 \end{code}

 We now proceed to show that X/≈ and image f are equivalent types.

 \begin{code}

  corestriction-respects-≈ : {x x' : X}
                           → x ≈ x'
                           → corestriction f x ＝ corestriction f x'
  corestriction-respects-≈ =
   to-subtype-＝ (λ y → being-in-the-image-is-prop y f)

  quotient-to-image : X/≈ → image f
  quotient-to-image = mediating-map/ ≋ (image-is-set f Y-is-set)
                       (corestriction f) (corestriction-respects-≈)

  image-to-quotient' : (y : image f)
                     → Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ＝ q) × (f x ＝ pr₁ y)
  image-to-quotient' (y , p) = ∥∥-rec prp r p
   where
    r : (Σ x ꞉ X , f x ＝ y)
      → (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ＝ q) × (f x ＝ y))
    r (x , e) = [ x ] , ∣ x , refl , e ∣
    prp : is-prop (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ＝ q) × (f x ＝ y))
    prp (q , u) (q' , u') = to-subtype-＝ (λ _ → ∃-is-prop)
                                         (∥∥-rec₂ (/-is-set ≋) γ u u')
     where
      γ : (Σ x  ꞉ X , ([ x  ] ＝ q ) × (f x  ＝ y))
        → (Σ x' ꞉ X , ([ x' ] ＝ q') × (f x' ＝ y))
        → q ＝ q'
      γ (x , refl , e) (x' , refl , refl) = η/-identifies-related-points ≋ e

  image-to-quotient : image f → X/≈
  image-to-quotient y = pr₁ (image-to-quotient' y)

  image-to-quotient-lemma : (x : X)
                          → image-to-quotient (corestriction f x) ＝ [ x ]
  image-to-quotient-lemma x = ∥∥-rec (/-is-set ≋) γ t
   where
    q : X/≈
    q = image-to-quotient (corestriction f x)
    t : ∃ x' ꞉ X , ([ x' ] ＝ q) × (f x' ＝ f x)
    t = pr₂ (image-to-quotient' (corestriction f x))
    γ : (Σ x' ꞉ X , ([ x' ] ＝ q) × (f x' ＝ f x))
      → q ＝ [ x ]
    γ (x' , u , v) =   q    ＝⟨ u ⁻¹ ⟩
                     [ x' ] ＝⟨ η/-identifies-related-points ≋ v ⟩
                     [ x  ] ∎

  image-≃-quotient : image f ≃ X/≈
  image-≃-quotient = qinveq ϕ (ψ , ρ , σ)
   where
    ϕ : image f → X/≈
    ϕ = image-to-quotient
    ψ : X/≈ → image f
    ψ = quotient-to-image
    τ : (x : X) → ψ [ x ] ＝ corestriction f x
    τ = universality-triangle/ ≋ (image-is-set f Y-is-set)
                               (corestriction f)
                               corestriction-respects-≈
    σ : ϕ ∘ ψ ∼ id
    σ = /-induction ≋ (λ x' → /-is-set ≋) γ
     where
      γ : (x : X) → ϕ (ψ [ x ]) ＝ [ x ]
      γ x = ϕ (ψ [ x ])            ＝⟨ ap ϕ (τ x)                ⟩
            ϕ (corestriction f x ) ＝⟨ image-to-quotient-lemma x ⟩
            [ x ]                  ∎
    ρ : ψ ∘ ϕ ∼ id
    ρ (y , p) = ∥∥-rec (image-is-set f Y-is-set) γ p
     where
      γ : (Σ x ꞉ X , f x ＝ y) → ψ (ϕ (y , p)) ＝ (y , p)
      γ (x , refl) = ψ (ϕ (f x , p))           ＝⟨ ⦅1⦆ ⟩
                     ψ (ϕ (corestriction f x)) ＝⟨ ⦅2⦆ ⟩
                     ψ [ x ]                   ＝⟨ ⦅3⦆ ⟩
                     corestriction f x         ＝⟨ ⦅4⦆ ⟩
                     (f x , p)                 ∎
       where
        ⦅4⦆ = to-subtype-＝ (λ y → being-in-the-image-is-prop y f) refl
        ⦅1⦆ = ap (ψ ∘ ϕ) (⦅4⦆ ⁻¹)
        ⦅2⦆ = ap ψ (image-to-quotient-lemma x)
        ⦅3⦆ = τ x

 set-replacement-from-set-quotients-and-prop-trunc : Set-Replacement pt
 set-replacement-from-set-quotients-and-prop-trunc
  {𝓦} {𝓣} {𝓤} {𝓥} {X} {Y} f X-is-small Y-is-loc-small Y-is-set = X/≈⁻ , ≃-sym e
  where
   X' : 𝓤 ̇
   X' = pr₁ X-is-small
   φ : X' ≃ X
   φ = pr₂ X-is-small
   f' : X' → Y
   f' = f ∘ ⌜ φ ⌝
   open set-replacement-construction f' Y-is-loc-small Y-is-set
   open import UF.EquivalenceExamples
   e = image f  ≃⟨ Σ-cong (λ y → ∥∥-cong pt (h y)) ⟩
       image f' ≃⟨ image-≃-quotient ⟩
       X/≈      ≃⟨ X/≈-≃-X/≈⁻       ⟩
       X/≈⁻     ■
    where
     h : (y : Y) → (Σ x ꞉ X , f x ＝ y) ≃ (Σ x' ꞉ X' , f' x' ＝ y)
     h y = ≃-sym (Σ-change-of-variable (λ x → f x ＝ y) ⌜ φ ⌝ (⌜⌝-is-equiv φ))


\end{code}

End of anonymous module assuming set-quotients-exist and
propositional-truncations-exist.

\begin{code}

set-replacement-from-set-quotients-and-funext
 : (sq : set-quotients-exist)
   (fe : Fun-Ext)
 → Set-Replacement (propositional-truncations-from-set-quotients sq fe)
set-replacement-from-set-quotients-and-funext sq fe =
 set-replacement-from-set-quotients-and-prop-trunc sq
  (propositional-truncations-from-set-quotients sq fe)

\end{code}
