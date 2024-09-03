Tom de Jong, 3 June 2022

The poset reflection of a preorder, using (large) set quotients as constructed
in Quotient.Large.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier

module OrderedTypes.PosetReflection
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Quotient.Type
open import Quotient.Large pt fe pe
open import UF.Base hiding (_≈_)
open import UF.ImageAndSurjection pt
open import UF.Subsingletons-FunExt

open general-set-quotients-exist large-set-quotients
open extending-relations-to-quotient fe pe

module poset-reflection
        (X : 𝓤 ̇ )
        (_≲_ : X → X → 𝓣 ̇ )
        (≲-is-prop-valued : (x y : X) → is-prop (x ≲ y))
        (≲-is-reflexive : (x : X) → x ≲ x)
        (≲-is-transitive : (x y z : X) → x ≲ y → y ≲ z → x ≲ z)
       where

 private
  _≲Ω_ : X → X → Ω 𝓣
  x ≲Ω y = x ≲ y , ≲-is-prop-valued x y

 _≈_ : X → X → 𝓣 ̇
 x ≈ y = x ≲ y × y ≲ x

 ≈-is-equiv-rel : is-equiv-relation _≈_
 ≈-is-equiv-rel = (λ x y → ×-is-prop (≲-is-prop-valued x y)
                                     (≲-is-prop-valued y x))
                , (λ x → ≲-is-reflexive x , ≲-is-reflexive x)
                , (λ x y (k , l) → l , k)
                , (λ x y z (k , l) (u , v) → (≲-is-transitive x y z k u)
                                           , (≲-is-transitive z y x v l))

 ≋ : EqRel X
 ≋ = _≈_ , ≈-is-equiv-rel

 private
  ≲-congruence : {x y x' y' : X} → x ≈ x' → y ≈ y' → x ≲Ω y ＝ x' ≲Ω y'
  ≲-congruence {x} {y} {x'} {y'} (k , l) (u , v) =
   Ω-extensionality pe fe
    (λ m → ≲-is-transitive x' x y' l
            (≲-is-transitive x y y' m u))
    (λ m → ≲-is-transitive x x' y k
            (≲-is-transitive x' y' y m v))

  _≤Ω_ : X / ≋ → X / ≋ → Ω 𝓣
  _≤Ω_ = extension-rel₂ ≋ (λ x y → x ≲Ω y) ≲-congruence

 poset-reflection-carrier : 𝓣 ⁺ ⊔ 𝓤 ̇
 poset-reflection-carrier = X / ≋

 poset-reflection-is-set : is-set poset-reflection-carrier
 poset-reflection-is-set = /-is-set ≋

 _≤_ : X / ≋ → X / ≋ → 𝓣 ̇
 x' ≤ y' = (x' ≤Ω y') holds

 ≤-is-prop-valued : (x' y' : X / ≋) → is-prop (x' ≤ y')
 ≤-is-prop-valued x' y' = holds-is-prop (x' ≤Ω y')

 η : X → X / ≋
 η = η/ ≋

 η-is-surjection : is-surjection η
 η-is-surjection = η/-is-surjection ≋ pt

 η-reflects-order : {x y : X} → η x ≤ η y → x ≲ y
 η-reflects-order {x} {y} =
  Idtofun (ap pr₁ (extension-rel-triangle₂ ≋ _≲Ω_ ≲-congruence x y))

 η-preserves-order : {x y : X} → x ≲ y → η x ≤ η y
 η-preserves-order {x} {y} =
  Idtofun (ap pr₁ ((extension-rel-triangle₂ ≋ _≲Ω_ ≲-congruence x y) ⁻¹))

 η-↔-order : {x y : X} → x ≲ y ↔ η x ≤ η y
 η-↔-order = η-preserves-order , η-reflects-order

 ≤-is-reflexive : (x' : X / ≋) → x' ≤ x'
 ≤-is-reflexive = /-induction ≋ (λ x' → ≤-is-prop-valued x' x')
                                (λ x → η-preserves-order (≲-is-reflexive x))

 ≤-is-transitive : (x' y' z' : X / ≋) → x' ≤ y' → y' ≤ z' → x' ≤ z'
 ≤-is-transitive =
  /-induction₃ fe ≋ (λ x' y' z' → Π₂-is-prop fe (λ _ _ → ≤-is-prop-valued x' z'))
                    (λ x y z k l → η-preserves-order
                                    (≲-is-transitive x y z
                                      (η-reflects-order k)
                                      (η-reflects-order l)))

 ≤-is-antisymmetric : (x' y' : X / ≋) → x' ≤ y' → y' ≤ x' → x' ＝ y'
 ≤-is-antisymmetric =
  /-induction₂ fe ≋ (λ x' q → Π₂-is-prop fe (λ _ _ → /-is-set ≋))
                    (λ x y k l → η/-identifies-related-points ≋
                                  ( η-reflects-order k
                                  , η-reflects-order l))

\end{code}

The requirement that Q is a set actually follows from the order assumptions, but
it is convenient to assume it (for now) anyway.

\begin{code}

 universal-property :
    {Q : 𝓤' ̇ } (_⊑_ : Q → Q → 𝓣' ̇ )
  → is-set Q
  → ((p q : Q) → is-prop (p ⊑ q))
  → ((q : Q) → q ⊑ q)
  → ((p q r : Q) → p ⊑ q → q ⊑ r → p ⊑ r)
  → ((p q : Q) → p ⊑ q → q ⊑ p → p ＝ q)
  → (f : X → Q)
  → ((x y : X) → x ≲ y → f x ⊑ f y)
  → ∃! f̃ ꞉ (X / ≋ → Q) , ((x' y' : X / ≋) → x' ≤ y' → f̃ x' ⊑ f̃ y')
                       × (f̃ ∘ η ∼ f)
 universal-property {𝓤'} {𝓣'} {Q} _⊑_ Q-is-set ⊑-prop ⊑-refl ⊑-trans
                                               ⊑-antisym f f-mon =
  (f̃ , f̃-mon , f̃-eq) , σ
   where
    μ : ∃! f̃ ꞉ (X / ≋ → Q), f̃ ∘ η ∼ f
    μ = /-universality ≋
         Q-is-set f (λ {x} {y} (k , l) → ⊑-antisym (f x) (f y)
                                          (f-mon x y k) (f-mon y x l))
    f̃ : X / ≋ → Q
    f̃ = ∃!-witness μ
    f̃-eq : f̃ ∘ η ∼ f
    f̃-eq = ∃!-is-witness μ
    f̃-mon : (x' y' : X / ≋) → x' ≤ y' → f̃ x' ⊑ f̃ y'
    f̃-mon = /-induction₂ fe ≋
             (λ x' y' → Π-is-prop fe (λ _ → ⊑-prop (f̃ x') (f̃ y')))
             (λ x y l → transport₂ _⊑_ ((f̃-eq x) ⁻¹) ((f̃-eq y) ⁻¹)
                         (f-mon x y (η-reflects-order l)))
    f̃-is-unique : (g : X / ≋ → Q)
                → ((x' y' : X / ≋) → x' ≤ y' → g x' ⊑ g y')
                → (g ∘ η ∼ f)
                → f̃ ∼ g
    f̃-is-unique g g-mon g-eq = happly e
     where
      e : f̃ ＝ g
      e = ap pr₁ (∃!-uniqueness' μ (g , g-eq))
    σ : is-central (Σ g ꞉ (X / ≋ → Q)
                        , ((x' y' : X / ≋) → x' ≤ y' → g x' ⊑ g y')
                        × g ∘ η ∼ f)
                   (f̃ , f̃-mon , f̃-eq)
    σ (g , g-mon , g-eq) =
     to-subtype-＝ (λ h → ×-is-prop
                          (Π₃-is-prop fe (λ x' y' _ → ⊑-prop (h x') (h y')))
                          (Π-is-prop fe (λ _ → Q-is-set)))
                  (dfunext fe (f̃-is-unique g g-mon g-eq))

\end{code}
