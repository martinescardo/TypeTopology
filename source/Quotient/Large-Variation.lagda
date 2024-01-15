Martin Escardo and Tom de Jong, October 2021

Modified from Quotient.Large to add the parameter F.

We use F to control the universe where propositional truncations live.
For more comments and explanations, see the original files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Powerset
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import UF.PropTrunc-Variation
open import UF.ImageAndSurjection-Variation

module Quotient.Large-Variation
        (F   : Universe → Universe)
        (pt  : propositional-truncations-exist F)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

module quotient
       {𝓤 𝓥 : Universe}
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-prop-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open PropositionalTruncation F pt
 open ImageAndSurjection F pt

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = x ≈ y , ≈p x y

 X/≈ : F (𝓤 ⊔ (𝓥 ⁺)) ⊔ 𝓤 ⊔ (𝓥 ⁺) ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
                (powersets-are-sets'' fe fe pe)
                ∥∥-is-prop

 η : X → X/≈
 η = corestriction equiv-rel

 η-surjection : is-surjection η
 η-surjection = corestriction-is-surjection equiv-rel

 quotient-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
                    → ((x' : X/≈) → is-prop (P x'))
                    → ((x : X) → P (η x))
                    → (x' : X/≈) → P x'
 quotient-induction = surjection-induction η η-surjection

 η-equiv-equal : {x y : X} → x ≈ y → η x ＝ η y
 η-equiv-equal {x} {y} e =
   to-Σ-＝ (dfunext fe
          (λ z → to-Σ-＝ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                         being-prop-is-prop fe _ _)) ,
       ∥∥-is-prop _ _)

 η-equal-equiv : {x y : X} → η x ＝ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ＝ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ＝ (x ≈ y)
     a = ap (λ - → pr₁ (- y)) (q ⁻¹)
     b : (y ≈ y) → (x ≈ y)
     b = Idtofun a

 universal-property : ∀ {𝓦} (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ＝ f x')
                    → ∃! f' ꞉ ( X/≈ → A), f' ∘ η ＝ f
 universal-property {𝓦} A iss f pr = ic
  where
   B : (x' : X/≈) → F (F (𝓥 ⁺ ⊔ 𝓤) ⊔ 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦) ⊔ 𝓦 ̇
   B x' = (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ＝ x') × (f x ＝ a))

   φ : (x' : X/≈) → is-prop (B x')
   φ = quotient-induction _ γ induction-step
     where
      induction-step : (y : X) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ＝ η y) × (f x ＝ a))
      induction-step x (a , d) (b , e) = to-Σ-＝ (p , ∥∥-is-prop _ _)
       where
        h : (Σ x' ꞉ X , (η x' ＝ η x) × (f x' ＝ a))
          → (Σ y' ꞉ X , (η y' ＝ η x) × (f y' ＝ b))
          → a ＝ b
        h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ pr (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

        p : a ＝ b
        p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

      γ : (x' : X/≈) → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)))
      γ x' = being-prop-is-prop fe

   k : (x' : X/≈) → B x'
   k = quotient-induction _ φ induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ＝ f
   r = dfunext fe h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))) → f' (η y) ＝ f y
     j y (x , p , q) = q ⁻¹ ∙ pr (η-equal-equiv p)

     h : (y : X) → f' (η y) ＝ f y
     h y = ∥∥-rec iss (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ＝ f) → (f' , r) ＝ σ
   c (f'' , s) = to-Σ-＝ (t , v)
    where
     w : ∀ x → f' (η x) ＝ f'' (η x)
     w = happly (r ∙ s ⁻¹)

     t : f' ＝ f''
     t = dfunext fe (quotient-induction _ (λ _ → iss) w)

     u : f'' ∘ η ＝ f
     u = transport (λ - → - ∘ η ＝ f) t r

     v : u ＝ s
     v = Π-is-set fe (λ _ → iss) u s

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ＝ f
   ic = (f' , r) , c

\end{code}
