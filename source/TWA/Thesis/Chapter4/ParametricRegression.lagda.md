[⇐ Index](../html/TWA.Thesis.index.html)

# Parametric Regression

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import UF.FunExt
open import UF.Subsingletons
open import Quotient.Type
  using (is-prop-valued;is-equiv-relation;EqRel)
open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import NotionsOfDecidability.Complemented
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import UF.DiscreteAndSeparated
open import MLTT.Two-Properties
open import UF.SubtypeClassifier

open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter4.ParametricRegression (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe
open import TWA.Thesis.Chapter4.GlobalOptimisation fe

open import TWA.Closeness fe hiding (is-ultra;is-closeness)
```

## Regression as maximisation

```
invert-rel : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → X → 𝓥 ̇ )
invert-rel R x y = R y x

invert-rel' : {X : 𝓤 ̇ } → (X → X → ℕ → 𝓥 ̇ ) → (X → X → ℕ → 𝓥 ̇ )
invert-rel' R x y = R y x 

invert-preorder-is-preorder : {X : 𝓤 ̇ } → (_≤_ : X → X → 𝓥 ̇ )
                            → is-preorder _≤_
                            → let _≥_ = invert-rel _≤_ in
                              is-preorder _≥_
invert-preorder-is-preorder _≤_ (r' , t' , p') = r , t , p
 where
  r : reflexive (invert-rel _≤_)
  r x = r' x
  t : transitive (invert-rel _≤_)
  t x y z q r = t' z y x r q
  p : is-prop-valued (invert-rel _≤_)
  p x y = p' y x

invert-approx-order-is-approx-order
 : (X : ClosenessSpace 𝓤)
 → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓥' ̇ )
 → is-approx-order X _≤ⁿ_
 → let _≥ⁿ_ = invert-rel' _≤ⁿ_ in
   is-approx-order X _≥ⁿ_
invert-approx-order-is-approx-order X _≤ⁿ_ a'@(_ , d' , c') = l , d , c
 where
  l : (ϵ : ℕ) → is-linear-preorder (λ x y → invert-rel' _≤ⁿ_ x y ϵ)
  l ϵ = (≤ⁿ-refl X a' ϵ
      , (λ x y z x≤y y≤z → ≤ⁿ-trans X a' ϵ z y x y≤z x≤y)
      , (λ x y → ≤ⁿ-prop X a' ϵ y x))
      , (λ x y → ≤ⁿ-linear X a' ϵ y x)
  d : (ϵ : ℕ) (x y : ⟨ X ⟩) → is-decidable (invert-rel' _≤ⁿ_ x y ϵ)
  d ϵ x y = d' ϵ y x
  c : (ϵ : ℕ) (x y : ⟨ X ⟩) → C X ϵ x y → invert-rel' _≤ⁿ_ x y ϵ
  c ϵ x y Cxy = c' ϵ y x (C-sym X ϵ x y Cxy)

is_global-maximal : ℕ → {𝓤 𝓥 : Universe}
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                  → (f : X → Y) → X → 𝓦 ⊔ 𝓤  ̇ 
(is ϵ global-maximal) {𝓤} {𝓥} {X} _≤ⁿ_ f x₀
 = is ϵ global-minimal (invert-rel' _≤ⁿ_) f x₀

has_global-maximal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : 𝓥 ̇ }
                   → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                   → (f : X → Y) → (𝓦 ⊔ 𝓤) ̇ 
(has ϵ global-maximal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f
 = Σ ((is ϵ global-maximal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f)

global-max-ℕ∞ : (X : ClosenessSpace 𝓤) → ⟨ X ⟩
              → totally-bounded X 𝓤'
              → (f : ⟨ X ⟩ → ℕ∞)
              → f-ucontinuous X ℕ∞-ClosenessSpace f
              → (ϵ : ℕ)
              → (has ϵ global-maximal) ℕ∞-approx-lexicorder f
global-max-ℕ∞ X x₀ t f ϕ ϵ
 = global-opt X ℕ∞-ClosenessSpace x₀
     (invert-rel' ℕ∞-approx-lexicorder)
     (invert-approx-order-is-approx-order ℕ∞-ClosenessSpace
         ℕ∞-approx-lexicorder
         ℕ∞-approx-lexicorder-is-approx-order)
     ϵ f ϕ t

oracle-closeness' : (Y : PseudoClosenessSpace 𝓥)
                  → (𝓞 : ⟪ Y ⟫)
                  → (ϵ : ℕ)
                  → let c = pr₁ (pr₂ Y) in
                    (y₁ y₂ : ⟪ Y ⟫)
                  → C' Y ϵ y₁ y₂
                  → C' (ι ℕ∞-ClosenessSpace) ϵ (c 𝓞 y₁) (c 𝓞 y₂)
oracle-closeness' (_ , c , _ , c-sym , c-ult) 𝓞 ϵ y₁ y₂ Cϵy₁y₂ n n⊏ϵ
 = decidable-𝟚₁ (∼ⁿ-decidable (λ _ → 𝟚-is-discrete) _ _ (succ n))
       (λ k k<sn → C𝓞-eq k
                     (<-≤-trans k (succ n) ϵ k<sn (⊏-gives-< n ϵ n⊏ϵ))
                     (𝟚-possibilities (pr₁ (c 𝓞 y₁) k))
                     (𝟚-possibilities (pr₁ (c 𝓞 y₂) k)))
   where
    C𝓞-eq : (n : ℕ) → n < ϵ
          → let c𝓞y₁n = pr₁ (c 𝓞 y₁) n in
            let c𝓞y₂n = pr₁ (c 𝓞 y₂) n in
            (c𝓞y₁n ＝ ₀) + (c𝓞y₁n ＝ ₁)
          → (c𝓞y₂n ＝ ₀) + (c𝓞y₂n ＝ ₁)
          → c𝓞y₁n ＝ c𝓞y₂n
    C𝓞-eq n n<ϵ (inl c𝓞y₁＝₀) (inl c𝓞y₂＝₀) = c𝓞y₁＝₀ ∙ c𝓞y₂＝₀ ⁻¹
    C𝓞-eq n n<ϵ (inl c𝓞y₁＝₀) (inr c𝓞y₂＝₁)
     = 𝟘-elim (zero-is-not-one
         (c𝓞y₁＝₀ ⁻¹
         ∙ c-ult 𝓞 y₂ y₁ n
           (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] c𝓞y₂＝₁
             (ap (λ - → pr₁ - n) (c-sym y₂ y₁)
             ∙ Cϵy₁y₂ n (<-gives-⊏ n ϵ n<ϵ)))))
    C𝓞-eq n n<ϵ (inr c𝓞y₁＝₁) (inl c𝓞y₂＝₀)
     = 𝟘-elim (zero-is-not-one
         (c𝓞y₂＝₀ ⁻¹
         ∙ c-ult 𝓞 y₁ y₂ n
           (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] c𝓞y₁＝₁
             (Cϵy₁y₂ n (<-gives-⊏ n ϵ n<ϵ))))) 
    C𝓞-eq n n<ϵ (inr c𝓞y₁＝₁) (inr c𝓞y₂＝₁) = c𝓞y₁＝₁ ∙ c𝓞y₂＝₁ ⁻¹
  
oracle-closeness : (Y : PseudoClosenessSpace 𝓥)
             → (𝓞 : ⟪ Y ⟫)
             → let c = pr₁ (pr₂ Y) in
               f-ucontinuous' Y (ι ℕ∞-ClosenessSpace) (c 𝓞)
oracle-closeness Y 𝓞 ϵ = ϵ , oracle-closeness' Y 𝓞 ϵ
    
optimisation-convergence
       : (X : ClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
       → ⟨ X ⟩ → totally-bounded X 𝓤'
       → (M : ⟨ X ⟩ → ⟪ Y ⟫) (𝓞 : ⟪ Y ⟫)
       → f-ucontinuous' (ι X) Y M
       → let c = pr₁ (pr₂ Y) in
         (ϵ : ℕ)
       → (has ϵ global-maximal) ℕ∞-approx-lexicorder (λ x → c 𝓞 (M x))
optimisation-convergence X Y x₀ t M 𝓞 ϕᴹ
 = global-max-ℕ∞ X x₀ t (c 𝓞 ∘ M)
     (λ ϵ → pr₁ (ϕᴹ ϵ)
          , λ x₁ x₂ Cδᶜx₁x₂ → oracle-closeness' Y 𝓞 ϵ (M x₁) (M x₂)
                                (pr₂ (ϕᴹ ϵ) x₁ x₂ Cδᶜx₁x₂))
 where
  c : ⟪ Y ⟫ → ⟪ Y ⟫ → ℕ∞
  c = pr₁ (pr₂ Y)

regressor : (X : ClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥) → 𝓤 ⊔ 𝓥  ̇
regressor {𝓤} {𝓥} X Y
 = (M : ⟨ X ⟩ → ⟪ Y ⟫) → f-ucontinuous' (ι X) Y M → ⟪ Y ⟫ → ⟨ X ⟩

p-regressor : (X : ClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
            → (𝓔S : csearchable 𝓤₀ X)
            → (ε : ℕ) → regressor X Y
p-regressor {𝓤} {𝓥} X Y S ε M ϕᴹ 𝓞 = pr₁ (S ((p , d) , ϕ))
 where
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = C'Ω Y ε 𝓞 (M x)
  d : is-complemented (λ x → p x holds)
  d x = C'-decidable Y ε 𝓞 (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Cδx₁x₂ px₁
     = C'-trans Y ε 𝓞 (M x₁) (M x₂) px₁ (pr₂ (ϕᴹ ε) x₁ x₂ Cδx₁x₂)

s-imperfect-convergence
       : (X : ClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
       → (S : csearchable 𝓤₀ X)
       → (ε : ℕ)
       → (M : ⟨ X ⟩ → ⟪ Y ⟫) (ϕᴹ : f-ucontinuous' (ι X) Y M)
       → (Ψ : ⟪ Y ⟫ → ⟪ Y ⟫) (k : ⟨ X ⟩)
       → let
           𝓞 = M k
           Ψ𝓞 = Ψ 𝓞
           reg = p-regressor X Y S ε
           ω = M (reg M ϕᴹ Ψ𝓞)
         in (C' Y ε 𝓞 Ψ𝓞) → (C' Y ε 𝓞 ω)
s-imperfect-convergence X Y S ε M ϕᴹ Ψ k Cε𝓞Ψ𝓞
 = C'-trans Y ε 𝓞 Ψ𝓞 ω Cε𝓞Ψ𝓞
     (pr₂ (S ((p , d) , ϕ)) (k , C'-sym Y ε 𝓞 Ψ𝓞 Cε𝓞Ψ𝓞))
 where
  𝓞 = M k 
  Ψ𝓞 = Ψ 𝓞
  reg = p-regressor X Y S ε
  ω = M (reg M ϕᴹ Ψ𝓞)
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = C'Ω Y ε Ψ𝓞 (M x)
  d : is-complemented (λ x → p x holds)
  d x = C'-decidable Y ε Ψ𝓞 (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Cδx₁x₂ CεΨ𝓞Mx₂
     = C'-trans Y ε Ψ𝓞 (M x₁) (M x₂) CεΨ𝓞Mx₂
         (pr₂ (ϕᴹ ε) x₁ x₂ Cδx₁x₂)

perfect-convergence
       : (X : ClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
       → (S : csearchable 𝓤₀ X)
       → (ε : ℕ)
       → (M : ⟨ X ⟩ → ⟪ Y ⟫) (ϕᴹ : f-ucontinuous' (ι X) Y M)
       → (k : ⟨ X ⟩)
       → let
           𝓞 = M k
           reg = p-regressor X Y S ε
           ω = M (reg M ϕᴹ 𝓞)
         in C' Y ε 𝓞 ω
perfect-convergence X Y S ε M ϕᴹ k
 = s-imperfect-convergence X Y S ε M ϕᴹ id k (C'-refl Y ε 𝓞)
 where 𝓞 = M k
```

[⇐ Index](../html/TWA.Thesis.index.html)
