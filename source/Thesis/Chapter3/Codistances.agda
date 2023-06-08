{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude
open import UF-FunExt
open import SignedDigit
open import GenericConvergentSequence
open import DiscreteAndSeparated
open import NaturalsOrder
open import Two-Properties

module Codistances (fe : FunExt) where

open import Codistance fe
open sequences

×-codistance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → (X → X → ℕ∞) → (Y → Y → ℕ∞)
             → (X × Y → X × Y → ℕ∞)
×-codistance cx cy (x₁ , y₁) (x₂ , y₂) = min (cx x₁ x₂) (cy y₁ y₂)

×ⁿ-codistance : {X : 𝓤 ̇ } → (X → X → ℕ∞)
              → (n : ℕ) → (X ^⟨succ n ⟩ → X ^⟨succ n ⟩ → ℕ∞)
×ⁿ-codistance cx 0 = cx
×ⁿ-codistance cx (succ n)
  = ×-codistance cx (×ⁿ-codistance cx n)

≈→≼ : {X : 𝓤 ̇ } (d≡ : is-discrete X) (x y : ℕ → X) (ε : ℕ)
    → (x ≈ y) ε → under ε ≼ codistance X d≡ x y
≈→≼ {𝓤} {X} d≡ x y ε x≈y n n⊏ε
 = codistance-conceptually₁ X d≡ x y n
     (λ k k≤n → Cases (<-split k n k≤n)
       (λ k<n → x≈y k (<-trans k n ε k<n
         (⊏-gives-< n ε n⊏ε)))
       (λ k≡n → x≈y k (transport (λ - → succ - ≤ ε) (k≡n ⁻¹)
         (⊏-gives-< n ε n⊏ε))))

≼→≈ : {X : 𝓤 ̇ } (d≡ : is-discrete X) (x y : ℕ → X) (ε : ℕ)
    → under ε ≼ codistance X d≡ x y → (x ≈ y) ε
≼→≈ {𝓤} {X} d≡ x y (succ ε) ε≼cxy
 = codistance-conceptually₂ X d≡ x y ε (ε≼cxy ε (under-diagonal₁ ε))

uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → (X → X → ℕ∞) → (Y → Y → ℕ∞)
           → (X → Y) → ℕ → ℕ → 𝓤 ̇
uc-mod-of² cx cy f ε δ
 = ∀ x y → (under δ) ≼ (cx x y) → (under ε) ≼ (cy (f x) (f y))

continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → (X → X → ℕ∞) → (Y → Y → ℕ∞)
            → (X → Y) → 𝓤 ̇
continuous² cx cy f = ∀ ε → Σ (uc-mod-of² cx cy f ε)

uc-mod-of : {X : 𝓤 ̇ } → (X → X → ℕ∞) → (X → 𝓥 ̇ ) → ℕ → 𝓤 ⊔ 𝓥 ̇
uc-mod-of c p δ = ∀ x y → (under δ) ≼ (c x y) → p x → p y

continuous : {X : 𝓤 ̇ } → (X → X → ℕ∞) → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
continuous c p = Σ (uc-mod-of c p)

everywhere-sin : {Y : 𝓤 ̇ } → (Y → Y → ℕ∞) → 𝓤 ̇
everywhere-sin cy = ∀ x → Π (_⊏ cy x x)

right-continuous : {Y : 𝓤 ̇ } → (Y → Y → ℕ∞) → 𝓤 ̇
right-continuous {𝓤} {Y} c
 = (ε : ℕ) → ((z x y : Y)
           → under ε ≼ c x y
           → (incl (c z x) ≈ incl (c z y)) ε)

×-codistance-min : {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                 → (cx : X → X → ℕ∞) → (cy : Y → Y → ℕ∞)
                 → (m : ℕ∞) (x₁ x₂ : X) (y₁ y₂ : Y)
                 → m ≼ cx x₁ x₂ → m ≼ cy y₁ y₂
                 → m ≼ (×-codistance cx cy) (x₁ , y₁) (x₂ , y₂)
×-codistance-min cx cy m x₁ x₂ y₁ y₂ m≼cx m≼cy n p
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (m≼cx n p) (m≼cy n p)

×-codistance-min' : {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                  → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
                  → (m : ℕ∞) (x₁ x₂ : X) (y₁ y₂ : Y)
                  → m ≼ (×-codistance cx cy) (x₁ , y₁) (x₂ , y₂)
                  → m ≼ cx x₁ x₂ × m ≼ cy y₁ y₂
×-codistance-min' cx cy m x₁ x₂ y₁ y₂ m≼cxy
 = (λ n r → Lemma[min𝟚ab≡₁→a≡₁] (m≼cxy n r))
 , (λ n r → Lemma[min𝟚ab≡₁→b≡₁] (m≼cxy n r))

→-everywhere-sin : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                 → everywhere-sin (codistance X d≡)
→-everywhere-sin {𝓤} {X} d≡ x n
 = transport (n ⊏_) (γ ⁻¹) (∞-⊏-maximal n)
 where
  γ : codistance X d≡ x x ≡ ∞
  γ = pr₁ (pr₂ (ℕ→D-has-codistance X d≡)) x

→-right-continuous : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                   → right-continuous (codistance X d≡)
→-right-continuous {𝓤} {X} d≡ ε z x y ε≼cxy 0 0<ε
 = Cases (d≡ (head z) (head x))
    (λ h → ap (λ - → incl - 0) (codistance-eq₁ X d≡ z x h)
         ∙ ap (λ - → incl - 0) (codistance-eq₁ X d≡ z y
             (h ∙ hx≡hy) ⁻¹))
   (λ ¬h → ap (λ - → incl - 0) (codistance-eq₀ X d≡ z x ¬h)
         ∙ ap (λ - → incl - 0) (codistance-eq₀ X d≡ z y
             (λ z≡y → ¬h (z≡y ∙ hx≡hy ⁻¹)) ⁻¹))
 where
  hx≡hy : head x ≡ head y
  hx≡hy = ≼→≈ d≡ x y ε ε≼cxy 0 0<ε
→-right-continuous {𝓤} {X} d≡ (succ ε) z x y ε≼cxy (succ k) k<ε
 = Cases (d≡ (head z) (head x))
     (λ h → ap (λ - → incl - (succ k)) (codistance-eq₁ X d≡ z x h)
          ∙ IH
          ∙ ap (λ - → incl - (succ k)) (codistance-eq₁ X d≡ z y
              (h ∙ hx≡hy) ⁻¹))
    (λ ¬h → ap (λ - → incl - (succ k)) (codistance-eq₀ X d≡ z x ¬h)
          ∙ ap (λ - → incl - (succ k)) (codistance-eq₀ X d≡ z y
              (λ z≡y → ¬h (z≡y ∙ hx≡hy ⁻¹)) ⁻¹))
 where
  x≈y : (x ≈ y) (succ ε)
  x≈y = ≼→≈ d≡ x y (succ ε) ε≼cxy
  hx≡hy : head x ≡ head y
  hx≡hy = x≈y 0 *
  IH = →-right-continuous d≡ ε (tail z) (tail x) (tail y)
         (≈→≼ d≡ (tail x) (tail y) ε (λ n n<ε → x≈y (succ n) n<ε))
         k k<ε

×-everywhere-sin : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
                 → everywhere-sin cx
                 → everywhere-sin cy
                 → everywhere-sin (×-codistance cx cy)
×-everywhere-sin cx cy cx→ cy→ (x , y) n
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (cx→ x n) (cy→ y n)

×ⁿ-everywhere-sin : {X : 𝓤 ̇ }
                 → (cx : X → X → ℕ∞) (n : ℕ)
                 → everywhere-sin cx
                 → everywhere-sin (×ⁿ-codistance cx n)
×ⁿ-everywhere-sin cx 0 = id
×ⁿ-everywhere-sin cx (succ n) cx→
 = ×-everywhere-sin cx (×ⁿ-codistance cx n) cx→
     (×ⁿ-everywhere-sin cx n cx→)

×-right-continuous
               : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞)
               → right-continuous cx
               → right-continuous cy
               → right-continuous (×-codistance cx cy)
×-right-continuous cx cy cx-r cy-r ε
 (z₁ , z₂) (x₁ , x₂) (y₁ , y₂) ε≼cxy k k<ε
 = min𝟚-abcd (cx-r ε z₁ x₁ y₁ (pr₁ γ) k k<ε)
             (cy-r ε z₂ x₂ y₂ (pr₂ γ) k k<ε)
 where
   γ = ×-codistance-min' cx cy (under ε) x₁ y₁ x₂ y₂ ε≼cxy

×ⁿ-right-continuous : {X : 𝓤 ̇ } 
                    → (cx : X → X → ℕ∞) (n : ℕ)
                    → right-continuous cx
                    → right-continuous (×ⁿ-codistance cx n)
×ⁿ-right-continuous cx 0 = id
×ⁿ-right-continuous cx (succ n) cx-r
 = ×-right-continuous cx (×ⁿ-codistance cx n)
     cx-r (×ⁿ-right-continuous cx n cx-r)
