```agda

{-# OPTIONS --without-K --exact-split --safe --guardedness #-}

open import MLTT.Spartan
open import UF.FunExt
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Embeddings
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to ι
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.Complemented
open import MLTT.Two-Properties

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter4.LPOWorking (fe : FunExt) where

open import Taboos.BasicDiscontinuity fe
open import Taboos.WLPO

decidable-𝟚 : {X : 𝓤 ̇ } → is-decidable X → 𝟚
decidable-𝟚 (inl _) = ₁
decidable-𝟚 (inr _) = ₀

decidable-𝟚₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → X → decidable-𝟚 d ＝ ₁
decidable-𝟚₁ (inl  x) _ = refl
decidable-𝟚₁ (inr ¬x) x = 𝟘-elim (¬x x)

decidable-𝟚₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → ¬ X → decidable-𝟚 d ＝ ₀
decidable-𝟚₀ (inl  x) ¬x = 𝟘-elim (¬x x)
decidable-𝟚₀ (inr ¬x)  _ = refl

𝟚-decidable₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₁ → X
𝟚-decidable₁ d e with d
... | inl  x = x
... | inr ¬x = 𝟘-elim (zero-is-not-one e)

𝟚-decidable₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₀ → ¬ X
𝟚-decidable₀ d e with d
... | inl  x = 𝟘-elim (zero-is-not-one (e ⁻¹))
... | inr ¬x = ¬x

decidable-seq-𝟚 : {X : ℕ → 𝓤 ̇ } → is-complemented X → (ℕ → 𝟚)
decidable-seq-𝟚 d n = decidable-𝟚 (d (succ n))

_≤l_ : (α β : ℕ → 𝟚) → 𝓤₀ ̇
α ≤l β = (n : ℕ) → (α ∼ⁿ β) n → α n ≤ β n

≤₂-+ : (a b : 𝟚) → (a ≤ b) + ¬ (a ≤ b)
≤₂-+ ₀ ₀ = inl ⋆
≤₂-+ ₀ ₁ = inl ⋆
≤₂-+ ₁ ₀ = inr id
≤₂-+ ₁ ₁ = inl ⋆

¬≤𝟚 : (a b : 𝟚) → ¬ (a ≤ b) → b ≤ a
¬≤𝟚 ₀ ₀ _ = ⋆
¬≤𝟚 ₀ ₁ f = f ⋆
¬≤𝟚 ₁ ₀ _ = ⋆
¬≤𝟚 ₁ ₁ _ = ⋆

linearity : 𝓤₀  ̇ 
linearity = (α β : ℕ → 𝟚) → α ≤l β + β ≤l α

linearity' : 𝓤₀ ̇
linearity' = (u v : ℕ∞) → u ≼ v + v ≼ u

flip : 𝟚 → 𝟚
flip ₀ = ₁
flip ₁ = ₀

which-of₀ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
          → (x : A + B)
          → ¬ B
          → pr₁ (which-of {_} {_} {A} {B} x) ＝ ₀
which-of₀ (inl x) ¬b = refl
which-of₀ (inr x) ¬b = 𝟘-elim (¬b x)

which-of₁ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
          → (x : A + B)
          → ¬ A
          → pr₁ (which-of {_} {_} {A} {B} x) ＝ ₁
which-of₁ (inl x) ¬a = 𝟘-elim (¬a x)
which-of₁ (inr x) ¬a = refl

₁-not-smaller-than-₀ : ¬ (₁ ≤₂ ₀)
₁-not-smaller-than-₀ ()

∞-not-smaller-than-finite : (n : ℕ) → ¬ (pr₁ ∞ ≤l pr₁ (ι n))
∞-not-smaller-than-finite n ∞≤n
 = transport (₁ ≤₂_)
     (ℕ-to-ℕ∞-diagonal₀ n)
     (∞≤n n (λ i i<n → <-gives-⊏ i n i<n ⁻¹))

linearity→WLPO : linearity → Σ basic-discontinuity
linearity→WLPO l
 = Cases (𝟚-possibilities (f (pr₁ ∞) (pr₁ ∞))) γ₁ γ₂
 where
  f : (ℕ → 𝟚) → (ℕ → 𝟚) → 𝟚
  f α β = pr₁ (which-of (l α β))
  γ₁ : f (pr₁ ∞) (pr₁ ∞) ＝ ₀ → Σ basic-discontinuity
  γ₁ e = p
       , (λ n → ap flip (which-of₁ (l (pr₁ ∞) (pr₁ (ι n)))
           (∞-not-smaller-than-finite n)))
       , ap flip e
   where
    p : ℕ∞ → 𝟚
    p u = flip (f (pr₁ ∞) (pr₁ u))
  γ₂ : f (pr₁ ∞) (pr₁ ∞) ＝ ₁ → Σ basic-discontinuity
  γ₂ e = p
       , (λ n → which-of₀ (l (pr₁ (ι n)) (pr₁ ∞))
           (∞-not-smaller-than-finite n))
       , e
   where
    p : ℕ∞ → 𝟚
    p u = f (pr₁ u) (pr₁ ∞)

decidable-thing : (α β : ℕ → 𝟚) (n : ℕ)
                → is-decidable ((α ∼ⁿ β) n → α n ≤ β n)
decidable-thing α β n
 = Cases (≤₂-+ (α n) (β n))
     (λ z → inl (λ _ → z))
     (Cases (∼ⁿ-decidable (λ _ → 𝟚-is-discrete) α β n)
       (λ z z₁ → inr (λ x → z₁ (x z)))
       (λ z z₁ → inl (𝟘-elim ∘ z)))

min-≼ : (u v : ℕ∞) → min u v ＝ u → u ≼ v
min-≼ u v m = transport (_≼ v) m (λ n e → Lemma[min𝟚ab＝₁→b＝₁] e)

¬-min₂ : (a b : 𝟚) → min𝟚 a b ≠ a → min𝟚 a b ＝ b
¬-min₂ ₀ ₀ e = refl
¬-min₂ ₀ ₁ e = 𝟘-elim (e refl)
¬-min₂ ₁ _ e = refl

min-Succ : (u v : ℕ∞) → Succ (min u v) ＝ min (Succ u) (Succ v)
min-Succ u v
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) γ)
 where
  γ : _
  γ zero = refl
  γ (succ i) = refl

Succ-≠ : (u v : ℕ∞) → Succ u ≠ Succ v → u ≠ v
Succ-≠ u v f refl = f refl

¬-min' : (n : ℕ) (v : ℕ∞) → min (ι n) v ≠ ι n → pr₁ v n ≠ ₁
¬-min' zero v m e = m refl
¬-min' (succ n) v m
 = Cases (Zero-or-Succ (fe _ _) v)
     (λ e f → zero-is-not-one (ap (λ - → pr₁ - n) (ap Pred e ∙ Pred-Zero-is-Zero) ⁻¹ ∙ f))
     (λ e → ¬-min' n (Pred v)
              (Succ-≠ _ _
                (transport (_≠ Succ (ι n))
                  (ap (min (Succ (ι n))) e
                  ∙ min-Succ (ι n) (Pred v) ⁻¹)
                m)))

¬-min : (u v : ℕ∞) → min u v ≠ u → ¬ (u ≺ v)
¬-min u v m (n , refl , e) = ¬-min' n v m e

WLPO→linearity' : WLPO → linearity'
WLPO→linearity' w α β
 = Cases (WLPO-gives-ℕ∞-discrete fe w (min α β) α)
     (inl ∘ min-≼ α β)
     (inr ∘ λ m → not-≺-≼ (fe _ _) β α (¬-min α β m))

