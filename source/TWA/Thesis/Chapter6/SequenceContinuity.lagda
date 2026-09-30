Todd Waugh Ambridge, January 2024

# Uniform continuity of sequence functions

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan

open import Notation.Order
open import Naturals.Order
open import UF.DiscreteAndSeparated
open import UF.FunExt

module TWA.Thesis.Chapter6.SequenceContinuity (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe

open import MLTT.Two-Properties

seq-f-ucontinuous¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y))
                   → 𝓤 ⊔ 𝓥 ̇
seq-f-ucontinuous¹ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : (ℕ → X))
 → (x₁ ∼ⁿ x₂) δ → (f x₁ ∼ⁿ f x₂) ϵ)

seq-f-ucontinuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                   → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
seq-f-ucontinuous² {𝓤} {𝓥} {𝓦} {X} {Y} f
 = (ϵ : ℕ) → Σ (δˣ , δʸ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → X)) (y₁ y₂ : (ℕ → Y))
 → (x₁ ∼ⁿ x₂) δˣ → (y₁ ∼ⁿ y₂) δʸ → (f x₁ y₁ ∼ⁿ f x₂ y₂) ϵ)

map-ucontinuous' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (f : X → Y) → seq-f-ucontinuous¹ (map f)
map-ucontinuous' f ε = ε , λ α β α∼ⁿβ k k<ε → ap f (α∼ⁿβ k k<ε)

zipWith-ucontinuous' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → (f : X → X → Y)
                     → seq-f-ucontinuous² (zipWith f)
zipWith-ucontinuous' f ε
 = (ε , ε)
 , (λ α₁ α₂ β₁ β₂ α∼ β∼ k k<ϵ
    → ap (λ - → f - (β₁ k)) (α∼ k k<ϵ)
    ∙ ap (f (α₂ k)) (β∼ k k<ϵ))

seq-f-ucontinuous²-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                        → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                        → seq-f-ucontinuous² f
                        → (β : ℕ → Y)
                        → seq-f-ucontinuous¹ (λ α → f α β)
seq-f-ucontinuous²-left f ϕ β ε
 = pr₁ (pr₁ (ϕ ε))
 , λ α₁ α₂ α∼ → pr₂ (ϕ ε) α₁ α₂ β β α∼ (λ _ _ → refl)

seq-f-ucontinuous²-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                         → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                         → seq-f-ucontinuous² f
                         → (α : ℕ → X)
                         → seq-f-ucontinuous¹ (f α)
seq-f-ucontinuous²-right f ϕ α ε
 = pr₂ (pr₁ (ϕ ε))
 , λ β₁ β₂ → pr₂ (ϕ ε) α α β₁ β₂ (λ _ _ → refl)

seq-f-ucontinuous²-both : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → (f : (ℕ → X) → (ℕ → X) → (ℕ → Y))
                        → seq-f-ucontinuous² f
                        → seq-f-ucontinuous¹ (λ α → f α α)
seq-f-ucontinuous²-both f ϕ ε
 = δ
 , λ α β α∼ᵐβ → pr₂ (ϕ ε) α β α β
     (λ i i<m → α∼ᵐβ i
       (<-≤-trans i δ₁ δ i<m (max-≤-upper-bound  δ₁ δ₂)))
     (λ i i<m → α∼ᵐβ i
       (<-≤-trans i δ₂ δ i<m (max-≤-upper-bound' δ₂ δ₁)))
 where
  δ₁ δ₂ δ : ℕ
  δ₁ = pr₁ (pr₁ (ϕ ε))
  δ₂ = pr₂ (pr₁ (ϕ ε))
  δ  = max δ₁ δ₂

seq-f-ucontinuous²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ } {T : 𝓤' ̇ }
 → (f : (ℕ → X) → (ℕ → W) → (ℕ → T))
 → (g : (ℕ → Y) → (ℕ → Z) → (ℕ → W))
 → seq-f-ucontinuous² f
 → seq-f-ucontinuous² g
 → (z : ℕ → Z) → seq-f-ucontinuous² λ x y → f x (g y z)
seq-f-ucontinuous²-comp
 {_} {_} {_} {_} {_} {X} {Y} {Z} {W} {T} f g ϕᶠ ϕᵍ z ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = (pr₁ (pr₁ (ϕᶠ ϵ))) , pr₁ (pr₁ (ϕᵍ (pr₂ (pr₁ (ϕᶠ ϵ)))))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ)
    → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f x₁ (g y₁ z) ∼ⁿ f x₂ (g y₂ z)) ϵ
  γ x₁ x₂ y₁ y₂ x₁∼x₂ y₁∼y₂
   = pr₂ (ϕᶠ ϵ) x₁ x₂ (g y₁ z) (g y₂ z)
       x₁∼x₂
       (pr₂ (ϕᵍ (pr₂ (pr₁ (ϕᶠ ϵ)))) y₁ y₂ z z
       y₁∼y₂
       (λ _ _ → refl))

seq-f-ucontinuous¹²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → Z) → (ℕ → W))
 → (g : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous¹ f
 → seq-f-ucontinuous² g
 → seq-f-ucontinuous² λ x y → f (g x y)
seq-f-ucontinuous¹²-comp {_} {_} {_} {_} {X} {Y} {Z} {W}
 f g ϕᶠ ϕᵍ ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = pr₁ (ϕᵍ (pr₁ (ϕᶠ ϵ)))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ) → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f (g x₁ y₁) ∼ⁿ f (g x₂ y₂)) ϵ
  γ x₁ x₂ y₁ y₂ x∼ y∼
    = pr₂ (ϕᶠ ϵ) (g x₁ y₁) (g x₂ y₂)
        (pr₂ (ϕᵍ (pr₁ (ϕᶠ ϵ))) x₁ x₂ y₁ y₂ x∼ y∼)

seq-f-ucontinuous²¹-comp-left
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → W) → (ℕ → Y) → (ℕ → Z))
 → (g : (ℕ → X) → (ℕ → W))
 → seq-f-ucontinuous² f
 → seq-f-ucontinuous¹ g
 → seq-f-ucontinuous² (λ x y → f (g x) y)
seq-f-ucontinuous²¹-comp-left {_} {_} {_} {_} {X} {Y} {Z} {W}
 f g ϕᶠ ϕᵍ ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = pr₁ (ϕᵍ (pr₁ (pr₁ (ϕᶠ ϵ)))) , (pr₂ (pr₁ (ϕᶠ ϵ)))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ) → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f (g x₁) y₁ ∼ⁿ f (g x₂) y₂) ϵ
  γ x₁ x₂ y₁ y₂ x∼ y∼
    = pr₂ (ϕᶠ ϵ) (g x₁) (g x₂) y₁ y₂
        (pr₂ (ϕᵍ (pr₁ (pr₁ (ϕᶠ ϵ)))) x₁ x₂ x∼) y∼

seq-f-ucontinuousᴺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
                    → 𝓤 ⊔ 𝓥 ̇
seq-f-ucontinuousᴺ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ (d , δ) ꞉ ℕ × ℕ , (d ≤ δ
 × ((x₁ x₂ : (ℕ → (ℕ → X)))
 → ((n : ℕ) → n < d → (x₁ n ∼ⁿ x₂ n) δ) → (f x₁ ∼ⁿ f x₂) ϵ))

seq-f-ucontinuous¹-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → X) → (ℕ → Y))
 → seq-f-ucontinuous¹ f
 → f-ucontinuous (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuous¹-to-closeness dˣ dʸ f ϕ ε
 = pr₁ (ϕ ε)
 , λ α β Cαβ → ∼ⁿ-to-C dʸ (f α) (f β) ε
                (pr₂ (ϕ ε) α β (C-to-∼ⁿ dˣ α β (pr₁ (ϕ ε)) Cαβ))

closeness-to-seq-f-ucontinuous¹
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → X) → (ℕ → Y))
 → f-ucontinuous (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ) f
 → seq-f-ucontinuous¹ f
closeness-to-seq-f-ucontinuous¹ dˣ dʸ f ϕ ε
 = pr₁ (ϕ ε)
 , λ α β α∼β → C-to-∼ⁿ dʸ (f α) (f β) ε
                (pr₂ (ϕ ε) α β (∼ⁿ-to-C dˣ α β (pr₁ (ϕ ε)) α∼β))

seq-f-ucontinuous¹-↔-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → X) → (ℕ → Y))
 → seq-f-ucontinuous¹ f
 ↔ f-ucontinuous (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuous¹-↔-closeness dˣ dʸ f
 = seq-f-ucontinuous¹-to-closeness dˣ dʸ f
 , closeness-to-seq-f-ucontinuous¹ dˣ dʸ f

seq-f-ucontinuous²-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y) (dᶻ : is-discrete Z)
 → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous² f
 → f-ucontinuous (×-ClosenessSpace (ℕ→D-ClosenessSpace dˣ)
                                   (ℕ→D-ClosenessSpace dʸ))
                 (ℕ→D-ClosenessSpace dᶻ) (uncurry f)
seq-f-ucontinuous²-to-closeness dˣ dʸ dᶻ f ϕ ε
 = δ
 , λ (α₁ , α₂) (β₁ , β₂) Cαβ
 → ∼ⁿ-to-C dᶻ (f α₁ α₂) (f β₁ β₂) ε
     (pr₂ (ϕ ε) α₁ β₁ α₂ β₂
       (λ i i<δα → C-to-∼ⁿ dˣ α₁ β₁ δ
         (×-C-left (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δα δ i<δα
              (max-≤-upper-bound δα δβ)))
       (λ i i<δβ → C-to-∼ⁿ dʸ α₂ β₂ δ
         (×-C-right (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δβ δ i<δβ
             (max-≤-upper-bound' δβ δα))))
 where
  δα δβ δ : ℕ
  δα = pr₁ (pr₁ (ϕ ε))
  δβ = pr₂ (pr₁ (ϕ ε))
  δ  = max δα δβ

closeness-to-seq-f-ucontinuous²
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y) (dᶻ : is-discrete Z)
 → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → f-ucontinuous (×-ClosenessSpace (ℕ→D-ClosenessSpace dˣ)
                                   (ℕ→D-ClosenessSpace dʸ))
                 (ℕ→D-ClosenessSpace dᶻ) (uncurry f)
 → seq-f-ucontinuous² f
closeness-to-seq-f-ucontinuous² dˣ dʸ dᶻ f ϕ ε
 = (δ , δ)
 , λ x₁ x₂ y₁ y₂ x₁∼x₂ y₁∼y₂
   → C-to-∼ⁿ dᶻ (f x₁ y₁) (f x₂ y₂) ε
       (pr₂ (ϕ ε) (x₁ , y₁) (x₂ , y₂)
         (×-C-combine
           (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           x₁ x₂ y₁ y₂ δ
           (∼ⁿ-to-C dˣ x₁ x₂ δ x₁∼x₂) (∼ⁿ-to-C dʸ y₁ y₂ δ y₁∼y₂)))
 where
  δ : ℕ
  δ = pr₁ (ϕ ε)

seq-f-ucontinuous²-↔-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y) (dᶻ : is-discrete Z)
 → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous² f
 ↔ f-ucontinuous (×-ClosenessSpace (ℕ→D-ClosenessSpace dˣ)
                                   (ℕ→D-ClosenessSpace dʸ))
                 (ℕ→D-ClosenessSpace dᶻ) (uncurry f)
seq-f-ucontinuous²-↔-closeness dˣ dʸ dᶻ f
 = seq-f-ucontinuous²-to-closeness dˣ dʸ dᶻ f
 , closeness-to-seq-f-ucontinuous² dˣ dʸ dᶻ f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ (double n))

double-≤ : (n : ℕ) → n ≤ double n
double-≤ zero = ⋆
double-≤ (succ zero) = ⋆
double-≤ (succ (succ n))
 = ≤-trans n (double n) (succ (succ (double n)))
     (double-≤ n)
     (≤-trans (double n) (succ (double n)) (succ (succ (double n)))
       (≤-succ (double n)) (≤-succ (succ (double n))))

pred^i-0-is-0 : (i : ℕ) → (pred ^ i) 0 ＝ 0
pred^i-0-is-0 zero = refl
pred^i-0-is-0 (succ i) = ap pred (pred^i-0-is-0 i)

pred^si-sn-is-pred^i-n
 : (i n : ℕ) → (pred ^ succ i) (succ n) ＝ (pred ^ i) n
pred^si-sn-is-pred^i-n zero n = refl
pred^si-sn-is-pred^i-n (succ i) n
 = ap pred (pred^si-sn-is-pred^i-n i n)

pred^i≥n-is-0 : (i n : ℕ) → n ≤ i → (pred ^ i) n ＝ 0
pred^i≥n-is-0 i zero n≤i = pred^i-0-is-0 i
pred^i≥n-is-0 zero (succ n) n≤i = 𝟘-elim n≤i
pred^i≥n-is-0 (succ i) (succ n) n≤i
 = pred^si-sn-is-pred^i-n i n
 ∙ pred^i≥n-is-0 i n n≤i

pred^i-sn-is-s-pred^i-n
 : (i n : ℕ) → i ≤ n → (pred ^ i) (succ n) ＝ succ ((pred ^ i) n)
pred^i-sn-is-s-pred^i-n zero n i<n = refl
pred^i-sn-is-s-pred^i-n (succ i) zero i<n = 𝟘-elim i<n
pred^i-sn-is-s-pred^i-n (succ i) (succ n) i<n
 = pred^si-sn-is-pred^i-n i (succ n)
 ∙ pred^i-sn-is-s-pred^i-n i n i<n
 ∙ ap succ (pred^si-sn-is-pred^i-n i n ⁻¹)

pred^n-double-n-is-n : (n : ℕ) → (pred ^ n) (double n) ＝ n
pred^n-double-n-is-n zero = refl
pred^n-double-n-is-n (succ n)
 = pred^si-sn-is-pred^i-n n (succ (double n))
 ∙ pred^i-sn-is-s-pred^i-n n (double n) (double-≤ n)
 ∙ ap succ (pred^n-double-n-is-n n)

pred-≤ : (n : ℕ) → pred n ≤ n
pred-≤ zero = ⋆
pred-≤ (succ n) = ≤-succ n

predⁱ-≤ : (i n : ℕ) → (pred ^ i) n ≤ n
predⁱ-≤ zero n = ≤-refl n
predⁱ-≤ (succ i) n
 = ≤-trans (pred ((pred ^ i) n)) ((pred ^ i) n) n
     (pred-≤ ((pred ^ i) n)) (predⁱ-≤ i n)

pred-mono : (n m : ℕ) → n ≤ m → pred n ≤ pred m
pred-mono zero zero n≤m = ⋆
pred-mono zero (succ m) n≤m = ⋆
pred-mono (succ n) zero n≤m = 𝟘-elim n≤m
pred-mono (succ n) (succ m) n≤m = n≤m

nid : (n i d : ℕ) → n < i → (pred ^ i) d ≤ (pred ^ n) d
nid zero zero d n<i = 𝟘-elim n<i
nid (succ n) zero d n<i = 𝟘-elim n<i
nid zero (succ i) d n<i = predⁱ-≤ (succ i) d
nid (succ n) (succ i) d n<i
 = pred-mono ((pred ^ i) d) ((pred ^ n) d) (nid n i d n<i)

ΠC-to-∼ⁿ' : {X : ℕ → 𝓤 ̇ }
          → (d : (n : ℕ) → is-discrete (X n))
          → (α β : (ℕ → Π X)) (n : ℕ)
          → C (Π-ClosenessSpace (λ _ → ΠD-ClosenessSpace d)) n α β
          → (i : ℕ)
          → (α i ∼ⁿ β i) ((pred ^ i) n)
ΠC-to-∼ⁿ' d α β zero Cαβ i
 = transport (α i ∼ⁿ β i) (pred^i-0-is-0 i ⁻¹) (λ _ → 𝟘-elim)
ΠC-to-∼ⁿ' d α β (succ n) Cαβ zero = C-to-∼ⁿ' d (α 0) (β 0) (succ n) γ
 where
  γ : C (ΠD-ClosenessSpace d) (succ n) (α 0) (β 0)
  γ 0 j⊏sn = Cαβ 0 refl
  γ (succ j) j⊏sn = Lemma[min𝟚ab＝₁→a＝₁] (Cαβ (succ j) j⊏sn)
ΠC-to-∼ⁿ' d α β (succ n) Cαβ (succ i)
 = transport (α (succ i) ∼ⁿ β (succ i)) (pred^si-sn-is-pred^i-n i n ⁻¹) γ
 where
  γ : (α (succ i) ∼ⁿ β (succ i)) ((pred ^ i) n)
  γ = ΠC-to-∼ⁿ' d (tail α) (tail β) n
        (λ j j⊏n → Lemma[min𝟚ab＝₁→b＝₁] (Cαβ (succ j) j⊏n)) i

∼ⁿ-to-ΠC' : {X : ℕ → 𝓤 ̇ }
          → (d : (n : ℕ) → is-discrete (X n))
          → (α β : (ℕ → Π X)) (n : ℕ)
          → ((i : ℕ) → (α i ∼ⁿ β i) ((pred ^ i) n))
          → C (Π-ClosenessSpace (λ _ → ΠD-ClosenessSpace d)) n α β
∼ⁿ-to-ΠC' d α β n f 0 i⊏sn
 = ∼ⁿ-to-C' d (α 0) (β 0) n (f 0) 0 i⊏sn
∼ⁿ-to-ΠC' d α β zero f (succ i) i⊏sn = 𝟘-elim (zero-is-not-one i⊏sn)
∼ⁿ-to-ΠC' d α β (succ n) f (succ i) i⊏sn
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
    (∼ⁿ-to-C' d (α 0) (β 0) (succ n) (f 0) (succ i) i⊏sn)
    (∼ⁿ-to-ΠC' d (tail α) (tail β) n γ i i⊏sn)
 where
  γ : (j : ℕ) → (α (succ j) ∼ⁿ β (succ j)) ((pred ^ j) n)
  γ j = transport (α (succ j) ∼ⁿ β (succ j))
         (pred^si-sn-is-pred^i-n j n)
         (f (succ j))

ΠC-to-∼ⁿ : {X : ℕ → 𝓤 ̇ }
         → (d : (n : ℕ) → is-discrete (X n))
         → (α β : (ℕ → Π X)) (n : ℕ)
         → C (Π-ClosenessSpace (λ _ → ΠD-ClosenessSpace d)) (double n) α β
         → (i : ℕ) → i < n → (α i ∼ⁿ β i) n
ΠC-to-∼ⁿ d α β zero Cαβ i i<n j j<n = 𝟘-elim i<n
ΠC-to-∼ⁿ d α β n@(succ _) Cαβ i i<n j j<n
 = ΠC-to-∼ⁿ' d α β (double n) Cαβ i j
     (<-≤-trans j n ((pred ^ i) (double n)) j<n
     (≤-trans n ((pred ^ n) (double n)) ((pred ^ i) (double n))
       (transport (n ≤_) (pred^n-double-n-is-n n ⁻¹) (≤-refl n ))
       (nid i n (double n) i<n)))

∼ⁿ-to-ΠC : {X : ℕ → 𝓤 ̇ }
         → (d : (n : ℕ) → is-discrete (X n))
         → (α β : (ℕ → Π X)) (n : ℕ)
         → ((i : ℕ) → i < n → (α i ∼ⁿ β i) n)
         → C (Π-ClosenessSpace (λ _ → ΠD-ClosenessSpace d)) n α β
∼ⁿ-to-ΠC d α β zero α∼β i i⊏n = 𝟘-elim (zero-is-not-one i⊏n)
∼ⁿ-to-ΠC d α β n@(succ _) α∼β
 = ∼ⁿ-to-ΠC' d α β n (λ i → Cases (order-split i n) (γ< i) (γ≥ i))
 where
  γ< : (i : ℕ) → i < n → (α i ∼ⁿ β i) ((pred ^ i) n)
  γ< i i<n j j<2n-i
   = α∼β i i<n j (<-≤-trans j ((pred ^ i) n) n j<2n-i (predⁱ-≤ i n))
  γ≥ : (i : ℕ) → n ≤ i → (α i ∼ⁿ β i) ((pred ^ i) n)
  γ≥ i n≤i = transport (α i ∼ⁿ β i) (pred^i≥n-is-0 i n n≤i ⁻¹) (λ _ → 𝟘-elim)

seq-f-ucontinuousᴺ-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
 → seq-f-ucontinuousᴺ f
 → f-ucontinuous (Π-ClosenessSpace (λ _ → ℕ→D-ClosenessSpace dˣ))
                 (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuousᴺ-to-closeness {𝓤} {𝓥} {X} {Y} dˣ dʸ f ϕ ε
 = double δ
 , λ x₁ x₂ C2δx₁x₂ → ∼ⁿ-to-C' (λ _ → dʸ) (f x₁) (f x₂) ε
     (ϕ' x₁ x₂ (λ n n<d
       → ΠC-to-∼ⁿ (λ _ → dˣ) x₁ x₂ δ C2δx₁x₂ n
           (<-≤-trans n d δ n<d d≤δ)))
 where
  d δ : ℕ
  d = pr₁ (pr₁ (ϕ ε))
  δ = pr₂ (pr₁ (ϕ ε))
  d≤δ : d ≤ δ
  d≤δ = pr₁ (pr₂ (ϕ ε))
  ϕ' : (x₁ x₂ : (ℕ → (ℕ → X)))
     → ((n : ℕ) → n < d → (x₁ n ∼ⁿ x₂ n) δ)
     → (f x₁ ∼ⁿ f x₂) ε
  ϕ' = pr₂ (pr₂ (ϕ ε))

closeness-to-seq-f-ucontinuousᴺ
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
 → f-ucontinuous (Π-ClosenessSpace (λ _ → ℕ→D-ClosenessSpace dˣ))
                 (ℕ→D-ClosenessSpace dʸ) f
 → seq-f-ucontinuousᴺ f
closeness-to-seq-f-ucontinuousᴺ {𝓤} {𝓥} {X} {Y} dˣ dʸ f ϕ ε
 = (δ , δ) , ≤-refl δ
 , λ x₁ x₂ x₁∼x₂ → C-to-∼ⁿ' (λ _ → dʸ) (f x₁) (f x₂) ε
     (pr₂ (ϕ ε) x₁ x₂ (∼ⁿ-to-ΠC (λ _ → dˣ) x₁ x₂ δ x₁∼x₂))
 where
  δ : ℕ
  δ = pr₁ (ϕ ε)

seq-f-ucontinuousᴺ-↔-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
 → seq-f-ucontinuousᴺ f
 ↔ f-ucontinuous (Π-ClosenessSpace (λ _ → ℕ→D-ClosenessSpace dˣ))
                 (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuousᴺ-↔-closeness {𝓤} {𝓥} {X} {Y} dˣ dʸ f
 = seq-f-ucontinuousᴺ-to-closeness dˣ dʸ f
 , closeness-to-seq-f-ucontinuousᴺ dˣ dʸ f
\end{code}
