{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude renaming (map to map')
open import UF-FunExt
open import SignedDigit
open import Two-Properties
open import SpartanMLTT
open import NaturalsOrder
open import DecidableAndDetachable
open import GenericConvergentSequence
open import DiscreteAndSeparated

module ConvergenceTheorems (fe : FunExt) where

open import Codistance fe
open import Codistances fe
open import SearchableTypes fe
open import SignedDigitContinuity fe

⊏-gives-≼ : (ε : ℕ) (v : ℕ∞) → ε ⊏ v → under (succ ε) ≼ v
⊏-gives-≼ ε v ε⊏v n n⊏ε = ⊏-trans'' v ε n (⊏-gives-< n (succ ε) n⊏ε) ε⊏v

≼-gives-⊏ : (ε : ℕ) (v : ℕ∞) → under (succ ε) ≼ v → ε ⊏ v
≼-gives-⊏ ε v ε≼v = ε≼v ε (under-diagonal₁ ε)

¬⊏-gives-¬≼ : (ε : ℕ) (v : ℕ∞) → ¬ (ε ⊏ v) → ¬ (under (succ ε) ≼ v)
¬⊏-gives-¬≼ ε v ¬ε⊏v sε≼v = ¬ε⊏v (≼-gives-⊏ ε v sε≼v)

≼-decidable : (ε : ℕ) (v : ℕ∞) → decidable (under ε ≼ v)
≼-decidable zero v = inl (Zero-minimal v)
≼-decidable (succ ε) v = Cases (𝟚-is-discrete (incl v ε) ₁)
                           (inl ∘ ⊏-gives-≼ ε v)
                           (inr ∘ ¬⊏-gives-¬≼ ε v)

≼-continuous : (ε : ℕ) (u v : ℕ∞)
             → (incl u ≈ incl v) ε
             → under ε ≼ u
             → under ε ≼ v
≼-continuous zero u v _ _ = Zero-minimal v
≼-continuous (succ ε) u v ε≼cuv sε≼u
 = ⊏-gives-≼ ε v (ε≼cuv ε (<-succ ε) ⁻¹ ∙ ≼-gives-⊏ ε u sε≼u)

regressor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → (cx : X → X → ℕ∞) (cy : Y → Y → ℕ∞) → 𝓤 ⊔ 𝓥 ̇
regressor {𝓤} {𝓥} {X} {Y} cx cy = (M : X → Y) → continuous² cx cy M → Y → X

p-regressor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → (cx : X → X → ℕ∞) (Φ : Y → Y → ℕ∞)
            → (ϕᴸ : right-continuous Φ)
            → (𝓔S : c-searchable cx)
            → (ε : ℕ) → regressor cx Φ
p-regressor {𝓤} {𝓥} {X} {Y} cx Φ ϕᴸ 𝓔S ε M cᴹ ΨΩ
 = 𝓔⟨ cx , 𝓔S ⟩ (p M cᴹ ΨΩ) (d M cᴹ ΨΩ) (ϕ M cᴹ ΨΩ)
  where
  p : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y) → (X → 𝓤₀ ̇ )
  p M ϕᴹ ΨΩ x = under ε ≼ Φ ΨΩ (M x)
  d : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y)
    → detachable (p M ϕᴹ ΨΩ)
  d M ϕᴹ ΨΩ x = ≼-decidable ε (Φ ΨΩ (M x))
  ϕ : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y)
    → continuous cx (p M ϕᴹ ΨΩ)
  ϕ M ϕᴹ ΨΩ = δ , γ where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : uc-mod-of cx (p M ϕᴹ ΨΩ) δ
    γ x y δ≼cxy = ≼-continuous ε (Φ ΨΩ (M x)) (Φ ΨΩ (M y))
                   (ϕᴸ ε ΨΩ (M x) (M y) (pr₂ (ϕᴹ ε) x y δ≼cxy))

_≼ⁿ_ : ℕ∞ → ℕ∞ → ℕ → 𝓤₀ ̇
(u ≼ⁿ v) n = <ₙ (λ k → k ⊏ u → k ⊏ v) n

≼ⁿ-back : (u v : ℕ∞) (n : ℕ) → ¬ (n ⊏ u) → (u ≼ⁿ v) n → (u ≼ⁿ v) (succ n)
≼ⁿ-back u v n ¬n⊏u u≼ⁿv = <ₙ-succ n u≼ⁿv (𝟘-elim ∘ ¬n⊏u)

≼ⁿ-top : (u v : ℕ∞) (n : ℕ) → n ⊏ v → (u ≼ⁿ v) (succ n)
≼ⁿ-top u v zero n⊏v 0 _ _ = n⊏v
≼ⁿ-top u v (succ n) n⊏v
 = <ₙ-succ (succ n) (≼ⁿ-top u v n (pr₂ v n n⊏v)) (λ _ → n⊏v)

f-max-≼ⁿ : {X : 𝓤 ̇ } → ℕ → (X → ℕ∞) → 𝓤 ̇ 
f-max-≼ⁿ {𝓤} {X} n f = Σ x₀ ꞉ X , Π x ꞉ X , (f x ≼ⁿ f x₀) n
         
f-minimisation : {X : 𝓤 ̇ } (c : X → X → ℕ∞)
               → (𝓔S : c-searchable c)
               → (n : ℕ) (f : X → ℕ∞)
               → continuous² c ℕ∞-codistance f
               → f-max-≼ⁿ n f
f-minimisation {𝓤} {X} _ 𝓔S 0 _ _
 = pr₁ (𝓔S {𝓤₀} (λ _ → 𝟙) (λ _ → inl *) (0 , (λ _ _ _ _ → *))) , λ _ _ ()
f-minimisation {𝓤} {X} c 𝓔S (succ n) f ϕf
 = Cases (𝓔S-dec c 𝓔S p d ϕ) γ₁ γ₂
 where
  p : X → 𝓤₀ ̇ 
  p x = n ⊏ f x
  d : detachable p
  d x = 𝟚-is-discrete (incl (f x) n) ₁
  ϕ : continuous c p
  pr₁ ϕ = pr₁ (ϕf (succ n))
  pr₂ ϕ x y δ≼cxy px = χ ⁻¹ ∙ px where
    χ : incl (f x) n ≡ incl (f y) n
    χ = sequences.codistance-conceptually₂
          𝟚 𝟚-is-discrete (incl (f x)) (incl (f y)) n
          (pr₂ (ϕf (succ n)) x y δ≼cxy n (under-diagonal₁ n)) n (≤-refl n)
  γ₁ : Σ p → f-max-≼ⁿ (succ n) f
  γ₁ (x₀ , px₀) = x₀ , λ x → ≼ⁿ-top (f x) (f x₀) n px₀
  γ₂ : ((x : X) → ¬ p x) → f-max-≼ⁿ (succ n) f
  γ₂ g = x₀ , λ x → ≼ⁿ-back (f x) (f x₀) n (g x) (γ₀ x)
   where
    IH = f-minimisation c 𝓔S n f ϕf
    x₀ = pr₁ IH
    γ₀ = pr₂ IH

minimisation-convergence
       : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
       → (cx : X → X → ℕ∞)
       → (𝓔S : c-searchable cx)
       → (ε : ℕ) (M : X → Y) (Φ : Y → Y → ℕ∞) (Ω : Y)
       → continuous² cx Φ M
       → continuous² Φ ℕ∞-codistance (λ y → Φ Ω y)
       → f-max-≼ⁿ ε (λ x → Φ Ω (M x))
minimisation-convergence cx 𝓔S ε M Φ Ω ϕM ϕL
 = f-minimisation cx 𝓔S ε (λ x → Φ Ω (M x)) γ
 where
  γ : continuous² cx ℕ∞-codistance (λ x → Φ Ω (M x))
  γ ε = (pr₁ (ϕM (pr₁ (ϕL ε))))
      , (λ x y δ≼cxy → pr₂ (ϕL ε) (M x) (M y)
           (pr₂ (ϕM (pr₁ (ϕL ε))) x y δ≼cxy))

s-imperfect-convergence
       : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
       → (cx : X → X → ℕ∞) (Φ : Y → Y → ℕ∞)
       → (ϕᴸ : right-continuous Φ)
       → (𝓔S : c-searchable cx)
       → (ε : ℕ)
       → (M : X → Y) (ϕᴹ : continuous² cx Φ M)
       → (Ψ : Y → Y) (k : X)
       → let
           Ω = M k
           ΨΩ = Ψ Ω
           reg = p-regressor cx Φ ϕᴸ 𝓔S ε
           ω = M (reg M ϕᴹ ΨΩ)
         in (under ε ≼ Φ ΨΩ Ω) → (under ε ≼ Φ ΨΩ ω)
s-imperfect-convergence {𝓤} {𝓥} {X} {Y} cx Φ ϕᴸ 𝓔S ε M ϕᴹ Ψ k ε≼Ψ
 = S⟨ cx , 𝓔S ⟩ (p M ϕᴹ ΨΩ) (d M ϕᴹ ΨΩ) (ϕ M ϕᴹ ΨΩ) (k , ε≼Ψ)
 where
  ΨΩ = Ψ (M k)
  p : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y)
    → (X → 𝓤₀ ̇ )
  p M ϕᴹ ΨΩ x = under ε ≼ Φ ΨΩ (M x)
  d : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y)
    → detachable (p M ϕᴹ ΨΩ)
  d M ϕᴹ ΨΩ x = ≼-decidable ε (Φ ΨΩ (M x))
  ϕ : (M : X → Y) (ϕᴹ : continuous² cx Φ M) (ΨΩ : Y)
    → continuous cx (p M ϕᴹ ΨΩ)
  ϕ M ϕᴹ ΨΩ = δ' , γ' where
    δ' : ℕ
    δ' = pr₁ (ϕᴹ ε)
    γ' : uc-mod-of cx (p M ϕᴹ ΨΩ) δ'
    γ' x y δ≼cxy = ≼-continuous ε (Φ ΨΩ (M x)) (Φ ΨΩ (M y))
                     (ϕᴸ ε ΨΩ (M x) (M y)
                     (pr₂ (ϕᴹ ε) x y δ≼cxy))
perfect-convergence
       : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
       → (cx : X → X → ℕ∞) (Φ : Y → Y → ℕ∞)
       → everywhere-sin Φ
       → (ϕᴸ : right-continuous Φ)
       → (𝓔S : c-searchable cx)
       → (ε : ℕ)
       → (M : X → Y) (ϕᴹ : continuous² cx Φ M)
       → (k : X)
       → let
           Ω = M k
           reg = p-regressor cx Φ ϕᴸ 𝓔S ε
           ω = M (reg M ϕᴹ Ω)
         in (under ε ≼ Φ Ω ω)
perfect-convergence {𝓤} {𝓥} {X} {Y} cx Φ ϕ→ ϕᴸ 𝓔S ε M ϕᴹ k
 = s-imperfect-convergence cx Φ ϕᴸ 𝓔S ε M ϕᴹ id k (λ n _ → ϕ→ (M k) n)

w-imperfect-convergence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
       → (cx : X → X → ℕ∞) (Φ : Y → Y → ℕ∞)
       → (ϕᴸ : right-continuous Φ)
       → (𝓔S : c-searchable cx)
       → (ε : ℕ)
       → (M : X → Y) (ϕᴹ : continuous² cx Φ M)
       → (Ψ : Y → Y) (k : X)
       → let
           Ω = M k
           ΨΩ = Ψ Ω
           reg = p-regressor cx Φ ϕᴸ 𝓔S ε
           ω = M (reg M ϕᴹ ΨΩ)
         in (under ε ≼ Φ ΨΩ Ω)
          → (under ε ≼ ℕ∞-codistance (Φ Ω ΨΩ) (Φ Ω ω))
w-imperfect-convergence {𝓤} {𝓥} {X} {Y} cx Φ ϕᴸ 𝓔S ε M ϕᴹ Ψ k ε≼Φ
 = ≈→≼ 𝟚-is-discrete (incl (Φ Ω ΨΩ)) (incl (Φ Ω ω)) ε
    (ϕᴸ ε Ω ΨΩ ω (s-imperfect-convergence cx Φ ϕᴸ 𝓔S ε M ϕᴹ Ψ k ε≼Φ))
 where
   Ω = M k
   ΨΩ = Ψ Ω
   reg = p-regressor cx Φ ϕᴸ 𝓔S ε
   ω = M (reg M ϕᴹ ΨΩ)

sampled-loss-function : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → (Y → Y → ℕ∞) → (d : ℕ) → X ^⟨succ d ⟩
                      → (X → Y) → (X → Y) → ℕ∞
sampled-loss-function {𝓤} {𝓥} {X} {Y} cy d v f g
 = ×ⁿ-codistance cy d (vec-map f v) (vec-map g v)

sampled-loss-everywhere-sin
               : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → (cy : Y → Y → ℕ∞) (d : ℕ) (xs : X ^⟨succ d ⟩)
               → everywhere-sin cy
               → everywhere-sin (sampled-loss-function cy d xs)
sampled-loss-everywhere-sin cy 0 xs cy→ f = cy→ (f xs)
sampled-loss-everywhere-sin cy (succ d) (x , xs) cy→ f n
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (cy→ (f x) n)
     (sampled-loss-everywhere-sin cy d xs cy→ f n)

sampled-loss-right-continuous
               : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → (cy : Y → Y → ℕ∞)
               → right-continuous cy
               → (d : ℕ) → (xs : X ^⟨succ d ⟩)
               → right-continuous (sampled-loss-function cy d xs)
sampled-loss-right-continuous cy cy-r d xs ε z x y ε≼cxy
 = ×ⁿ-right-continuous cy d cy-r ε
     (vec-map z xs) (vec-map x xs) (vec-map y xs) ε≼cxy

if_then_else_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → decidable X → Y → Y → Y
if (inl _) then y₀ else _ = y₀
if (inr _) then _ else y₁ = y₁

if-elim₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (d : decidable X) {y₁ y₂ : Y}
         → (x : X) → if d then y₁ else y₂ ≡ y₁
if-elim₁ (inl _ ) _ = refl
if-elim₁ (inr ¬x) x = 𝟘-elim (¬x x)

if-elim₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (d : decidable X) {y₁ y₂ : Y}
         → (¬x : ¬ X) → if d then y₁ else y₂ ≡ y₂
if-elim₂ (inl x) ¬x = 𝟘-elim (¬x x)
if-elim₂ (inr _)  _ = refl

order : 𝓤 ̇ → 𝓤 ⁺ ̇
order {𝓤} X = Σ _≤'_ ꞉ (X → X → 𝓤 ̇ )
            , ((x y   : X)   → decidable (x ≤' y))
            × ({x     : X}   → x ≤' x)
            × ({x y z : X}   → ¬ (x ≤' y) → ¬ (y ≤' z) → ¬ (x ≤' z))

fst : {X : 𝓤 ̇ } (d : ℕ) → X ^⟨succ d ⟩ → X
fst 0 x = x
fst (succ _) (x , _) = x

ordered : {X : 𝓤 ̇ } (d : ℕ) → order X → X ^⟨succ d ⟩ → 𝓤 ̇
ordered 0 (_≤'_ , q) xs = 𝟙
ordered (succ d) (_≤'_ , q) (y₀ , ys)
 = ¬ (fst d ys ≤' y₀) × ordered d (_≤'_ , q) ys

c-interpolation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (o : order X) (d : ℕ)
                → X ^⟨succ d ⟩
                → (X → Y) → (X → Y)
c-interpolation _ 0 x₀ f _ = f x₀
c-interpolation (_≤'_ , ≤'-dec , q) (succ d) (x₀ , xs) f x
 = if   (≤'-dec x x₀) then f x₀
   else (c-interpolation (_≤'_ , ≤'-dec , q) d xs f x)

c-int-≡ : {Y₁ : 𝓥 ̇ } {Y₂ : 𝓦 ̇ }
        → (d : ℕ)
        → (y : Y₁) (ys : Y₁ ^⟨succ d ⟩)
        → ((_≤'_ , ≤'-dec , ≤'-refl) : order Y₁)
        → (f g : Y₁ → Y₂)
        → ordered (succ d) (_≤'_ , ≤'-dec , ≤'-refl) (y , ys)
        → (vec-map (λ y' → if ≤'-dec y' y then f y else g y') ys)
        ≡ (vec-map g ys)
c-int-≡ zero y₀ y₁ (_≤'_ , ≤'-dec ,  ≤'-refl , ≤'-trans) f g or
 = if-elim₂ (≤'-dec y₁ y₀) (pr₁ or)
c-int-≡ (succ d) y₀ (y₁ , ys) (_≤'_ , ≤'-dec ,  ≤'-refl , ≤'-trans) f g or
 = ×-≡ (if-elim₂ (≤'-dec y₁ y₀) (pr₁ or))
       (c-int-≡ d y₀ ys (_≤'_ , ≤'-dec ,  ≤'-refl , ≤'-trans) f g
         (≤'-trans (pr₁ (pr₂ or)) (pr₁ or) , pr₂ (pr₂ or)))

interpolated-slf-minimises-loss : {Y₁ : 𝓥 ̇ } {Y₂ : 𝓦 ̇ }
      → (cy : Y₂ → Y₂ → ℕ∞) (d : ℕ) (ys : Y₁ ^⟨succ d ⟩)
      → ((y : Y₂) → Π (_⊏ cy y y))
      → (o₁ : order Y₁) → ordered d o₁ ys
      → (Ω : Y₁ → Y₂) (ε : ℕ)
      → under ε ≼ sampled-loss-function cy d ys
                    (c-interpolation o₁ d ys Ω) Ω
interpolated-slf-minimises-loss cy 0 y cy→ _ _ Ω _ n _ = cy→ (Ω y) n
interpolated-slf-minimises-loss cy (succ d) (y , ys) cy→
                                (_≤'_ , ≤'-dec , ≤'-refl , ≤'-trans) or Ω ε
 = ×-codistance-min cy (sampled-loss-function cy d ys) (under ε) _ _
  (c-interpolation o₁ (succ d) (y , ys) Ω) Ω
    (λ n _ → transport (λ - → n ⊏ cy - (Ω y))
      (if-elim₁ (≤'-dec y y) ≤'-refl ⁻¹) (cy→ (Ω y) n))
    (transport (λ - → under ε ≼ ×ⁿ-codistance cy d - (vec-map Ω ys))
      (c-int-≡ d y ys o₁ Ω
        (c-interpolation (_≤'_ , ≤'-dec , ≤'-refl , ≤'-trans) d ys Ω) or ⁻¹)
      (interpolated-slf-minimises-loss cy d ys cy→ o₁ (pr₂ or) Ω ε))
 where
   o₁ : order _
   o₁ = (_≤'_ , ≤'-dec , ≤'-refl , ≤'-trans)

interpolation-theorem : {X : 𝓤 ̇ } {Y₁ : 𝓥 ̇ } {Y₂ : 𝓦 ̇ }
       → (cx : X → X → ℕ∞) (cy : Y₂ → Y₂ → ℕ∞)
       → everywhere-sin cy
       → (cy-r : right-continuous cy)
       → (𝓔S : c-searchable cx)
       → (o : order Y₁) (d : ℕ)
       → (ys : Y₁ ^⟨succ d ⟩) (or : ordered d o ys)
       → let
           Φ = sampled-loss-function cy d ys
           ϕᴸ = sampled-loss-right-continuous cy cy-r d ys
           Ψ = c-interpolation o d ys
         in (ε : ℕ)
       → (M : X → (Y₁ → Y₂)) (ϕᴹ : continuous² cx Φ M)
       → (k : X)
       → let
           Ω = M k
           ΨΩ = Ψ Ω
           reg = p-regressor cx Φ ϕᴸ 𝓔S ε
           ω = M (reg M ϕᴹ ΨΩ)
         in (under ε ≼ Φ ΨΩ ω)
interpolation-theorem cx cy cy→ cy-r 𝓔S o d ys or ε M ϕᴹ k
 = s-imperfect-convergence cx Φ ϕᴸ 𝓔S ε M ϕᴹ Ψ k
     (interpolated-slf-minimises-loss cy d ys cy→ o or Ω ε)
 where
  Φ = sampled-loss-function cy d ys
  Ψ = c-interpolation o d ys
  Ω = M k
  ϕᴸ = sampled-loss-right-continuous cy cy-r d ys
