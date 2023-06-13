{-# OPTIONS --without-K --exact-split --safe #-}

open import Thesis.Chapter5.Prelude renaming (map to map')
open import UF.FunExt
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Quotient
open import Thesis.Chapter5.SignedDigit
open import MLTT.Two-Properties
open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import TypeTopology.DiscreteAndSeparated

module Thesis.Chapter4.ConvergenceTheorems (fe : FunExt) where

open import Thesis.Chapter3.ClosenessSpaces fe
open import Thesis.Chapter3.ClosenessSpaces-Examples fe
open import Thesis.Chapter3.SearchableTypes fe
open import Thesis.Chapter4.ApproxOrder fe
open import Thesis.Chapter4.ApproxOrder-Examples fe
open import Thesis.Chapter4.GlobalOptimisation fe
open import UF.Subsingletons-FunExt  

-- Definition 4.2.10 (Does not have continuity of M!)
regressor : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥) → 𝓤 ⊔ 𝓥  ̇
regressor {𝓤} {𝓥} X Y
 = (M : ⟨ X ⟩ → ⟨ Y ⟩) → f-ucontinuous X Y M → ⟨ Y ⟩ → ⟨ X ⟩

C-ucontinuous : (X : ClosenessSpace 𝓤)
              → (ε : ℕ) (x : ⟨ X ⟩) → p-ucontinuous X (CΩ X ε x)
C-ucontinuous X ε x = ε , γ
 where
  γ : (y z : ⟨ X ⟩) → C X ε y z → C X ε x y → C X ε x z
  γ y z Cyz Cxy = C-trans X ε x y z Cxy Cyz

-- TODO: Fix overloaded Ω
p-regressor : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → (𝓔S : csearchable 𝓤₀ X)
            → (ε : ℕ) → regressor X Y
p-regressor {𝓤} {𝓥} X Y (𝓔 , S) ε M ϕᴹ Ω' = 𝓔 ((p , d) , ϕ)
 where
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = CΩ Y ε Ω' (M x)
  d : is-complemented (λ x → p x holds)
  d x = C-decidable Y ε Ω' (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Cδx₁x₂ px₁
     = C-trans Y ε Ω' (M x₁) (M x₂) px₁ (pr₂ (ϕᴹ ε) x₁ x₂ Cδx₁x₂)

ℕ∞-≽-preorder : is-preorder _≽_
ℕ∞-≽-preorder = r , t , p
 where
  r : reflexive _≽_
  r x n = id
  t : transitive _≽_
  t x y z x≽z y≽z n = x≽z n ∘ (y≽z n)
  p : is-prop-valued _≽_
  p x y = ≼-is-prop-valued (fe _ _) y x

-- Global min of _≽_ is the global max of _≼_
-- Not covered in paper on this section very well
_≽ⁿ_ : ℕ∞ → ℕ∞ → ℕ → 𝓤₀ ̇
(u ≽ⁿ v) n = (i : ℕ) → i < n → i ⊏ v → i ⊏ u

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
 → (_≤_ : ⟨ X ⟩ → ⟨ X ⟩ → 𝓥 ̇ ) (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓥' ̇ )
 → is-approx-order X _≤_ _≤ⁿ_
 → let _≥_  = invert-rel  _≤_  in
   let _≥ⁿ_ = invert-rel' _≤ⁿ_ in
   is-approx-order X _≥_ _≥ⁿ_
invert-approx-order-is-approx-order X _≤_ _≤ⁿ_ (pre' , lin' , c' , a')
 = pre , lin , c , a
 where
  pre : is-preorder (invert-rel _≤_)
  pre = invert-preorder-is-preorder _≤_ pre'
  lin : (ϵ : ℕ) → is-linear-order (λ x y → invert-rel' _≤ⁿ_ x y ϵ)
  lin ϵ = (r'
        , (λ x y z q r → t' z y x r q)
        , λ x y → p' y x)
        , λ x y → l' y x
   where
    r' = (pr₁ ∘ pr₁)       (lin' ϵ)
    t' = (pr₁ ∘ pr₂ ∘ pr₁) (lin' ϵ)
    p' = (pr₂ ∘ pr₂ ∘ pr₁) (lin' ϵ)
    l' = pr₂               (lin' ϵ)
  c : (ϵ : ℕ) (x y : ⟨ X ⟩) → C X ϵ x y → invert-rel' _≤ⁿ_ x y ϵ
  c ϵ x y Cxy = c' ϵ y x (C-sym X ϵ x y Cxy)
  a : (ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ C X ϵ x y → invert-rel' _≤ⁿ_ x y ϵ
                                          ⇔ invert-rel _≤_ x y
  a ϵ x y ¬Cxy = a' ϵ y x (λ Cyx → 𝟘-elim (¬Cxy (C-sym X ϵ y x Cyx)))

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
     (invert-rel ℕ∞-lexicorder) (invert-rel' ℕ∞-approx-lexicorder)
     (invert-approx-order-is-approx-order ℕ∞-ClosenessSpace
       ℕ∞-lexicorder ℕ∞-approx-lexicorder
         ℕ∞-approx-lexicorder-is-approx-order)
     ϵ f ϕ t

-- Theorem 4.2.8
optimisation-convergence
       : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
       → ⟨ X ⟩ → totally-bounded X 𝓤'
       → (M : ⟨ X ⟩ → ⟨ Y ⟩) (Ω : ⟨ Y ⟩)
       → f-ucontinuous X Y M
       → let c = pr₁ (pr₂ Y) in
         f-ucontinuous Y ℕ∞-ClosenessSpace (c Ω)
       → (ϵ : ℕ)
       → (has ϵ global-maximal) ℕ∞-approx-lexicorder (λ x → c Ω (M x))
optimisation-convergence X Y x₀ t M Ω ϕᴹ ϕᶜ
 = global-max-ℕ∞ X x₀ t (c Ω ∘ M)
     (λ ϵ → pr₁ (ϕᴹ (pr₁ (ϕᶜ ϵ)))
          , λ x₁ x₂ Cδᶜx₁x₂ → pr₂ (ϕᶜ ϵ) (M x₁) (M x₂)
                               (pr₂ (ϕᴹ (pr₁ (ϕᶜ ϵ))) x₁ x₂ Cδᶜx₁x₂))
 where
  c : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ∞
  c = pr₁ (pr₂ Y)

-- Make sure the fixed oracle is on the left (in paper too)
-- Theorem 4.2.12
s-imperfect-convergence
       : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
       → (𝓔S : csearchable 𝓤₀ X)
       → (ε : ℕ)
       → (M : ⟨ X ⟩ → ⟨ Y ⟩) (ϕᴹ : f-ucontinuous X Y M)
       → (Ψ : ⟨ Y ⟩ → ⟨ Y ⟩) (k : ⟨ X ⟩)
       → let
           Ω = M k
           ΨΩ = Ψ Ω
           reg = p-regressor X Y 𝓔S ε
           ω = M (reg M ϕᴹ ΨΩ)
         in (C Y ε Ω ΨΩ) → (C Y ε Ω ω)
s-imperfect-convergence X Y (𝓔 , S) ε M ϕᴹ Ψ k CεΩΨΩ
 = C-trans Y ε Ω' ΨΩ ω CεΩΨΩ (S ((p , d) , ϕ) (k , C-sym Y ε Ω' ΨΩ CεΩΨΩ))
 where
  Ω' = M k -- fix Ω definition in paper and agda
  ΨΩ = Ψ Ω'
  reg = p-regressor X Y (𝓔 , S) ε
  ω = M (reg M ϕᴹ ΨΩ)
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = CΩ Y ε ΨΩ (M x)
  d : is-complemented (λ x → p x holds)
  d x = C-decidable Y ε ΨΩ (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Cδx₁x₂ CεΨΩMx₂
     = C-trans Y ε ΨΩ (M x₁) (M x₂) CεΨΩMx₂
         (pr₂ (ϕᴹ ε) x₁ x₂ Cδx₁x₂)

perfect-convergence
       : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
       → (𝓔S : csearchable 𝓤₀ X)
       → (ε : ℕ)
       → (M : ⟨ X ⟩ → ⟨ Y ⟩) (ϕᴹ : f-ucontinuous X Y M)
       → (k : ⟨ X ⟩)
       → let
           Ω = M k
           reg = p-regressor X Y 𝓔S ε
           ω = M (reg M ϕᴹ Ω)
         in C Y ε Ω ω
perfect-convergence X Y 𝓔S ε M ϕᴹ k
 = s-imperfect-convergence X Y 𝓔S ε M ϕᴹ id k (C-refl Y ε Ω')
 where Ω' = M k

{-
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
-}
