{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

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

-- open import Thesis.Chapter3.ClosenessSpaces fe {!!} {!!} {!!}
open import Thesis.Chapter3.SearchableTypes fe
open import Thesis.Chapter6.SignedDigitContinuity fe
open import UF.Subsingletons-FunExt 

-- Definition 4.2.10 (Does not have continuity of M!)
regressor : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥) → 𝓤 ⊔ 𝓥  ̇
regressor {𝓤} {𝓥} X Y
 = (M : ⟨ X ⟩ → ⟨ Y ⟩) → f-ucontinuous X Y M → ⟨ Y ⟩ → ⟨ X ⟩

B-ucontinuous : (X : ClosenessSpace 𝓤)
              → (ε : ℕ) (x : ⟨ X ⟩) → p-ucontinuous X (B* X ε x)
B-ucontinuous X ε x = ε , γ
 where
  γ : (y z : ⟨ X ⟩) → B X ε y z → B* X ε x y holds → B* X ε x z holds
  γ y z Byz Bxy = B-trans X ε x y z Bxy Byz

-- TODO: Fix overloaded Ω
p-regressor : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → (𝓔S : csearchable 𝓤₀ X)
            → (ε : ℕ) → regressor X Y
p-regressor {𝓤} {𝓥} X Y (𝓔 , S) ε M ϕᴹ Ω' = 𝓔 ((p , d) , ϕ)
 where
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = B* Y ε Ω' (M x)
  d : is-complemented (λ x → p x holds)
  d x = B-decidable Y ε Ω' (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → B X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Bδx₁x₂ px₁
     = B-trans Y ε Ω' (M x₁) (M x₂) px₁ (pr₂ (ϕᴹ ε) x₁ x₂ Bδx₁x₂)

open import Thesis.Chapter4.GlobalOptimisation fe

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

open import TWA.Closeness fe hiding (is-ultra; is-closeness)

Σ-clofun : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ )
         → ((x : X) → is-prop (P x))
         → Σ cx ꞉ (X → X → ℕ∞) , is-closeness cx
         → Σ c ꞉ (Σ P → Σ P → ℕ∞) , is-closeness c
Σ-clofun {𝓤} {𝓥} {X} P p (cx , ex , ix , sx , ux) = c , e , i , s , u
 where
  c : Σ P → Σ P → ℕ∞
  c (x , _) (y , _) = cx x y
  e : indistinguishable-are-equal c
  e (x , _) (y , _) cxy=∞ = to-subtype-＝ p (ex x y cxy=∞)
  i : self-indistinguishable c
  i (x , _) = ix x
  s : is-symmetric c
  s (x , _) (y , _) = sx x y
  u : is-ultra c
  u (x , _) (y , _) (z , _) = ux x y z

Σ-ClosenessSpace : (X : ClosenessSpace 𝓤)
                 → (P : ⟨ X ⟩ → 𝓥 ̇ ) → ((x : ⟨ X ⟩) → is-prop (P x))
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
Σ-ClosenessSpace {𝓤} {𝓥} (X , cx) P p = Σ P  , Σ-clofun P p cx

ℕ→𝟚-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ→𝟚-ClosenessSpace = ℕ→D-ClosenessSpace 𝟚-is-discrete

ℕ∞-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ∞-ClosenessSpace = Σ-ClosenessSpace ℕ→𝟚-ClosenessSpace is-decreasing
                     (being-decreasing-is-prop (fe _ _))


{-
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
-}
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
         in (B Y ε Ω ΨΩ) → (B Y ε Ω ω)
s-imperfect-convergence X Y (𝓔 , S) ε M ϕᴹ Ψ k BεΩΨΩ
 = B-trans Y ε Ω' ΨΩ ω BεΩΨΩ (S ((p , d) , ϕ) (k , B-sym Y ε Ω' ΨΩ BεΩΨΩ))
 where
  Ω' = M k -- fix Ω definition in paper and agda
  ΨΩ = Ψ Ω'
  reg = p-regressor X Y (𝓔 , S) ε
  ω = M (reg M ϕᴹ ΨΩ)
  p : ⟨ X ⟩ → Ω 𝓤₀
  p x = B* Y ε ΨΩ (M x)
  d : is-complemented (λ x → p x holds)
  d x = B-decidable Y ε ΨΩ (M x)
  ϕ : p-ucontinuous X p
  ϕ = δ , γ
   where
    δ : ℕ
    δ = pr₁ (ϕᴹ ε)
    γ : (x₁ x₂ : ⟨ X ⟩) → B X δ x₁ x₂ → p x₁ holds → p x₂ holds
    γ x₁ x₂ Bδx₁x₂ BεΨΩMx₂
     = B-trans Y ε ΨΩ (M x₁) (M x₂) BεΨΩMx₂
         (pr₂ (ϕᴹ ε) x₁ x₂ Bδx₁x₂)

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
         in B Y ε Ω ω
perfect-convergence X Y 𝓔S ε M ϕᴹ k
 = s-imperfect-convergence X Y 𝓔S ε M ϕᴹ id k (B-refl Y ε Ω')
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
