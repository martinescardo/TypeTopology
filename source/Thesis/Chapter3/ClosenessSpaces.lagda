\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import CoNaturals.GenericConvergentSequence
open import Notation.Order
open import UF.Subsingletons
open import UF.PropTrunc
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Base
open import UF.Retracts
open import UF.Miscelanea
open import MLTT.Two-Properties
open import UF.Equiv

module Thesis.Chapter3.ClosenessSpaces
 (fe : FunExt)
 (pe : PropExt)
 (pt : propositional-truncations-exist)
 (sq : set-quotients-exist)
 where

open import CoNaturals.Arithmetic fe hiding (min)
open import TWA.Closeness fe
open PropositionalTruncation pt

_≡_ = Id
_↑ = ℕ-to-ℕ∞

is-ultra' is-closeness' : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇
is-ultra' {𝓤} {X} c
 = (x y z : X) → (n : ℕ) → min (c x y) (c y z) ≼ c x z

is-closeness' c
 = indistinguishable-are-equal c
 × self-indistinguishable c
 × is-symmetric c
 × is-ultra' c

is-closeness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-closeness-space X = Σ c ꞉ (X → X → ℕ∞) , is-closeness' c

ClosenessSpace : 𝓤 ⁺  ̇ 
ClosenessSpace {𝓤}
 = Σ X ꞉ 𝓤 ̇ , Σ c ꞉ (X → X → ℕ∞) , is-closeness' c

cloeq' : ((X , _) : ClosenessSpace {𝓤}) → ℕ → X → X → 𝓤₀  ̇   
cloeq' (X , c , _) n x y = (n ↑) ≼ c x y 

clotoeq : (C : ClosenessSpace {𝓤})
        → (n : ℕ) → is-equiv-relation (cloeq' C n)
pr₁ (clotoeq (X , c , i , j , k , l) n) x y
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → 𝟚-is-set))
pr₁ (pr₂ (clotoeq (X , c , i , j , k , l) n)) x m η
 = transport (λ - → ℕ∞-to-ℕ→𝟚 - m ≡ ₁) (j x ⁻¹) refl
pr₁ (pr₂ (pr₂ (clotoeq (X , c , i , j , k , l) n))) x y η m ρ
 = transport (λ - → ℕ∞-to-ℕ→𝟚 - m ≡ ₁) (k x y) (η m ρ)
pr₂ (pr₂ (pr₂ (clotoeq (X , c , i , j , k , l) n))) x y z η ρ m π
 = l x y z n m ((Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (η m π) (ρ m π)))

cloeq : ((X , ci) : ClosenessSpace {𝓤}) → (n : ℕ) → EqRel X
cloeq C n = cloeq' C n , clotoeq C n

searchable : (X : 𝓤 ̇ ) → 𝓤 ⊔ 𝓦 ⁺   ̇
searchable {𝓤} {𝓦} X
 = (p : X → Ω 𝓦)
 → Σ x₀ ꞉ X , ((Σ x ꞉ X , (p x) holds) → (p x₀) holds)

u-continuous-pred
 : ((X , _) : ClosenessSpace {𝓤}) → (p : X → Ω 𝓦) → 𝓤 ⊔ 𝓦 ̇
u-continuous-pred (X , c , i) p
 = Σ δ ꞉ ℕ
 , ((x₁ x₂ : X) → (δ ↑) ≼ c x₁ x₂ → (p x₁) holds ⇔ (p x₂) holds)

c-searchable : ((X , cx) : ClosenessSpace {𝓤}) → 𝓤 ⊔ 𝓦 ⁺ ̇
c-searchable {𝓤} {𝓦} (X , ci)
 = (p : X → Ω 𝓦) → u-continuous-pred (X , ci) p
 → Σ x₀ ꞉ X , ((Σ x ꞉ X , (p x) holds) → (p x₀) holds)

open set-quotients-exist sq

semi-searchable : (C : ClosenessSpace {𝓤}) → 𝓤 ⊔ 𝓦 ⁺  ̇ 
semi-searchable {𝓤} {𝓦} (X , ci)
 = (n : ℕ) → searchable {𝓤} {𝓦} (X / cloeq (X , ci) n)

open extending-relations-to-quotient

quotient-uc-predicate : ((X , ci) : ClosenessSpace {𝓤})
                      → (p : X → Ω 𝓦)
                      → ((δ , _) : u-continuous-pred (X , ci) p)
                      → Σ p' ꞉ (X / cloeq (X , ci) δ → Ω 𝓦)
                      , ((x : X)
                      → (p' (η/ (cloeq (X , ci) δ) x)) ≡ (p x))
quotient-uc-predicate (X , c , i) p (δ , ϕ)
 = pr₁ (/-universality (cloeq (X , c , i) δ) (Ω-is-set (fe _ _) (pe _))
     p (λ η → Ω-extensionality (fe _ _) (pe _)
     (pr₁ (ϕ _ _ η)) (pr₂ (ϕ _ _ η))))

quotient-uc-predicate⇔ : ((X , ci) : ClosenessSpace {𝓤})
                       → (p : X → Ω 𝓦)
                       → ((δ , ϕ) : u-continuous-pred (X , ci) p)
                       → ((x : X)
                       → let p' = pr₁ (quotient-uc-predicate (X , ci) p (δ , ϕ)) in
                         (p' (η/ (cloeq (X , ci) δ) x)) holds
                       ⇔ (p x) holds)
quotient-uc-predicate⇔ C p ϕ x
 = transport (_holds) (pr₂ (quotient-uc-predicate C p ϕ) x   )
 , transport (_holds) (pr₂ (quotient-uc-predicate C p ϕ) x ⁻¹)

semi-searchable⇒c-searchable : ((X , ci) : ClosenessSpace {𝓤})
                             → ((n : ℕ) → has-section (η/ (cloeq (X , ci) n)))
                             → semi-searchable {𝓤} {𝓦} (X , ci)
                             →    c-searchable {𝓤} {𝓦} (X , ci)
semi-searchable⇒c-searchable {𝓤} {𝓦} (X , ci) r S p (δ , ϕ)
 = x₀ , λ (x , px) → p'→p x₀
          (transport (λ - → p' - holds)
            γ₀ (γ₀/ (η/ (cloeq (X , ci) δ) x , p→p' x px)))
 where
   X/ = X / cloeq (X , ci) δ
   p' : X/ → Ω 𝓦
   p' = pr₁ (quotient-uc-predicate (X , ci) p (δ , ϕ))
   p'→p : (x : X) → p' (η/ (cloeq (X , ci) δ) x) holds → (p x holds)
   p'→p x = pr₁ (quotient-uc-predicate⇔ (X , ci) p (δ , ϕ) x)
   p→p' : (x : X) → (p x holds) → p' (η/ (cloeq (X , ci) δ) x) holds
   p→p' x = pr₂ (quotient-uc-predicate⇔ (X , ci) p (δ , ϕ) x)
   ζ = S δ p'
   x₀/ : X / cloeq (X , ci) δ
   x₀/ = pr₁ ζ
   γ₀/ : (Σ x ꞉ X/ , p' x holds) → p' x₀/ holds
   γ₀/ = pr₂ ζ
   x₀ : X
   x₀ = pr₁ (r δ) x₀/
   γ₀ : x₀/ ＝ η/ (cloeq (X , ci) δ) x₀
   γ₀ = pr₂ (r δ) x₀/ ⁻¹
   
Σ-Closeness : {X : 𝓤 ̇ } → is-closeness-space X
            → (P : X → 𝓥 ̇ ) → ((x : X) → is-prop (P x))
            → is-closeness-space (Σ P)
Σ-Closeness (c , i₀ , i₁ , i₂ , i₃) P i = c' , i₀' , i₁' , i₂' , i₃'
 where
  c'  : Σ P → Σ P → ℕ∞
  c'  (x , a) (y , b) = c x y
  i₀' : indistinguishable-are-equal c'
  i₀' (x , a) (y , b) q = to-Σ-＝ ((i₀ x y q) , i _ _ b)
  i₁' : (x : Σ P) → c' x x ＝ ∞
  i₁' (x , a) = i₁ x
  i₂' : is-symmetric c'
  i₂' (x , a) (y , b) = i₂ x y
  i₃' : is-ultra' c'
  i₃' (x , a) (y , b) (z , c) = i₃ x y z
{-
ordered : (X : 𝓤 ̇ ) → 𝓤 ⊔ 𝓥 ⁺  ̇
ordered {𝓤} {𝓥} X = Σ _≤_ ꞉ (X → X → 𝓥  ̇ )
                   , reflexive _≤_
                   × transitive _≤_
                   × ((x y : X) → ¬ (x ≤ y) → y ≤ x)

totally-ordered : {X : 𝓤 ̇ } → ordered {𝓤} {𝓥} X → 𝓤 ⊔ 𝓥  ̇
totally-ordered {𝓤} {𝓥} {X} (_≤_ , _) = (x y : X) → is-complemented (x ≤ y)

data List (X : 𝓤 ̇ ) : 𝓤 ̇ where
  [] : List X
  _::_ : X → List X → List X

_∈_ : {X : 𝓤 ̇ } → X → List X → 𝓤 ̇
x ∈ [] = 𝟘
x ∈ (y :: xs) = (x ≡ y) + (x ∈ xs)

fin-has-minimal : {X : 𝓤 ̇ } → ((_≤_ , q) : ordered {𝓤} {𝓥} X)
                → totally-ordered (_≤_ , q)
                → (x : X) (xs : List X)
                → Σ x₀ ꞉ X , (x₀ ∈ (x :: xs))
                × ((x' : X) → x' ∈ (x :: xs) → x₀ ≤ x')
fin-has-minimal (_≤_ , r , t , a) d x []
 = x , (inl refl , λ x' → cases (λ e → transport (_≤ x') e (r x')) 𝟘-elim)
fin-has-minimal (_≤_ , r , t , a) d x (x' :: xs)
 = Cases (d x x₀)
     (λ x≤x₀ → x , (inl refl , (λ x'' → cases
       (λ e → transport (_≤ x'') e (r x''))
       (t x x₀ x'' x≤x₀ ∘ (pr₂ γ₀ x'')))))
     (λ ¬x≤x₀ → x₀ , (inr (pr₁ γ₀)) , (λ x'' → cases
       (λ e → transport (x₀ ≤_) (e ⁻¹) (a x x₀ ¬x≤x₀))
       (pr₂ γ₀ x'')))
 where
   IH = fin-has-minimal (_≤_ , r , t , a) d x' xs
   x₀ = pr₁ IH
   γ₀ : (x₀ ∈ (x' :: xs)) × (∀ x'' → x'' ∈ (x' :: xs) → x₀ ≤ x'')
   γ₀ = pr₂ IH

approx-ordered : {(X , _) : ClosenessSpace {𝓤}} → ordered {𝓤} {𝓥} X
               → 𝓤 ⊔ 𝓥 ⁺  ̇
approx-ordered {𝓤} {𝓥} {(X , c , _)} (_≤_ , _)
 = Σ _≤'_ ꞉ (X → X → ℕ → 𝓥 ̇ )
 , ((x y : X) (ϵ : ℕ) → (ϵ ↑) ≼ c x y → (x ≤' y) ϵ)
 × ((x y : X) (ϵ : ℕ) → c x y ≺ (ϵ ↑) → (x ≤' y) ϵ ⇔ x ≤ y)

approx-refl : {(X , ci) : ClosenessSpace {𝓤}} → (o : ordered {𝓤} {𝓥} X)
            → ((_≤'_ , _) : approx-ordered {𝓤} {𝓥} {(X , ci)} o)
            → (ϵ : ℕ) → reflexive (λ x y → (x ≤' y) ϵ)
approx-refl {𝓤} {𝓥} {(X , c , i₀ , i₁ , i₂ , i₃)} (_≤_ , r , t , a)
 (_≤'_ , p , q) ϵ x
 = p x x ϵ (transport ((ϵ ↑) ≼_) (i₁ x ⁻¹) (∞-largest (ϵ ↑)))

≼-decidable : (x : ℕ∞) (ϵ : ℕ) → ((ϵ ↑) ≼ x) + (x ≺ (ϵ ↑))
≼-decidable = {!!}

approx-trans : {(X , c , i) : ClosenessSpace {𝓤}} → (o : ordered {𝓤} {𝓥} X)
             → ((_≤'_ , _) : approx-ordered {𝓤} {𝓥} {(X , c , i)} o)
             → (ϵ : ℕ) → (x y z : X)
             → ((ϵ ↑) ≼ c x y) + (c x y ≺ (ϵ ↑))
             → ((ϵ ↑) ≼ c y z) + (c y z ≺ (ϵ ↑))
             → ((ϵ ↑) ≼ c x z) + (c x z ≺ (ϵ ↑))
             → (x ≤' y) ϵ → (y ≤' z) ϵ → (x ≤' z) ϵ
approx-trans {𝓤} {𝓥} {X , c , i₀ , i₁ , i₂ , i₃} (_≤_ , r , t , a) (_≤'_ , p , q) ϵ x y z α β (inl x₁) x≤'y y≤'z = p x z ϵ x₁
approx-trans {𝓤} {𝓥} {X , c , i₀ , i₁ , i₂ , i₃} (_≤_ , r , t , a) (_≤'_ , p , q) ϵ x y z (inl x₂) (inl x₃) (inr x₁) x≤'y y≤'z
 = {!!}
approx-trans {𝓤} {𝓥} {X , c , i₀ , i₁ , i₂ , i₃} (_≤_ , r , t , a) (_≤'_ , p , q) ϵ x y z (inl x₂) (inr x₃) (inr x₁) x≤'y y≤'z
 = {!!}
approx-trans {𝓤} {𝓥} {X , c , i₀ , i₁ , i₂ , i₃} (_≤_ , r , t , a) (_≤'_ , p , q) ϵ x y z (inr x₂) (inl x₃) (inr x₁) x≤'y y≤'z
 = {!!}
approx-trans {𝓤} {𝓥} {X , c , i₀ , i₁ , i₂ , i₃} (_≤_ , r , t , a) (_≤'_ , p , q) ϵ x y z (inr x₂) (inr x₃) (inr x₁) x≤'y y≤'z
 = pr₂ (q x z ϵ x₁) (t x y z (pr₁ (q x y ϵ x₂) x≤'y) (pr₁ (q y z ϵ x₃) y≤'z))

subtype : {X : 𝓤 ̇ } → (X → Ω 𝓥) → 𝓤 ⊔ 𝓥  ̇
subtype P = Σ (λ x → P x holds)

_is-_-covered-by_ : (X : 𝓤 ̇ ) → EqRel {𝓤} {𝓦} X → (X → Ω 𝓥) → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
X is- (_≊_ , _) -covered-by P = (x : X) → Σ (x' , _) ꞉ subtype P , (x ≊ x')

_is-_-covered-by'_ : (X : 𝓤 ̇ ) → EqRel {𝓤} {𝓦} X → (Y : 𝓥 ̇ ) → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ̇
X is- (_≊_ , _) -covered-by' Y = Σ f ꞉ (Y → X) , ((x : X) → Σ y ꞉ Y , (x ≊ f y))

cover→cover' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
             → (P : X → Ω 𝓣)
             → X is- (_≊_ , e) -covered-by P
             → X is- (_≊_ , e) -covered-by' (subtype P)
cover→cover' (_≊_ , e) P v = pr₁ , v

cover'→cover : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
             → (P : X → Ω 𝓣)
             → X is- (_≊_ , e) -covered-by' (subtype P)
             → X is- (_≊_ , e) -covered-by P
cover'→cover (_≊_ , e@(e₁ , e₂ , e₃ , e₄)) P (f , v) x
 = pr₁ (v x) , e₄ _ _ _ (pr₂ (v x)) {!!}

quotient-covers : {X : 𝓤 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
                → ((ρ , q) : is-section (η/ (_≊_ , e)))
                → X is- (_≊_ , e) -covered-by' (X / (_≊_ , e))
quotient-covers (_≊_ , e@(_ , r , _)) (ρ , q)
 = ρ , (λ x → (η/ (_≊_ , e) x) , transport (x ≊_) (q _ ⁻¹) (r _))

List-to-Type : {X : 𝓤 ̇ } → List X → 𝓤 ̇
List-to-Type {𝓤} {X} v = Σ x ꞉ X , (x ∈ v)

-- subtype-covers : {X : 𝓤 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
   --            → s

quotient-subtype-equiv' : {X : 𝓤 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
                        → (∀ x y → decidable (x ≊ y))
                        → is-section (η/ (_≊_ , e))
                        → is-set X
                        → Σ P ꞉ (X → Ω {!!})
                        , ((X is- (_≊_ , e) -covered-by P)
                        × (X / (_≊_ , e) ≃ subtype P))
quotient-subtype-equiv' (_≊_ , e@(e₁ , e₂ , e₃ , e₄)) d (ρ , q) i = f , γ₁ , γ₂
 where
  η  = η/ (_≊_ , e)
  ρη = ρ ∘ η
  ηρ = η ∘ ρ
  f  : _ → Ω _
  f x = x ≡ ρη x , i
  f∀ : ∀ x → f (ρη x) holds
  f∀ x = q (ρη x) ⁻¹
  γ₁ : _ is- _≊_ , e -covered-by f
  ext : ∀ x y → η x ≡ η y → x ≊ y
  ext x y η≡ with d x y
  ... | inl h = h
  ... | inr h = 𝟘-elim (dni {!!} h)
   where
     dni : {A : 𝓤 ̇ } → A → ¬¬ A
     dni A ¬A = ¬A A
  γ₁ x = (ρη x , f∀ x) , ext x (ρη x) (ap η (q x ⁻¹))
  γ₂ : (_ / (_≊_ , e)) ≃ subtype f
  γ₂ = {!!}
  
quotient-subtype-equiv : {X : 𝓤 ̇ } → ((_≊_ , e) : EqRel {𝓤} {𝓦} X)
                       → (P : X → Ω 𝓥)
                       → is-section (η/ (_≊_ , e))
                       → X is- (_≊_ , e) -covered-by P
                       → (X / (_≊_ , e)) ≃ subtype P
quotient-subtype-equiv (_≊_ , e) P (ρ , q) v
 = f , (g , γ₁) , (g , γ₂)
 where
   f = (λ x → pr₁ (v (ρ x)))
   g = (λ (x , h) → η/ (_≊_ , e) x)
   γ₁ : (λ x → f (g x)) ∼ (λ x → x)
   γ₁ (x , h) = {!!}
   γ₂ : (λ x → g (f x)) ∼ (λ x → x)
   γ₂ x = {!!}
-}
