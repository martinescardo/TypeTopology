Tom de Jong, 18 December 2020
(Formalizing a paper proof sketch from 12 November 2020)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module FreeJoinSemiLattice
        (pt : propositional-truncations-exist)
       where

open import UF-Subsingletons
open PropositionalTruncation pt hiding (_∨_)

open import Fin hiding (_∷_ ; suc)
open import UF-ImageAndSurjection
open ImageAndSurjection pt

open import UF-Powerset

𝕋_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓤 ̇
𝕋_ {𝓤} {X} A = Σ x ꞉ X , (x ∈ A)

η' : {X : 𝓤 ̇ } → is-set X → X → 𝓟 X
η' i x = (λ y → ((y ≡ x) , i))

∅ : {X : 𝓤 ̇ } → 𝓟 X
∅ x = 𝟘 , 𝟘-is-prop

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ ⊆ A
∅-is-least x _ = 𝟘-induction

_∪_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X
(A ∪ B) x = ∥ x ∈ A + x ∈ B ∥ , ∥∥-is-prop

∪-is-upperbound₁ : {X : 𝓤 ̇ } (A B : 𝓟 X) → A ⊆ (A ∪ B)
∪-is-upperbound₁ A B x a = ∣ inl a ∣

∪-is-upperbound₂ : {X : 𝓤 ̇ } (A B : 𝓟 X) → B ⊆ (A ∪ B)
∪-is-upperbound₂ A B x b = ∣ inr b ∣

∪-is-lowerbound-of-upperbounds : {X : 𝓤 ̇ } (A B C : 𝓟 X)
                               → A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C
∪-is-lowerbound-of-upperbounds {𝓤} {X} A B C s t x =
 ∥∥-rec (∈-is-prop C x) γ
  where
   γ : (x ∈ A + x ∈ B) → x ∈ C
   γ (inl a) = s x a
   γ (inr b) = t x b

is-Kuratowski-finite : (X : 𝓤 ̇ ) → 𝓤 ̇
is-Kuratowski-finite X = ∥ (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → X) , is-surjection e) ∥

being-Kuratowski-finite-is-prop : {X : 𝓤 ̇ } → is-prop (is-Kuratowski-finite X)
being-Kuratowski-finite-is-prop = ∥∥-is-prop

𝓚 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓚 X = Σ A ꞉ 𝓟 X , is-Kuratowski-finite (𝕋 A)

⟨_⟩ : {X : 𝓤 ̇ } → 𝓚 X → 𝓟 X
⟨_⟩ = pr₁

⟨_⟩₂ : {X : 𝓤 ̇} (A : 𝓚 X) → is-Kuratowski-finite (𝕋 ⟨ A ⟩)
⟨_⟩₂ = pr₂

η : {X : 𝓤 ̇ } → is-set X → X → 𝓚 X
η i x = η' i x , κ
 where
  κ : is-Kuratowski-finite (𝕋 η' i x)
  κ = ∣ 1 , e , σ ∣
   where
    e : Fin 1 → 𝕋 η' i x
    e (inr *) = x , refl
    σ : is-surjection e
    σ (x , refl) = ∣ inr * , refl ∣

_⊑[𝓚]_ : {X : 𝓤 ̇ } → 𝓚 X → 𝓚 X → 𝓤 ̇
A ⊑[𝓚] B = ⟨ A ⟩ ⊆ ⟨ B ⟩

⊑[𝓚]-is-reflexive : {X : 𝓤 ̇ } (A : 𝓚 X) → A ⊑[𝓚] A
⊑[𝓚]-is-reflexive {𝓤} {X} A = ⊆-refl ⟨ A ⟩

⊑[𝓚]-is-transitive : {X : 𝓤 ̇ } (A B C : 𝓚 X) → A ⊑[𝓚] B → B ⊑[𝓚] C → A ⊑[𝓚] C
⊑[𝓚]-is-transitive {𝓤} {X} A B C = ⊆-trans ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

open import UF-FunExt
module _
        (fe₁ : funext 𝓤 𝓤)
       where

 ⊑[𝓚]-is-prop : {X : 𝓤 ̇ } (A B : 𝓚 X) → is-prop (A ⊑[𝓚] B)
 ⊑[𝓚]-is-prop {X} A B = ⊆-is-prop fe₁ fe₁ ⟨ A ⟩ ⟨ B ⟩

 module _
        (pe : propext 𝓤)
        (fe₂ : funext 𝓤 (𝓤 ⁺))
       where

  ⊑[𝓚]-is-antisymmetric : {X : 𝓤 ̇ } (A B : 𝓚 X) → A ⊑[𝓚] B → B ⊑[𝓚] A → A ≡ B
  ⊑[𝓚]-is-antisymmetric {X} A B s t =
   to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop)
   (subset-extensionality pe fe₁ fe₂ s t)

  open import UF-Subsingletons-FunExt

  𝓚-is-set : {X : 𝓤 ̇} → is-set (𝓚 X)
  𝓚-is-set {X} =
   subtypes-of-sets-are-sets p s (powersets-are-sets fe₂ fe₁ pe)
    where
     p : 𝓚 X → 𝓟 X
     p = pr₁
     s : left-cancellable p
     s e = to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop) e

open import ArithmeticViaEquivalence
open import UF-Equiv

∪-enum' : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
        → (Fin n → 𝕋 A)
        → (Fin m → 𝕋 B)
        → (Fin n + Fin m) → 𝕋 (A ∪ B)
∪-enum' A B e f (inl k) = (pr₁ (e k)) , ∣ inl (pr₂ (e k)) ∣
∪-enum' A B e f (inr k) = (pr₁ (f k)) , ∣ inr (pr₂ (f k)) ∣

∪-enum : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
       → (Fin n → 𝕋 A)
       → (Fin m → 𝕋 B)
       → Fin (n +' m) → 𝕋 (A ∪ B)
∪-enum A B {n} {m} e f = ∪-enum' A B e f ∘ ⌜ Fin+homo n m ⌝

∪-enum'-is-surjection : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
                        (e : Fin n → 𝕋 A)
                        (f : Fin m → 𝕋 B)
                      → is-surjection e
                      → is-surjection f
                      → is-surjection (∪-enum' A B e f)
∪-enum'-is-surjection A B {n} {m} e f σ τ (x , p) = ∥∥-rec ∥∥-is-prop γ p
  where
   γ : (x ∈ A + x ∈ B)
     → ∃ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
   γ (inl a) = ∥∥-functor γ₁ (σ (x , a))
    where
     γ₁ : (Σ k ꞉ Fin n , e k ≡ (x , a))
        → Σ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
     γ₁ (k , p) = inl k , to-subtype-≡ (∈-is-prop (A ∪ B)) (ap pr₁ p)
   γ (inr b) = ∥∥-functor γ₂ (τ (x , b))
    where
     γ₂ : (Σ k ꞉ Fin m , f k ≡ (x , b))
        → Σ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
     γ₂ (k , p) = inr k , to-subtype-≡ (∈-is-prop (A ∪ B)) (ap pr₁ p)

∪-enum-is-surjection : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
                       (e : Fin n → 𝕋 A)
                       (f : Fin m → 𝕋 B)
                     → is-surjection e
                     → is-surjection f
                     → is-surjection (∪-enum A B e f)
∪-enum-is-surjection A B {n} {m} e f σ τ =
 ∘-is-surjection
  (equivs-are-surjections (⌜⌝-is-equiv (Fin+homo n m)))
  (∪-enum'-is-surjection A B e f σ τ)

_∨[𝓚]_ : {X : 𝓤 ̇ } → 𝓚 X → 𝓚 X → 𝓚 X
_∨[𝓚]_ {𝓤} {X} (A , κ₁) (B , κ₂) = (A ∪ B) , κ
 where
  κ : is-Kuratowski-finite (𝕋 (A ∪ B))
  κ = ∥∥-rec being-Kuratowski-finite-is-prop γ₁ κ₁
   where
    γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
       → is-Kuratowski-finite (𝕋 (A ∪ B))
    γ₁ (n , e , σ) = ∥∥-rec being-Kuratowski-finite-is-prop γ₂ κ₂
     where
      γ₂ : (Σ m ꞉ ℕ , Σ f ꞉ (Fin m → 𝕋 B) , is-surjection f)
         → is-Kuratowski-finite (𝕋 (A ∪ B))
      γ₂ (m , f , τ) = ∣ (n +' m) , g , ρ ∣
       where
        g : Fin (n +' m) → 𝕋 (A ∪ B)
        g = ∪-enum A B e f
        ρ : is-surjection g
        ρ = ∪-enum-is-surjection A B e f σ τ

∨[𝓚]-is-upperbound₁ : {X : 𝓤 ̇ } (A B : 𝓚 X) → A ⊑[𝓚] (A ∨[𝓚] B)
∨[𝓚]-is-upperbound₁ {𝓤} {X} A B = ∪-is-upperbound₁ ⟨ A ⟩ ⟨ B ⟩

∨[𝓚]-is-upperbound₂ : {X : 𝓤 ̇ } (A B : 𝓚 X) → B ⊑[𝓚] (A ∨[𝓚] B)
∨[𝓚]-is-upperbound₂ {𝓤} {X} A B = ∪-is-upperbound₂ ⟨ A ⟩ ⟨ B ⟩

∨[𝓚]-is-lowerbound-of-upperbounds : {X : 𝓤 ̇ } (A B C : 𝓚 X)
                             → A ⊑[𝓚] C → B ⊑[𝓚] C → (A ∨[𝓚] B) ⊑[𝓚] C
∨[𝓚]-is-lowerbound-of-upperbounds {𝓤} {X} A B C =
 ∪-is-lowerbound-of-upperbounds ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

⊥[𝓚] : {X : 𝓤 ̇ } → 𝓚 X
⊥[𝓚] {X} = ∅ , κ
 where
  κ : is-Kuratowski-finite (𝕋 ∅)
  κ = ∣ 0 , unique-from-𝟘 , (λ (y : 𝕋 ∅) → unique-from-𝟘 (pr₂ y)) ∣

⊥[𝓚]-is-least : {X : 𝓤 ̇ } (A : 𝓚 X) → ⊥[𝓚] ⊑[𝓚] A
⊥[𝓚]-is-least {𝓤} {X} A = ∅-is-least ⟨ A ⟩

record JoinSemiLattice (𝓥 𝓣 : Universe) : 𝓤ω where
  constructor
    joinsemilattice
  field
    L : 𝓥 ̇
    L-is-set : is-set L
    _⊑_ : L → L → 𝓣 ̇
    ⊑-is-prop-valued : (x y : L) → is-prop (x ⊑ y)
    ⊑-is-reflexive : (x : L) → x ⊑ x
    ⊑-is-transitive : (x y z : L) → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-is-antisymmetric : (x y : L) → x ⊑ y → y ⊑ x → x ≡ y
    ⊥ : L
    _∨_ : L → L → L
    ⊥-is-least : (x : L) → ⊥ ⊑ x
    ∨-is-upperbound₁ : (x y : L) → x ⊑ (x ∨ y)
    ∨-is-upperbound₂ : (x y : L) → y ⊑ (x ∨ y)
    ∨-is-lowerbound-of-upperbounds : (x y z : L) → x ⊑ z → y ⊑ z → (x ∨ y) ⊑ z

module _
        (pe : propext 𝓤)
        (fe₁ : funext 𝓤 𝓤)
        (fe₂ : funext 𝓤 (𝓤 ⁺))
       where

 𝓚-join-semilattice : (X : 𝓤 ̇ ) → JoinSemiLattice (𝓤 ⁺) 𝓤
 𝓚-join-semilattice X = joinsemilattice
                          (𝓚 X)
                          (𝓚-is-set fe₁ pe fe₂)
                          _⊑[𝓚]_
                          (⊑[𝓚]-is-prop fe₁)
                          ⊑[𝓚]-is-reflexive
                          ⊑[𝓚]-is-transitive
                          (⊑[𝓚]-is-antisymmetric fe₁ pe fe₂)
                          ⊥[𝓚]
                          _∨[𝓚]_
                          ⊥[𝓚]-is-least
                          ∨[𝓚]-is-upperbound₁
                          ∨[𝓚]-is-upperbound₂
                          ∨[𝓚]-is-lowerbound-of-upperbounds

module _
        (𝓛 : JoinSemiLattice 𝓥 𝓣)
       where

 open JoinSemiLattice 𝓛

 transitivity' : (x : L) {y z : L}
               → x ⊑ y → y ⊑ z → x ⊑ z
 transitivity' x {y} {z} = ⊑-is-transitive x y z

 syntax transitivity' x u v = x ⊑⟨ u ⟩ v
 infixr 0 transitivity'

 reflexivity' : (x : L) → x ⊑ x
 reflexivity' x = ⊑-is-reflexive x

 syntax reflexivity' x = x ⊑∎
 infix 1 reflexivity'

 ≡-to-⊑ : {x y : L} → x ≡ y → x ⊑ y
 ≡-to-⊑ {x} {x} refl = reflexivity' x

 ∨ⁿ : {n : ℕ} → (Fin n → L) → L
 ∨ⁿ {zero}   e = ⊥
 ∨ⁿ {succ m} e = (∨ⁿ (e ∘ inl)) ∨ (e (inr *))
 {-
  where
   e' : Fin m → L
   e' = e ∘ inl
   x : L
   x = e (inr *)
   IH : L
   IH = ∨ⁿ e'
 -}

 ∨ⁿ-is-upperbound : {n : ℕ} (σ : Fin n → L)
                  → (k : Fin n) → σ k ⊑ ∨ⁿ σ
 ∨ⁿ-is-upperbound {succ n} σ (inl k) = σ (inl k)    ⊑⟨ IH ⟩
                                       ∨ⁿ (σ ∘ inl) ⊑⟨ ∨-is-upperbound₁ _ _ ⟩
                                       ∨ⁿ σ         ⊑∎
  where
   IH = ∨ⁿ-is-upperbound (σ ∘ inl) k
 ∨ⁿ-is-upperbound {succ n} σ (inr *) = ∨-is-upperbound₂ _ _

 ∨ⁿ-is-lowerbound-of-upperbounds : {n : ℕ} (σ : Fin n → L)
                                   (x : L)
                                 → ((k : Fin n) → σ k ⊑ x)
                                 → ∨ⁿ σ ⊑ x
 ∨ⁿ-is-lowerbound-of-upperbounds {zero}   σ x ub = ⊥-is-least x
 ∨ⁿ-is-lowerbound-of-upperbounds {succ n} σ x ub =
  ∨-is-lowerbound-of-upperbounds _ _ _ u v
   where
    u : ∨ⁿ (σ ∘ inl) ⊑ x
    u = ∨ⁿ-is-lowerbound-of-upperbounds {n} (σ ∘ inl) x (λ k → ub (inl k))
    v : σ (inr *) ⊑ x
    v = ub (inr *)

 module _
         (X : 𝓤 ̇ )
         (X-is-set : is-set X)
         (f : X → L)
        where

  g' : (A : 𝓟 X)
     → (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
     → L
  g' A (n , e , x) = ∨ⁿ (f ∘ pr₁ ∘ e)

  g'-is-wconstant : (A : 𝓟 X) → wconstant (g' A)
  g'-is-wconstant A (n , e , σ) (n' , e' , σ') = ⊑-is-antisymmetric _ _ u v
   where
    u : ∨ⁿ (f ∘ pr₁ ∘ e) ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
    u = ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ pr₁ ∘ e) (∨ⁿ (f ∘ pr₁ ∘ e')) γ
     where
      γ : (k : Fin n) → f (pr₁ (e k)) ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
      γ k = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ' (e k))
       where
        ϕ : (Σ k' ꞉ Fin n' , e' k' ≡ e k) → f (pr₁ (e k)) ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
        ϕ (k' , p) = (f ∘ pr₁) (e k)   ⊑⟨ ≡-to-⊑ (ap (f ∘ pr₁) (p ⁻¹)) ⟩
                     (f ∘ pr₁) (e' k') ⊑⟨ ∨ⁿ-is-upperbound (f ∘ pr₁ ∘ e') k' ⟩
                     ∨ⁿ (f ∘ pr₁ ∘ e') ⊑∎
    v : ∨ⁿ (f ∘ pr₁ ∘ e') ⊑ ∨ⁿ (f ∘ pr₁ ∘ e)
    v = ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ pr₁ ∘ e') (∨ⁿ (f ∘ pr₁ ∘ e)) γ
     where
      γ : (k' : Fin n') → f (pr₁ (e' k')) ⊑ ∨ⁿ (λ x → f (pr₁ (e x)))
      γ k' = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ (e' k'))
       where
        ϕ : (Σ k ꞉ Fin n , e k ≡ e' k') → f (pr₁ (e' k')) ⊑ ∨ⁿ (λ x → f (pr₁ (e x)))
        ϕ (k , p) = (f ∘ pr₁) (e' k') ⊑⟨ ≡-to-⊑ (ap (f ∘ pr₁) (p ⁻¹)) ⟩
                    (f ∘ pr₁) (e k)   ⊑⟨ ∨ⁿ-is-upperbound (f ∘ pr₁ ∘ e) k ⟩
                    ∨ⁿ (f ∘ pr₁ ∘ e)  ⊑∎

  g : 𝓚 X → L
  g (A , κ) =
   wconstant-map-to-set-truncation-of-domain-map _ L-is-set
    (g' A) (g'-is-wconstant A) κ

  g-in-terms-of-g' : (A : 𝓟 X) {n : ℕ} {e : (Fin n → 𝕋 A)} (σ : is-surjection e)
                     (κ : is-Kuratowski-finite (𝕋 A))
                   → g (A , κ) ≡ g' A (n , e , σ)
  g-in-terms-of-g' A {n} {e} σ κ = g (A , κ)             ≡⟨ I  ⟩
                                   g (A , ∣ n , e , σ ∣) ≡⟨ II ⟩
                                   g' A (n , e , σ)      ∎
   where
    I  = ap (λ - → g (A , -)) (∥∥-is-prop κ ∣ n , e , σ ∣)
    II = (wconstant-map-to-set-factors-through-truncation-of-domain
          (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e) L-is-set
          (g' A) (g'-is-wconstant A) (n , e , σ)) ⁻¹

  g-after-η-is-f : g ∘ (η X-is-set) ∼ f
  g-after-η-is-f x = g (η X-is-set x) ≡⟨ I  ⟩
                     g' A (1 , e , σ) ≡⟨ II ⟩
                     f x ∎
   where
    A : 𝓟 X
    A = η' X-is-set x
    e : Fin 1 → 𝕋 A
    e (inr *) = x , refl
    σ : is-surjection e
    σ (x , refl) = ∣ inr * , refl ∣
    I = g-in-terms-of-g' A σ (pr₂ (η X-is-set x))
    II = ⊑-is-antisymmetric _ _
          (∨-is-lowerbound-of-upperbounds _ _ _
           (⊥-is-least (f x)) (⊑-is-reflexive (f x)))
          (∨-is-upperbound₂ _ _) -- ∨-is-upperbound₂

  g-is-monotone : (A B : 𝓚 X)
                → ((x : X) → x ∈ ⟨ A ⟩ → x ∈ ⟨ B ⟩)
                → g A ⊑ g B
  g-is-monotone (A , κ₁) (B , κ₂) s = ∥∥-rec (⊑-is-prop-valued _ _) γ₁ κ₁
   where
    γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
      → g (A , κ₁) ⊑ g (B , κ₂)
    γ₁ (n , e , σ) = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ κ₂
     where
      γ₂ : (Σ n' ꞉ ℕ , Σ e' ꞉ (Fin n' → 𝕋 B) , is-surjection e')
        → g (A , κ₁) ⊑ g (B , κ₂)
      γ₂ (n' , e' , σ') = g (A , κ₁)        ⊑⟨ u₁ ⟩
                          ∨ⁿ (f ∘ pr₁ ∘ e)  ⊑⟨ u₂ ⟩
                          ∨ⁿ (f ∘ pr₁ ∘ e') ⊑⟨ u₃ ⟩
                          g (B , κ₂)        ⊑∎
       where
        u₁ = ≡-to-⊑ (g-in-terms-of-g' A σ κ₁)
        u₃ = ≡-to-⊑ ((g-in-terms-of-g' B σ' κ₂) ⁻¹)
        u₂ = ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ pr₁ ∘ e) (∨ⁿ (f ∘ pr₁ ∘ e')) γ₃
         where
          γ₃ : (k : Fin n) → (f ∘ pr₁ ∘ e) k ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
          γ₃ k = ∥∥-rec (⊑-is-prop-valued _ _) γ₄ t
           where
            x : X
            x = pr₁ (e k)
            a : x ∈ A
            a = pr₂ (e k)
            b : x ∈ B
            b = s x a
            t : ∃ k' ꞉ Fin n' , e' k' ≡ (x , b)
            t = σ' (x , b)
            γ₄ : (Σ k' ꞉ Fin n' , e' k' ≡ (x , b))
               → (f ∘ pr₁ ∘ e) k ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
            γ₄ (k' , p) = (f ∘ pr₁) (e k)   ⊑⟨ v₁ ⟩
                          (f ∘ pr₁) (e' k') ⊑⟨ v₂ ⟩
                          ∨ⁿ (f ∘ pr₁ ∘ e') ⊑∎
             where
              v₁ = ≡-to-⊑ (ap f q)
               where
                q : pr₁ (e k) ≡ pr₁ (e' k')
                q = ap pr₁ (p ⁻¹)
              v₂ = ∨ⁿ-is-upperbound (f ∘ pr₁ ∘ e') k'


  -- TO DO: Clean this a bit
  g-preserves-∨ : (A B : 𝓚 X) → g (A ∨[𝓚] B) ≡ g A ∨ g B
  g-preserves-∨ A B = ⊑-is-antisymmetric _ _ u v
   where
    u : g (A ∨[𝓚] B) ⊑ (g A ∨ g B)
    u = ∥∥-rec (⊑-is-prop-valued (g (A ∨[𝓚] B)) (g A ∨ g B))
        γ₁ (⟨ A ⟩₂)
     where
      γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 ⟨ A ⟩) , is-surjection e)
         → g (A ∨[𝓚] B) ⊑ (g A ∨ g B)
      γ₁ (n , e , σ) = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ (⟨ B ⟩₂)
       where
        γ₂ : (Σ n' ꞉ ℕ , Σ e' ꞉ (Fin n' → 𝕋 ⟨ B ⟩) , is-surjection e')
           → g (A ∨[𝓚] B) ⊑ (g A ∨ g B)
        γ₂ (n' , e' , σ') = g (A ∨[𝓚] B) ⊑⟨ ≡-to-⊑ kkk ⟩
                            ∨ⁿ (f ∘ pr₁ ∘ [e,e']) ⊑⟨ ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ pr₁ ∘ [e,e']) (g A ∨ g B) γ ⟩
                            (g A ∨ g B) ⊑∎
         where
          [e,e'] : Fin (n +' n') → 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩)
          [e,e'] = (∪-enum ⟨ A ⟩ ⟨ B ⟩ e e')
          τ : is-surjection [e,e']
          τ = ∪-enum-is-surjection ⟨ A ⟩ ⟨ B ⟩ e e' σ σ'
          kkk : g (A ∨[𝓚] B) ≡ g' (⟨ A ⟩ ∪ ⟨ B ⟩) (n +' n' , [e,e'] , τ)
          kkk = g-in-terms-of-g' (⟨ A ⟩ ∪ ⟨ B ⟩) τ ⟨ A ∨[𝓚] B ⟩₂
          γ : (k : Fin (n +' n'))
            → (f ∘ pr₁ ∘ [e,e']) k ⊑ (g A ∨ g B)
          γ k = (f ∘ pr₁ ∘ [e,e']) k                   ⊑⟨ ⊑-is-reflexive _ ⟩
                (f ∘ pr₁ ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑⟨ γ' c ⟩
                (g A ∨ g B)                            ⊑∎
           where
            c : Fin n + Fin n'
            c = ⌜ Fin+homo n n' ⌝ k
            γ' : (c : Fin n + Fin n')
               → (f ∘ pr₁ ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑ (g A ∨ g B)
            γ' (inl k) = (f ∘ pr₁ ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inl k) ⊑⟨ ⊑-is-reflexive ((f ∘ pr₁ ∘ e) k) ⟩
                         (f ∘ pr₁ ∘ e) k                              ⊑⟨ ∨ⁿ-is-upperbound (f ∘ pr₁ ∘ e) k ⟩
                         ∨ⁿ (f ∘ pr₁ ∘ e)                             ⊑⟨ ⊑-is-reflexive (∨ⁿ (f ∘ pr₁ ∘ e)) ⟩
                         g' ⟨ A ⟩ (n , e , σ)                         ⊑⟨ ≡-to-⊑ ((g-in-terms-of-g' ⟨ A ⟩ σ ⟨ A ⟩₂) ⁻¹) ⟩
                         g A                                          ⊑⟨ ∨-is-upperbound₁ (g A) (g B) ⟩
                         g A ∨ g B                                    ⊑∎
            γ' (inr k) = (f ∘ pr₁ ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inr k) ⊑⟨ ⊑-is-reflexive ((f ∘ pr₁ ∘ e') k) ⟩
                         (f ∘ pr₁ ∘ e') k                             ⊑⟨ ∨ⁿ-is-upperbound (f ∘ pr₁ ∘ e') k ⟩
                         ∨ⁿ (f ∘ pr₁ ∘ e')                            ⊑⟨ ⊑-is-reflexive (∨ⁿ (f ∘ pr₁ ∘ e')) ⟩
                         g' ⟨ B ⟩ (n' , e' , σ')                      ⊑⟨ ≡-to-⊑ ((g-in-terms-of-g' ⟨ B ⟩ σ' ⟨ B ⟩₂) ⁻¹) ⟩
                         g B                                          ⊑⟨ ∨-is-upperbound₂ (g A) (g B) ⟩
                         g A ∨ g B                                    ⊑∎
    v : (g A ∨ g B) ⊑ g (A ∨[𝓚] B)
    v = ∨-is-lowerbound-of-upperbounds _ _ _
        (g-is-monotone A (A ∨[𝓚] B) (∨[𝓚]-is-upperbound₁ A B))
        (g-is-monotone B (A ∨[𝓚] B) (∨[𝓚]-is-upperbound₂ A B))

{-

module _
        (L : 𝓥 ̇ )

       where

-}
\end{code}
