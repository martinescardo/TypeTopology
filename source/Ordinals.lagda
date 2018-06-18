Martin Escardo, April 2013, adapted to this development June 2018

Ordinals like in the HoTT book and variations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (_≤_)
open import UF-Subsingletons
open import UF-FunExt

module Ordinals {U V : Universe} {X : U ̇} (_<_ : X → X → V ̇) where

data is-accessible : X → U ⊔ V ̇ where
 next : (x : X) → ((y : X) → y < x → is-accessible y) → is-accessible x

accessible-induction : ∀ {W} (P : (x : X) → is-accessible x → W ̇)
                    → ((x : X) (σ : (y : X) → y < x → is-accessible y)
                        → ((y : X) (l : y < x) → P y (σ y l))
                        → P x (next x σ))
                    → (x : X) (a : is-accessible x) → P x a
accessible-induction P step = h
  where
   h : (x : X) (a : is-accessible x) → P x a
   h x (next .x σ) = step x σ (λ y l → h y (σ y l))

prev : (x : X) → is-accessible x → (y : X) → y < x → is-accessible y
prev = accessible-induction (λ x _ → (y : X) → y < x → is-accessible y)
                            (λ x σ f y l → σ y l)

prev-behaviour : (x : X) → ∀(a : is-accessible x) → next x (prev x a) ≡ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

transfinite-induction' :  ∀ {W} (P : X → W ̇) → 
                 ((x : X) → (∀(y : X) → y < x → P y) → P x) →
                 (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction (λ x _ → P x)
                                                  (λ x _ → f x) 

well-founded : U ⊔ V ̇
well-founded = (x : X) → is-accessible x

Well-founded : ∀ {W} → U ⊔ V ⊔ W ′ ̇
Well-founded {W} = (P : X → W ̇) → ((x : X) → ((y : X) → y < x → P y) → P x) → (x : X) → P x

transfinite-induction : well-founded → ∀ {W} → Well-founded {W}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : Well-founded {U ⊔ V} → well-founded
transfinite-induction-converse F = F is-accessible next

transfinite-recursion : well-founded → ∀ {W} {Y : W ̇}
                     → ((x : X) → ((y : X) → y < x → Y) → Y) → X → Y
transfinite-recursion w {W} {Y} = transfinite-induction w (λ x → Y)

transitive : U ⊔ V ̇
transitive = {x y z : X} → x < y → y < z → x < z

extensional : U ⊔ V ̇
extensional = {x y : X} → ((z : X) → (z < x) ⇔ (z < y)) → x ≡ y 

ordinal : U ⊔ V ̇
ordinal = well-founded × extensional × transitive

is-accessible-is-prop : funext U (U ⊔ V) → funext V (U ⊔ V)
                      → (x : X) → is-prop(is-accessible x)
is-accessible-is-prop fe fe' = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → U ⊔ V ̇
  P x a = (b : is-accessible x) → a ≡ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y) →
      ((y : X) (l : y < x) (a : is-accessible y) → σ y l ≡ a) →
      (b : is-accessible x) → next x σ ≡ b
  φ x σ IH b = next x σ ≡⟨ ap (λ f → next x f) (dfunext fe (λ y → dfunext fe' (h y))) ⟩
               next x τ ≡⟨ prev-behaviour x b ⟩
               b ∎
   where
    τ : (y : X) (l : y < x) → is-accessible y
    τ = prev x b
    h :  (y : X) (l : y < x) → σ y l ≡ τ y l
    h y l = IH y l (τ y l)

_≤_ : X → X → V ̇
x ≤ y = ¬(y < x)

antisym : (x : X) → is-accessible x → ∀ y → y < x → y ≤ x
antisym = transfinite-induction' (λ x → (y : X) → y < x → y ≤ x)
                                 (λ x f y l m → f y l x m l) 

irrefl : (x : X) → is-accessible x → x ≤ x
irrefl x a l = antisym x a x l l

notricycle : (x : X) → is-accessible x
           → (y z : X) → y < x → z < y → z ≤ x
notricycle = transfinite-induction' (λ x → (y z : X) → y < x → z < y → z ≤ x)
                                    (λ x f y z l m n → f y l z x m n l) 

\end{code}
