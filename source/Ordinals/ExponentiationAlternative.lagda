Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 April 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.ExponentiationAlternative
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
open import UF.Equiv
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua


open import Naturals.Order

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Sigma
open import MLTT.List

open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderingTaboo
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open import Ordinals.Exponentiation ua pt sr

open PropositionalTruncation pt

open suprema pt sr
\end{code}


We define `exp α β = sup_{1 + ⟨ β ⟩} (inl _ ↦ 𝟙ₒ; inr b ↦ exp α (β ↓ b) ×ₒ α)
by transfinite recursion on β.

\begin{code}

exp : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → Ordinal (𝓤 ⊔ 𝓥)
exp {𝓤} {𝓥} α = transfinite-recursion-on-OO
                  (Ordinal (𝓤 ⊔ 𝓥))
                  (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩}
                                  (cases
                                    (λ _ → 𝟙ₒ)
                                    (λ b → ih b ×ₒ α))) -- exp α (β ↓ b) ×ₒ α

exp-behaviour : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) →
                exp α β ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α))
exp-behaviour {𝓤} {𝓥} α β = {!transfinite-recursion-on-OO-behaviour (Ordinal (𝓤 ⊔ 𝓥)) ((λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → ih b ×ₒ α)))exp-body α) β!}

\end{code}

\begin{code}

sup-composition : {B : 𝓤 ̇ }{C : 𝓤 ̇ } → (f : B → C) → (F : C → Ordinal 𝓤) → sup (F ∘ f) ⊴ sup F
sup-composition f F = sup-is-lower-bound-of-upper-bounds (F ∘ f) (sup F) (λ i → sup-is-upper-bound F (f i))

exp-monotone-in-exponent : (α : Ordinal 𝓤) → (β γ : Ordinal 𝓥)
                         → β ⊴ γ → exp α β ⊴ exp α γ
exp-monotone-in-exponent α β γ p = transport₂⁻¹ _⊴_ (exp-behaviour α β) (exp-behaviour α γ) (transport (λ - → sup -  ⊴ sup F) claim' (sup-composition f F))
  where
    F : 𝟙 {𝓤} + ⟨ γ ⟩ → Ordinal _
    F  = cases (λ _ → 𝟙ₒ) (λ c → exp α (γ ↓ c) ×ₒ α)

    f : 𝟙 {𝓤} + ⟨ β ⟩ → 𝟙 {𝓤} + ⟨ γ ⟩
    f (inl x) = inl x
    f (inr b) = inr (pr₁ p b)

    F' : 𝟙 {𝓤} + ⟨ β ⟩ → Ordinal _
    F' = cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α)

    initial-segments-agree : (b : ⟨ β ⟩) → β ↓ b ＝ γ ↓ (pr₁ p b)
    initial-segments-agree b = pr₂ (from-≼ (⊴-gives-≼ β γ p) b)

    claim : (i : 𝟙 {𝓤} + ⟨ β ⟩) → F (f i) ＝ F' i
    claim (inl x) = refl
    claim (inr b) = ap (λ - → exp α - ×ₒ α) (initial-segments-agree b ⁻¹)

    claim' : F ∘ f ＝ F'
    claim' = dfunext fe' claim

exp-has-least-element : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → 𝟙ₒ {𝓤 ⊔ 𝓥} ⊴ exp α β
exp-has-least-element {𝓤} α β = transport⁻¹ (𝟙ₒ ⊴_) (exp-behaviour α β) q
  where
    q : 𝟙ₒ ⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α))
    q = sup-is-upper-bound (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α)) (inl ⋆)

exp-satisfies-zero-specification : (α : Ordinal 𝓤) → exp α (𝟘ₒ {𝓥}) ＝ 𝟙ₒ
exp-satisfies-zero-specification α = ⊴-antisym (exp α 𝟘ₒ) 𝟙ₒ II III
  where
    I : (i : 𝟙 + 𝟘) → cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟘ₒ ↓ b) ×ₒ α) i ⊴ 𝟙ₒ
    I (inl _) = ⊴-refl 𝟙ₒ

    II : exp α 𝟘ₒ ⊴ 𝟙ₒ
    II = transport⁻¹ (_⊴ 𝟙ₒ) (exp-behaviour α 𝟘ₒ) (sup-is-lower-bound-of-upper-bounds (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟘ₒ ↓ b) ×ₒ α)) 𝟙ₒ I)

    III : 𝟙ₒ ⊴ exp α 𝟘ₒ
    III = exp-has-least-element α 𝟘ₒ

exp-power-one-is-identity : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp α (𝟙ₒ {𝓤}) ＝ α
exp-power-one-is-identity α p = transport⁻¹ (λ - → - ＝ α) (exp-behaviour α 𝟙ₒ)
                                            (⊴-antisym _ _ f g)
 where
  I : (𝟙ₒ ↓ ⋆) ⊴ 𝟘ₒ
  I = (λ x → 𝟘-elim (pr₂ x)) , (λ x → 𝟘-elim (pr₂ x)) , (λ x → 𝟘-elim (pr₂ x))

  II : (𝟙ₒ ↓ ⋆) ＝ 𝟘ₒ
  II = ⊴-antisym _ _ I (𝟘ₒ-least-⊴ (𝟙ₒ ↓ ⋆))

  III : exp α (𝟙ₒ ↓ ⋆) ＝ 𝟙ₒ
  III = transport⁻¹ (λ - → exp α - ＝ 𝟙ₒ) II (exp-satisfies-zero-specification α)

  IV : exp α (𝟙ₒ ↓ ⋆) ×ₒ α ＝ α
  IV = (ap (_×ₒ α) III ∙ 𝟙ₒ-left-neutral-×ₒ α)

  f : sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α)) ⊴ α
  f = (sup-is-lower-bound-of-upper-bounds (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α)) α k)
    where
     k : (i : 𝟙 + 𝟙) → cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α) i ⊴ α
     k (inl _) = p
     k (inr b) = transport⁻¹ (_⊴ α) IV (⊴-refl α)

  g : α ⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α))
  g = transport (_⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α)))
                IV
                (sup-is-upper-bound (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟙ₒ ↓ b) ×ₒ α)) (inr ⋆))


exp-power-two : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp α (𝟙ₒ +ₒ 𝟙ₒ {𝓤}) ＝ α ×ₒ α
exp-power-two {𝓤} α p = transport⁻¹ (λ - → - ＝ α ×ₒ α) (exp-behaviour α (𝟙ₒ +ₒ 𝟙ₒ) ∙ ap sup eq')
                                (⊴-antisym _ _ (sup-is-lower-bound-of-upper-bounds F (α ×ₒ α) F-upper-bound) (sup-is-upper-bound F (inr (inr ⋆))))
  where
   F : 𝟙 + (𝟙 + 𝟙) → Ordinal 𝓤
   F (inl _) = 𝟙ₒ
   F (inr (inl _)) = α
   F (inr (inr _)) = α ×ₒ α

   p₂ : α ⊴ (α ×ₒ α)
   p₂ = transport (_⊴ (α ×ₒ α)) (𝟙ₒ-right-neutral-×ₒ α) (×ₒ-right-monotone-⊴ α 𝟙ₒ α p)

   F-upper-bound : (i : 𝟙 + (𝟙 + 𝟙)) →  F i ⊴ (α ×ₒ α)
   F-upper-bound (inl _) = ⊴-trans _ _ _ p p₂
   F-upper-bound (inr (inl _)) = p₂
   F-upper-bound (inr (inr _)) = ⊴-refl (α ×ₒ α)

   eq : (i : 𝟙 + (𝟙 + 𝟙)) → (cases (λ _ → 𝟙ₒ) (λ b → exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) i ＝ F i
   eq (inl _) = refl
   eq (inr (inl x)) = IV
    where
      I : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ⊴ 𝟘ₒ
      I = (λ { (inl x , p) → p ; (inr x , p) → p}) , (λ x y → 𝟘-elim y) , λ { (inl x , p) → 𝟘-elim p ; (inr x , p) → 𝟘-elim p }

      II : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ＝ 𝟘ₒ
      II = ⊴-antisym _ _ I (𝟘ₒ-least-⊴ ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆))

      III : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ＝ 𝟙ₒ
      III = transport⁻¹ (λ - → exp α - ＝ 𝟙ₒ) II (exp-satisfies-zero-specification α)

      IV : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ×ₒ α ＝ α
      IV = (ap (_×ₒ α) III ∙ 𝟙ₒ-left-neutral-×ₒ α)
   eq (inr (inr x)) = III
     where
      I : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ＝ 𝟙ₒ
      I = +ₒ-𝟙ₒ-↓-right 𝟙ₒ

      II : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ＝ α
      II = ap (exp α) I ∙ exp-power-one-is-identity α p

      III : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ×ₒ α ＝ α ×ₒ α
      III = ap (_×ₒ α) II

   eq' : (cases (λ _ → 𝟙ₒ) (λ b → exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ＝ F
   eq' = dfunext fe' eq

finite-ord : ℕ → Ordinal 𝓤
finite-ord zero = 𝟘ₒ
finite-ord (succ n) = finite-ord n +ₒ 𝟙ₒ

finite-ord⁻¹ : {n : ℕ} → ⟨ finite-ord {𝓤 = 𝓤} n ⟩ → ℕ
finite-ord⁻¹ {n = succ n} (inl x) = finite-ord⁻¹ {n = n} x
finite-ord⁻¹ {n = succ n} (inr x) = n

finite-ord⁻¹-bound : {n : ℕ} → (k : ⟨ finite-ord {𝓤 = 𝓤} n ⟩) → finite-ord⁻¹ k <ℕ n
finite-ord⁻¹-bound {n = succ n} (inl k) = ≤-trans (finite-ord⁻¹ k) (succ (finite-ord⁻¹ k)) n (≤-succ (finite-ord⁻¹ k)) (finite-ord⁻¹-bound {n = n} k)
finite-ord⁻¹-bound {n = succ n} (inr _) = <-succ n

finite-ord-↓ : {n : ℕ} → (k : ⟨ finite-ord {𝓤} n ⟩) →  finite-ord n ↓ k ＝ finite-ord (finite-ord⁻¹ k)
finite-ord-↓ {n = succ n} (inl k) = +ₒ-↓-left k ⁻¹ ∙ finite-ord-↓ {n = n} k
finite-ord-↓ {n = succ n} (inr x) = +ₒ-𝟙ₒ-↓-right (finite-ord n)

finite-exp : Ordinal 𝓤 → ℕ → Ordinal 𝓤
finite-exp α zero = 𝟙ₒ
finite-exp α (succ n) = finite-exp α n ×ₒ α

finite-exp-swap : (α : Ordinal 𝓤) → (n : ℕ) → finite-exp α (succ n) ＝ α ×ₒ finite-exp α n
finite-exp-swap α zero = (𝟙ₒ ×ₒ α) ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩ α ＝⟨ 𝟙ₒ-right-neutral-×ₒ α ⁻¹ ⟩ (α ×ₒ 𝟙ₒ) ∎
finite-exp-swap α (succ n) =
  ((finite-exp α n ×ₒ α) ×ₒ α) ＝⟨ ap (_×ₒ α) (finite-exp-swap α n) ⟩
  ((α ×ₒ finite-exp α n) ×ₒ α) ＝⟨ ×ₒ-assoc α (finite-exp α n) α ⟩
  ( α ×ₒ (finite-exp α n ×ₒ α)) ∎

finite-exp-least-element : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → (n : ℕ) → 𝟙ₒ {𝓤} ⊴ finite-exp α n
finite-exp-least-element α p zero = ⊴-refl 𝟙ₒ
finite-exp-least-element α p (succ n) = ⊴-trans _ _ _ p
                                                      (transport₂ _⊴_
                                                                  (𝟙ₒ-right-neutral-×ₒ α)
                                                                  (finite-exp-swap α n ⁻¹)
                                                                  (×ₒ-right-monotone-⊴ α _ _ (finite-exp-least-element α p n)))


finite-exp-monotone : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → (n : ℕ) → (k : ⟨ finite-ord {𝓤 = 𝓤} n ⟩) → finite-exp α (finite-ord⁻¹ k) ⊴ finite-exp α n
finite-exp-monotone α p (succ n) (inl x) = ⊴-trans _ _ _ (finite-exp-monotone α p n x) (transport (_⊴ (finite-exp α n ×ₒ α)) (𝟙ₒ-right-neutral-×ₒ _) (×ₒ-right-monotone-⊴ (finite-exp α n) _ _ p))
finite-exp-monotone α p (succ n) (inr x) = transport (_⊴ (finite-exp α n ×ₒ α)) (𝟙ₒ-right-neutral-×ₒ _) (×ₒ-right-monotone-⊴ (finite-exp α n) _ _ p)

finite-exp-finite-ord⁻¹-swap : (α : Ordinal 𝓤) → (n : ℕ) → (k : ⟨ finite-ord {𝓤 = 𝓤} n ⟩) → finite-exp α (finite-ord⁻¹ {n = n} k) ×ₒ α ＝ (α ×ₒ finite-exp α (finite-ord⁻¹ {n = n} k))
finite-exp-finite-ord⁻¹-swap α (succ n) (inl x) = finite-exp-finite-ord⁻¹-swap α n x
finite-exp-finite-ord⁻¹-swap α (succ n) (inr x) = finite-exp-swap α n


exp-satisfies-succ-specification-for-finite-powers : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                                   → (n : ℕ) → exp α (finite-ord {𝓤} n) ＝ finite-exp α n
exp-satisfies-succ-specification-for-finite-powers {𝓤} α p = course-of-values-induction (λ n → exp α (finite-ord {𝓤} n) ＝ finite-exp α n) step
 where
  step : (n : ℕ) → (((m : ℕ) → m <ℕ n → exp α (finite-ord {𝓤} m) ＝ finite-exp α m)) → exp α (finite-ord {𝓤} n) ＝ finite-exp α n
  step zero ih = exp-satisfies-zero-specification α
  step (succ n) ih = transport⁻¹ (λ - → - ＝ finite-exp α n ×ₒ α) (exp-behaviour α (finite-ord n +ₒ 𝟙ₒ) ∙ ap sup eq')
                                 (⊴-antisym _ _ (sup-is-lower-bound-of-upper-bounds F _ upper-bound) (sup-is-upper-bound F (inr (inr ⋆))))
   where
    F : 𝟙 + (⟨ finite-ord n ⟩ + 𝟙) → Ordinal 𝓤
    F (inl _) = 𝟙ₒ
    F (inr (inl k)) = finite-exp α (finite-ord⁻¹ k) ×ₒ α
    F (inr (inr _)) = finite-exp α n ×ₒ α

    upper-bound : (i : 𝟙 + (⟨ finite-ord n ⟩ + 𝟙)) → F i ⊴ (finite-exp α n ×ₒ α)
    upper-bound (inl _) = finite-exp-least-element {𝓤} α p (succ n)
    upper-bound (inr (inl k)) = transport₂⁻¹ _⊴_ (finite-exp-finite-ord⁻¹-swap α n k)
                                                 (finite-exp-swap α n)
                                                 (×ₒ-right-monotone-⊴ α _ _ (finite-exp-monotone α p n k))
    upper-bound (inr (inr _)) = ⊴-refl (finite-exp α n ×ₒ α)

    eq : (i : 𝟙 + (⟨ finite-ord n ⟩ + 𝟙)) → (cases (λ _ → 𝟙ₒ) (λ b → exp α ((finite-ord n +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) i ＝ F i
    eq (inl _) = refl
    eq (inr (inl k)) = ap (_×ₒ α) III
     where
      I : (finite-ord n +ₒ 𝟙ₒ) ↓ inl k ＝ finite-ord (finite-ord⁻¹ k)
      I = +ₒ-↓-left k ⁻¹ ∙ finite-ord-↓ k

      III : exp α ((finite-ord n +ₒ 𝟙ₒ) ↓ inl k) ＝ finite-exp α (finite-ord⁻¹ k)
      III = ap (exp α) I ∙ ih (finite-ord⁻¹ k) (finite-ord⁻¹-bound {n = succ n} (inl k))
    eq (inr (inr _)) = ap (λ z → exp α z ×ₒ α) (+ₒ-𝟙ₒ-↓-right (finite-ord n)) ∙ ap (_×ₒ α) (ih n (<-succ n))

    eq' : (cases (λ _ → 𝟙ₒ) (λ b → exp α ((finite-ord n +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ＝ F
    eq' = dfunext fe' eq



{-

   F-upper-bound : (i : 𝟙 + (𝟙 + 𝟙)) →  F i ⊴ (α ×ₒ α)
   F-upper-bound (inl _) = ⊴-trans _ _ _ p p₂
   F-upper-bound (inr (inl _)) = p₂
   F-upper-bound (inr (inr _)) = ⊴-refl (α ×ₒ α)

   eq : (i : 𝟙 + (𝟙 + 𝟙)) → (cases (λ _ → 𝟙ₒ) (λ b → exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) i ＝ F i
   eq (inl _) = refl
   eq (inr (inl x)) = IV
    where
      I : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ⊴ 𝟘ₒ
      I = (λ { (inl x , p) → p ; (inr x , p) → p}) , (λ x y → 𝟘-elim y) , λ { (inl x , p) → 𝟘-elim p ; (inr x , p) → 𝟘-elim p }

      II : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ＝ 𝟘ₒ
      II = ⊴-antisym _ _ I (𝟘ₒ-least-⊴ ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆))

      III : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ＝ 𝟙ₒ
      III = transport⁻¹ (λ - → exp α - ＝ 𝟙ₒ) II (exp-satisfies-zero-specification α)

      IV : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inl ⋆) ×ₒ α ＝ α
      IV = (ap (_×ₒ α) III ∙ 𝟙ₒ-left-neutral-×ₒ α)
   eq (inr (inr x)) = III
     where
      I : ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ＝ 𝟙ₒ
      I = +ₒ-𝟙ₒ-↓-right 𝟙ₒ

      II : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ＝ α
      II = ap (exp α) I ∙ exp-power-one-is-identity α p

      III : exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ inr ⋆) ×ₒ α ＝ α ×ₒ α
      III = ap (_×ₒ α) II

   eq' : (cases (λ _ → 𝟙ₒ) (λ b → exp α ((𝟙ₒ +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ＝ F
   eq' = dfunext fe' eq
-}
{-
exp-satisfies-succ-specification : (α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                 → exp α (β +ₒ 𝟙ₒ) ＝ (exp α β) ×ₒ α
exp-satisfies-succ-specification α β p = transport⁻¹ (λ - → - ＝ (exp α β) ×ₒ α) (exp-behaviour α (β +ₒ 𝟙ₒ))
                                           (surjective-simulation-gives-equality _ (exp α β ×ₒ α) f f-is-simulation f-is-surjective)
 where
  h : sup (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ⊴ ((exp α β) ×ₒ α)
  h = (sup-is-lower-bound-of-upper-bounds (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ((exp α β) ×ₒ α) k)
    where
      k : (i : 𝟙 + pr₁ (β +ₒ 𝟙ₒ)) → cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α) i ⊴ (exp α β ×ₒ α)
      k (inl _) = {!!}
      k (inr (inl b)) = {!!}
      k (inr (inr _)) = {!!}

  f : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ⟩ →  ⟨ (exp α β) ×ₒ α ⟩
  f = pr₁ h

  f-is-simulation : is-simulation _ (exp α β ×ₒ α) f
  f-is-simulation = pr₂ h

  f-is-surjective : is-surjection f
  f-is-surjective = {!!}
-}
{-



(f : α ≤ α') →? α ×ₒ β ≤ α' ×ₒ β

(a , b) ↦ (f a , b)

Assume (a' , b') < (f a  , b). Need to find (a₀ , b₀) s t (f a₀ , b₀) = (a' , b').



Case b' < b: Take a₀ = ???, b₀ = b'.

Case b' = b, a' < f a


-}

\end{code}
