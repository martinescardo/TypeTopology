Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 April 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Supremum
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UniverseEmbedding
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
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderingTaboo
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open import Ordinals.Exponentiation.DecreasingList ua pt sr hiding (exp-+-distributes)
open import Ordinals.Exponentiation.Specification ua pt sr

open PropositionalTruncation pt

open suprema pt sr
\end{code}


We define `α ^ₒ β = sup_{1 + ⟨ β ⟩} (inl _ ↦ 𝟙ₒ; inr b ↦ α ^ₒ (β ↓ b) ×ₒ α)
by transfinite recursion on β.

\begin{code}

exp-bundled :
   (α : Ordinal 𝓤)
 → Σ f ꞉ (Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)) ,
     ((β : Ordinal 𝓥)
       → f β ＝ sup {I = 𝟙 + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → f (β ↓ b) ×ₒ α)))
exp-bundled {𝓤} {𝓥} α =
 transfinite-recursion-on-OO-bundled
  (Ordinal (𝓤 ⊔ 𝓥))
  (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) λ b → ih b ×ₒ α))

abstract
 _^ₒ_ : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → Ordinal (𝓤 ⊔ 𝓥)
 _^ₒ_ α = pr₁ (exp-bundled α)

 infixr 8 _^ₒ_

 ^ₒ-behaviour :
    (α : Ordinal 𝓤) (β : Ordinal 𝓥)
  → α ^ₒ β
    ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ (β ↓ b) ×ₒ α))
 ^ₒ-behaviour α = pr₂ (exp-bundled α)

 module _
  (α : Ordinal 𝓤)
  (β : Ordinal 𝓥)
  where

  ^ₒ-family : 𝟙 {𝓤} + ⟨ β ⟩ → Ordinal (𝓤 ⊔ 𝓥)
  ^ₒ-family = cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ (β ↓ b) ×ₒ α)

  ^ₒ-is-upper-bound : (x : 𝟙 + ⟨ β ⟩) → ^ₒ-family x ⊴ α ^ₒ β
  ^ₒ-is-upper-bound x =
   transport⁻¹
    (^ₒ-family x ⊴_)
    (^ₒ-behaviour α β)
    (sup-is-upper-bound ^ₒ-family x)

  ^ₒ-is-upper-bound₁ : 𝟙ₒ ⊴ α ^ₒ β
  ^ₒ-is-upper-bound₁ = ^ₒ-is-upper-bound (inl ⋆)

  ^ₒ-is-upper-bound₂ : {b : ⟨ β ⟩} → α ^ₒ (β ↓ b) ×ₒ α ⊴ α ^ₒ β
  ^ₒ-is-upper-bound₂ {b} = ^ₒ-is-upper-bound (inr b)

  ^ₒ-is-lower-bound-of-upper-bounds :
     (γ : Ordinal (𝓤 ⊔ 𝓥))
   → 𝟙ₒ ⊴ γ
   → ((b : ⟨ β ⟩) → α ^ₒ (β ↓ b) ×ₒ α ⊴ γ)
   → α ^ₒ β ⊴ γ
  ^ₒ-is-lower-bound-of-upper-bounds γ l₁ l₂ =
   transport⁻¹ (_⊴ γ)
    (^ₒ-behaviour α β)
    (sup-is-lower-bound-of-upper-bounds
      ^ₒ-family γ (dep-cases (λ _ → l₁) l₂))

  ^ₒ-⊥ : ⟨ α ^ₒ β ⟩
  ^ₒ-⊥ = [ 𝟙ₒ , α ^ₒ β ]⟨ ^ₒ-is-upper-bound₁ ⟩ ⋆

  ×ₒ-to-^ₒ : {b : ⟨ β ⟩} → ⟨ α ^ₒ (β ↓ b) ×ₒ α ⟩ → ⟨ α ^ₒ β ⟩
  ×ₒ-to-^ₒ {b} = [ α ^ₒ (β ↓ b) ×ₒ α , α ^ₒ β ]⟨ ^ₒ-is-upper-bound₂ ⟩

  private
   ι : (x : 𝟙 + ⟨ β ⟩) → ⟨ ^ₒ-family x ⟩ → ⟨ α ^ₒ β ⟩
   ι x = [ ^ₒ-family x , α ^ₒ β ]⟨ ^ₒ-is-upper-bound x ⟩

   ι-is-jointly-surjective :
      (e : ⟨ α ^ₒ β ⟩)
     → ∃ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , ι x y ＝ e
   ι-is-jointly-surjective e = ∥∥-functor I II
    where
     σ = λ (x : 𝟙 + ⟨ β ⟩)
           → [ ^ₒ-family x , sup ^ₒ-family ]⟨ sup-is-upper-bound ^ₒ-family x ⟩
     module _
      {γ : Ordinal (𝓤 ⊔ 𝓥)}
      (e : ⟨ γ ⟩)
      where
       III :
          (p : γ ＝ sup ^ₒ-family) {x : 𝟙 + ⟨ β ⟩} {y : ⟨ ^ₒ-family x ⟩}
        → σ x y ＝ Idtofun (ap ⟨_⟩ p) e
        → [ ^ₒ-family x , γ ]⟨
            transport⁻¹ (^ₒ-family x ⊴_) p (sup-is-upper-bound ^ₒ-family x) ⟩ y
          ＝ e
       III refl = id

     p = ^ₒ-behaviour α β
     q = ap ⟨_⟩ p
     e' = Idtofun q e

     I : (Σ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , σ x y ＝ e')
       → (Σ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , ι x y ＝ e)
     I (x , y , eq) = x , y , III e p eq

     II : ∃ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , σ x y ＝ e'
     II = sup-is-upper-bound-jointly-surjective ^ₒ-family (Idtofun q e)

  ^ₒ-induction : {𝓦 : Universe} (P : ⟨ α ^ₒ β ⟩ → 𝓦 ̇  )
               → ((e : ⟨ α ^ₒ β ⟩) → is-prop (P e))
               → P ^ₒ-⊥
               → ((b : ⟨ β ⟩) (y : ⟨ α ^ₒ (β ↓ b) ×ₒ α ⟩) → P (×ₒ-to-^ₒ y))
               → (e : ⟨ α ^ₒ β ⟩) → P e
  ^ₒ-induction P P-is-prop-valued P-⊥ P-component =
   surjection-induction σ σ-is-surjection P P-is-prop-valued ρ
    where
     σ : (Σ x ꞉ 𝟙 + ⟨ β ⟩ , ⟨ ^ₒ-family x ⟩) → ⟨ α ^ₒ β ⟩
     σ (x , y) = ι x y

     σ-is-surjection : is-surjection σ
     σ-is-surjection e =
      ∥∥-functor
       (λ (x , y , p) → (x , y) , p)
       (ι-is-jointly-surjective e)

     ρ : ((x , y) : domain σ) → P (ι x y)
     ρ (inl ⋆ , ⋆) = P-⊥
     ρ (inr b , y) = P-component b y

\end{code}

\begin{code}

^ₒ-has-least-element : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝟙ₒ ⊴ α ^ₒ β
^ₒ-has-least-element = ^ₒ-is-upper-bound₁

^ₒ-is-positive : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝟘ₒ ⊲ α ^ₒ β
^ₒ-is-positive α β =
 ⊲-⊴-gives-⊲ 𝟘ₒ 𝟙ₒ (α ^ₒ β) 𝟘ₒ-⊲-𝟙ₒ (^ₒ-has-least-element α β)

^ₒ-monotone-in-exponent : (α : Ordinal 𝓤) → (β γ : Ordinal 𝓥)
                        → β ⊴ γ → α ^ₒ β ⊴ α ^ₒ γ
^ₒ-monotone-in-exponent {𝓤} {𝓥} α β γ 𝕗@(f , _) =
 transport₂⁻¹ _⊴_
  (^ₒ-behaviour α β) (^ₒ-behaviour α γ)
  (transport (λ - → sup - ⊴ sup G) I (sup-composition-⊴ f' G))
  where
   F = ^ₒ-family α β
   G = ^ₒ-family α γ

   f' : 𝟙 + ⟨ β ⟩ → 𝟙 + ⟨ γ ⟩
   f' = cases (λ _ → inl ⋆) (λ b → inr (f b))

   initial-segments-agree : (b : ⟨ β ⟩) → β ↓ b ＝ γ ↓ f b
   initial-segments-agree b = simulations-preserve-↓ β γ 𝕗 b

   I : G ∘ f' ＝ F
   I = dfunext fe' II
    where
     II : (x : 𝟙 + ⟨ β ⟩) → G (f' x) ＝ F x
     II (inl ⋆) = refl
     II (inr b) = ap (λ - → α ^ₒ - ×ₒ α) (initial-segments-agree b ⁻¹)

\end{code}

\begin{code}

^ₒ-satisfies-zero-specification : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤)
                                → exp-specification-zero {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisfies-zero-specification {𝓤} {𝓥} α = ⊴-antisym (α ^ₒ 𝟘ₒ) 𝟙ₒ I II
 where
  I : α ^ₒ 𝟘ₒ ⊴ 𝟙ₒ
  I = ^ₒ-is-lower-bound-of-upper-bounds α 𝟘ₒ 𝟙ₒ (⊴-refl 𝟙ₒ) 𝟘-induction

  II : 𝟙ₒ ⊴ α ^ₒ 𝟘ₒ
  II = ^ₒ-has-least-element α 𝟘ₒ

\end{code}

\begin{code}

^ₒ-⊴-×ₒ-base : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
             → 𝟙ₒ {𝓦} ⊴ α
             → α ^ₒ β ⊴ α ^ₒ β ×ₒ α
^ₒ-⊴-×ₒ-base α β l =
 ⊴-trans (α ^ₒ β) (α ^ₒ β ×ₒ 𝟙ₒ) (α ^ₒ β ×ₒ α)
  (＝-to-⊴ (α ^ₒ β) (α ^ₒ β ×ₒ 𝟙ₒ) ((𝟙ₒ-right-neutral-×ₒ (α ^ₒ β)) ⁻¹))
  (×ₒ-right-monotone-⊴ (α ^ₒ β) 𝟙ₒ α (𝟙ₒ-⊴-shift α l))

^ₒ-satisifies-succ-specification : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                 → exp-specification-succ {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisifies-succ-specification {𝓤} {𝓥} α l β =
 ⊴-antisym (α ^ₒ (β +ₒ 𝟙ₒ)) (α ^ₒ β ×ₒ α) I II
  where
   I : α ^ₒ (β +ₒ 𝟙ₒ) ⊴ α ^ₒ β ×ₒ α
   I = ^ₒ-is-lower-bound-of-upper-bounds α (β +ₒ 𝟙ₒ) (α ^ₒ β ×ₒ α) I₁ I₂
    where
     I₁ : 𝟙ₒ ⊴ α ^ₒ β ×ₒ α
     I₁ = ⊴-trans 𝟙ₒ (α ^ₒ β) (α ^ₒ β ×ₒ α)
           (^ₒ-is-upper-bound₁ α β)
           (^ₒ-⊴-×ₒ-base α β l)
     I₂ : (x : ⟨ β +ₒ 𝟙ₒ ⟩) → α ^ₒ ((β +ₒ 𝟙ₒ) ↓ x) ×ₒ α ⊴ α ^ₒ β ×ₒ α
     I₂ (inl b) = ⊴-trans
                   (α ^ₒ ((β +ₒ 𝟙ₒ) ↓ inl b) ×ₒ α)
                   (α ^ₒ β)
                   (α ^ₒ β ×ₒ α)
                   (transport (_⊴ α ^ₒ β)
                     (ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-left b))
                     (^ₒ-is-upper-bound₂ α β))
                   (^ₒ-⊴-×ₒ-base α β l)
     I₂ (inr ⋆) = ＝-to-⊴
                   (α ^ₒ ((β +ₒ 𝟙ₒ) ↓ inr ⋆) ×ₒ α)
                   (α ^ₒ β ×ₒ α)
                   (ap (λ - → α ^ₒ - ×ₒ α) (successor-lemma-right β))
   II : α ^ₒ β ×ₒ α ⊴ α ^ₒ (β +ₒ 𝟙ₒ)
   II = transport
         (_⊴ α ^ₒ (β +ₒ 𝟙ₒ))
         (ap (λ - → α ^ₒ - ×ₒ α) (successor-lemma-right β))
         (^ₒ-is-upper-bound₂ α (β +ₒ 𝟙ₒ))

\end{code}

\begin{code}

^ₒ-𝟙ₒ-is-neutral : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ^ₒ 𝟙ₒ ＝ α
^ₒ-𝟙ₒ-is-neutral {𝓤} α l =
 α ^ₒ 𝟙ₒ             ＝⟨ ap (α ^ₒ_) (𝟘ₒ-left-neutral 𝟙ₒ ⁻¹)  ⟩
 α ^ₒ (𝟘ₒ {𝓤} +ₒ 𝟙ₒ) ＝⟨ ^ₒ-satisifies-succ-specification α l 𝟘ₒ ⟩
 α ^ₒ (𝟘ₒ) ×ₒ α      ＝⟨ ap (_×ₒ α) (^ₒ-satisfies-zero-specification α) ⟩
 𝟙ₒ ×ₒ α             ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
 α                   ∎

^ₒ-𝟚ₒ-is-×ₒ : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ^ₒ 𝟚ₒ ＝ α ×ₒ α
^ₒ-𝟚ₒ-is-×ₒ α p =
 α ^ₒ (𝟙ₒ +ₒ 𝟙ₒ) ＝⟨ ^ₒ-satisifies-succ-specification α p 𝟙ₒ ⟩
 α ^ₒ 𝟙ₒ ×ₒ α    ＝⟨ ap (_×ₒ α) (^ₒ-𝟙ₒ-is-neutral α p) ⟩
 α ×ₒ α          ∎

\end{code}

\begin{code}

^ₒ-satisfies-sup-specification-generalized :
   {𝓤 𝓥 : Universe} (α : Ordinal 𝓤)
 → exp-specification-sup-generalized {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisfies-sup-specification-generalized {𝓤} {𝓥} α p {S} S-inh F =
 ⊴-antisym (α ^ₒ sup F) (sup (λ - → α ^ₒ F (lower -))) I II
  where
   II : sup (λ - → α ^ₒ F (lower -)) ⊴ α ^ₒ sup F
   II = sup-is-lower-bound-of-upper-bounds
         (λ - → α ^ₒ F (lower -))
         (α ^ₒ sup F)
         (λ i → ^ₒ-monotone-in-exponent α (F (lower i)) (sup F)
                 (sup-is-upper-bound F (lower i)))

   I : α ^ₒ sup F ⊴ sup (λ - → α ^ₒ F (lower -))
   I = ^ₒ-is-lower-bound-of-upper-bounds
        α
        (sup F)
        (sup (λ - → α ^ₒ F (lower -)))
        I₁
        I₂
    where
     I₁ : 𝟙ₒ ⊴ sup (λ - → α ^ₒ F (lower -))
     I₁ = ∥∥-rec (⊴-is-prop-valued 𝟙ₒ (sup (λ - → α ^ₒ F (lower -)))) I₁' S-inh
      where
       I₁' : S → 𝟙ₒ ⊴ sup (λ - → α ^ₒ F (lower -))
       I₁' s₀ = ⊴-trans
                 𝟙ₒ
                 (α ^ₒ (F s₀))
                 (sup (λ - → α ^ₒ F (lower -)))
                 (^ₒ-is-upper-bound₁ α (F s₀))
                 (sup-is-upper-bound (λ - → α ^ₒ F (lower -)) (lift 𝓤 s₀))
     I₂ : (y : ⟨ sup F ⟩)
        → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup (λ - → α ^ₒ F (lower -))
     I₂ y = ∥∥-rec
             (⊴-is-prop-valued (α ^ₒ (sup F ↓ y) ×ₒ α) (sup (λ - → α ^ₒ F (lower -))))
             I₂'
             (initial-segment-of-sup-is-initial-segment-of-some-component F y)
      where
       I₂' : (Σ s ꞉ S , Σ x ꞉ ⟨ F s ⟩ , sup F ↓ y ＝ F s ↓ x)
           → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup (λ - → α ^ₒ F (lower -))
       I₂' (s , x , p) =
        transport⁻¹
         (_⊴ sup (λ - → α ^ₒ F (lower -)))
         (ap (λ - → α ^ₒ - ×ₒ α) p)
         (⊴-trans (α ^ₒ (F s ↓ x) ×ₒ α) (α ^ₒ F s) (sup (λ - → α ^ₒ (F (lower -))))
          (^ₒ-is-upper-bound₂ α (F s))
          (sup-is-upper-bound (λ - → α ^ₒ (F (lower -))) (lift 𝓤 s)))

^ₒ-satisfies-sup-specification : (α : Ordinal 𝓤) → exp-specification-sup α (α ^ₒ_)
^ₒ-satisfies-sup-specification α =
 exp-specification-sup-from-generalized
  α (α ^ₒ_) (^ₒ-satisfies-sup-specification-generalized α)

-- curiosity : (P : 𝓤 ̇ ) → (pp : is-prop P) → exp {𝓤} 𝟚ₒ (prop-ordinal P pp) ＝ 𝟙ₒ +ₒ prop-ordinal P pp
-- curiosity {𝓤} P pp = transport⁻¹ (λ - → - ＝ 𝟙ₒ +ₒ (prop-ordinal P pp))
--                                  (^ₒ-behaviour 𝟚ₒ (prop-ordinal P pp) ∙ ap sup (dfunext fe' eq))
--                                  (⊴-antisym (sup F) (𝟙ₒ +ₒ prop-ordinal P pp)
--                                             (sup-is-lower-bound-of-upper-bounds F _ upper-bound)
--                                             (g , g-is-simulation))
--  where
--   F : 𝟙 + P → Ordinal 𝓤
--   F (inl _) = 𝟙ₒ
--   F (inr p) = 𝟚ₒ

--   eq : (i : 𝟙 + P) → (cases (λ _ → 𝟙ₒ) (λ b → exp 𝟚ₒ (prop-ordinal P pp ↓ b) ×ₒ 𝟚ₒ)) i ＝ F i
--   eq (inl _) = refl
--   eq (inr p) = exp 𝟚ₒ (prop-ordinal P pp ↓ p) ×ₒ 𝟚ₒ ＝⟨ ap (λ z → exp 𝟚ₒ z ×ₒ 𝟚ₒ) (prop-ordinal-↓ P pp p) ⟩
--                exp 𝟚ₒ 𝟘ₒ ×ₒ 𝟚ₒ                      ＝⟨ ap (_×ₒ 𝟚ₒ) (^ₒ-satisfies-zero-specification 𝟚ₒ) ⟩
--                𝟙ₒ ×ₒ 𝟚ₒ                             ＝⟨ 𝟙ₒ-left-neutral-×ₒ 𝟚ₒ ⟩
--                𝟚ₒ ∎

--   upper-bound : (i : 𝟙 + P) → F i ⊴ (𝟙ₒ +ₒ prop-ordinal P pp)
--   upper-bound (inl _) = (λ _ → inl _) , (λ x → dep-cases (λ _ → 𝟘-elim) (λ p → 𝟘-elim)) , (λ _ _ q → 𝟘-elim q)
--   upper-bound (inr p) = cases inl (λ _ → inr p) , (λ { (inr p') (inl _) _ → (inl _) , (⋆ , refl)
--                                                      ; (inl _) (inr p') q → 𝟘-elim q
--                                                      ; (inr p') (inr p'') q → 𝟘-elim q})
--                                                 , (λ { (inl _) (inr p') q → ⋆
--                                                      ; (inl _) (inl _) q → 𝟘-elim q})

--   f : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ F i ⟩
--   f (inl _) = ⋆
--   f (inr p) = inr ⋆

--   g : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ sup F ⟩
--   g i = pr₁ (sup-is-upper-bound F i) (f i)

--   g-is-initial-segment : is-initial-segment (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-initial-segment (inl _) y q = inl ⋆ , pr₂ (pr₁ (pr₂ (sup-is-upper-bound F (inl _))) ⋆ y q)
--   g-is-initial-segment (inr p) y q with pr₁ (pr₂ (sup-is-upper-bound F (inr p))) (inr ⋆) y q
--   ... | inl _ , _ , refl = inl ⋆ , ⋆ , ↓-lc (sup F)
--                                             (pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
--                                             (pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
--                                             e
--    where
--     e = (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
--           ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
--         (𝟙ₒ ↓ ⋆)
--           ＝⟨ +ₒ-↓-left ⋆ ⟩
--         (𝟚ₒ ↓ inl ⋆)
--           ＝⟨ initial-segment-of-sup-at-component F (inr p) (inl ⋆) ⁻¹ ⟩
--         (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
--           ∎

--   g-is-order-preserving : is-order-preserving (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-order-preserving (inl _) (inr p) _ = ↓-reflects-order (sup F) (g (inl _)) (g (inr p)) q
--    where
--     eq₁ = sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆
--             ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
--           𝟙ₒ ↓ ⋆
--             ＝⟨ prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⟩
--           𝟘ₒ
--             ∎
--     eq₂ = sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆)
--             ＝⟨ initial-segment-of-sup-at-component F (inr p) (inr ⋆) ⟩
--           (𝟚ₒ ↓ inr ⋆)
--             ＝⟨ successor-lemma-right 𝟙ₒ ⟩
--           𝟙ₒ
--             ∎
--     q : (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆) ⊲ (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆))
--     q = transport₂⁻¹ _⊲_ eq₁ eq₂ (⋆ , (prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⁻¹))
--   g-is-order-preserving (inl _) (inl _) q = 𝟘-elim q

--   g-is-simulation : is-simulation (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-simulation = g-is-initial-segment , g-is-order-preserving



-- \end{code}

-- Added 16 September 2024 by Tom de Jong.

-- \begin{code}

-- exp-+-distributes : {𝓤 : Universe} (α β γ : Ordinal 𝓤)
--                   → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ
-- exp-+-distributes {𝓤} α β =
--  transfinite-induction-on-OO (λ γ → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ) I
--   where
--    I : (γ : Ordinal 𝓤)
--      → ((c : ⟨ γ ⟩) → α ^ₒ (β +ₒ (γ ↓ c)) ＝ α ^ₒ β ×ₒ α ^ₒ (γ ↓ c))
--      → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ
--    I γ IH = ^ₒ-behaviour α (β +ₒ γ) ∙ III ∙ II ⁻¹
--     where
--      III : sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α))
--          ＝ sup (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α))
--      III = ⊴-antisym _ _ III₁ III₂
--       where
--        III₁ : sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α))
--             ⊴ sup (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α))
--        III₁ = sup-is-lower-bound-of-upper-bounds _ _ ub
--         where
--          ub : (i : 𝟙 + ⟨ β +ₒ γ ⟩)
--             → cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α) i
--             ⊴ sup (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α))
--          ub (inl ⋆) = ⊴-trans 𝟙ₒ (α ^ₒ β) _ (exp-has-least-element α β) (sup-is-upper-bound _ (inl ⋆))
--          ub (inr (inl b)) = ⊴-trans _ (α ^ₒ β) _
--                              (transport⁻¹ (_⊴ α ^ₒ β) (ap (λ - → α ^ₒ - ×ₒ α) ((+ₒ-↓-left b) ⁻¹)) (exp-component-⊴ α β))
--                              (sup-is-upper-bound _ (inl ⋆))
--          ub (inr (inr c)) = transport⁻¹
--                              (_⊴ sup {_} {𝟙{𝓤} + ⟨ γ ⟩} (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α)))
--                              (ap (λ - → α ^ₒ - ×ₒ α) ((+ₒ-↓-right c) ⁻¹))
--                              (sup-is-upper-bound _ (inr c))
--        III₂ : sup (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α))
--             ⊴ sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α))
--        III₂ = sup-is-lower-bound-of-upper-bounds _ _ ub
--         where
--          ub : (i : 𝟙 + ⟨ γ ⟩)
--             → cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α) i
--             ⊴ sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α))
--          ub (inl ⋆) = transport⁻¹
--                        (_⊴ sup {_} {𝟙{𝓤} + ⟨ β +ₒ γ ⟩} (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α)))
--                        (^ₒ-behaviour α β)
--                        (sup-is-lower-bound-of-upper-bounds _ _ h)
--           where
--            h : (j : 𝟙 + ⟨ β ⟩)
--              → cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ (β ↓ b) ×ₒ α) j
--              ⊴ sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α))
--            h (inl ⋆) = sup-is-upper-bound _ (inl ⋆)
--            h (inr b) = transport⁻¹
--                          (_⊴ sup {_} {𝟙 + ⟨ β +ₒ γ ⟩} (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α)))
--                          (ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-left b))
--                          (sup-is-upper-bound _ (inr (inl b)))
--          ub (inr c) = transport⁻¹
--                        (_⊴ sup {_} {𝟙{𝓤} + ⟨ β +ₒ γ ⟩} (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β +ₒ γ) ↓ x) ×ₒ α)))
--                        (ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-right c))
--                        (sup-is-upper-bound _ (inr (inr c)))

--      II = α ^ₒ β ×ₒ α ^ₒ γ ＝⟨ ap (α ^ₒ β ×ₒ_) (^ₒ-behaviour α γ) ⟩
--           α ^ₒ β ×ₒ (sup (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α))) ＝⟨ ×ₒ-preserves-suprema pt sr (α ^ₒ β) _ ⟩
--           sup (λ i → α ^ₒ β ×ₒ (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α)) i) ＝⟨ ap sup (dfunext fe' h) ⟩
--           sup (cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α)) ∎
--       where
--        h : (λ i → α ^ₒ β ×ₒ cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α) i)
--          ∼ cases (λ _ → α ^ₒ β) (λ c → α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α)
--        h (inl ⋆) = 𝟙ₒ-right-neutral-×ₒ (α ^ₒ β)
--        h (inr c) = α ^ₒ β ×ₒ (α ^ₒ (γ ↓ c) ×ₒ α) ＝⟨ ×ₒ-assoc (α ^ₒ β) (α ^ₒ (γ ↓ c)) α ⁻¹ ⟩
--                    (α ^ₒ β ×ₒ α ^ₒ (γ ↓ c)) ×ₒ α ＝⟨ ap (_×ₒ α) ((IH c) ⁻¹) ⟩
--                    α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α       ∎

-- ^ₒ-satisifies-succ-specification' : (α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
--                                   → α ^ₒ (β +ₒ 𝟙ₒ) ＝ (α ^ₒ β) ×ₒ α
-- ^ₒ-satisifies-succ-specification' α β l =
--  exp-+-distributes α β 𝟙ₒ ∙ ap (α ^ₒ β ×ₒ_) (exp-power-one-is-identity α l)

-- iterated-exp-is-exp-by-×ₒ : (α β γ : Ordinal 𝓤)
--                           → exp (α ^ₒ β) γ ＝ α ^ₒ (β ×ₒ γ)
-- iterated-exp-is-exp-by-×ₒ {𝓤} α β =
--  transfinite-induction-on-OO
--   (λ γ → exp (α ^ₒ β) γ ＝ α ^ₒ (β ×ₒ γ))
--   I
--   where
--    I : (γ : Ordinal 𝓤)
--      → ((c : ⟨ γ ⟩) → exp (α ^ₒ β) (γ ↓ c) ＝ α ^ₒ (β ×ₒ (γ ↓ c)))
--      → exp (α ^ₒ β) γ ＝ α ^ₒ (β ×ₒ γ)
--    I γ IH = ⊴-antisym (exp (α ^ₒ β) γ) (α ^ₒ (β ×ₒ γ)) II III
--     where
--      II : exp (α ^ₒ β) γ ⊴ α ^ₒ (β ×ₒ γ)
--      II = transport⁻¹ (_⊴ α ^ₒ (β ×ₒ γ)) (^ₒ-behaviour (α ^ₒ β) γ) II'
--       where
--        II' : sup (cases (λ _ → 𝟙ₒ) (λ c → exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ β))
--            ⊴ α ^ₒ (β ×ₒ γ)
--        II' = sup-is-lower-bound-of-upper-bounds _ _ ub
--         where
--          ub : (i : 𝟙 + ⟨ γ ⟩)
--             → cases (λ _ → 𝟙ₒ) (λ b → exp (α ^ₒ β) (γ ↓ b) ×ₒ α ^ₒ β) i
--               ⊴ α ^ₒ (β ×ₒ γ)
--          ub (inl ⋆) = exp-has-least-element α (β ×ₒ γ)
--          ub (inr c) = transport⁻¹ (_⊴ α ^ₒ (β ×ₒ γ))
--                        eq
--                        (^ₒ-monotone-in-exponent α
--                          (β ×ₒ ((γ ↓ c) +ₒ 𝟙ₒ)) (β ×ₒ γ)
--                          (×ₒ-right-monotone-⊴ β ((γ ↓ c) +ₒ 𝟙ₒ) γ
--                            (upper-bound-of-successors-of-initial-segments γ c)))
--           where
--            eq = exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ β ＝⟨ ap (_×ₒ α ^ₒ β) (IH c) ⟩
--                 α ^ₒ (β ×ₒ (γ ↓ c)) ×ₒ α ^ₒ β  ＝⟨ (exp-+-distributes α (β ×ₒ (γ ↓ c)) β) ⁻¹ ⟩
--                 α ^ₒ ((β ×ₒ (γ ↓ c)) +ₒ β)      ＝⟨ ap (α ^ₒ) ((×ₒ-successor β (γ ↓ c)) ⁻¹) ⟩
--                 α ^ₒ (β ×ₒ ((γ ↓ c) +ₒ 𝟙ₒ))     ∎
--      III : α ^ₒ (β ×ₒ γ) ⊴ exp (α ^ₒ β) γ
--      III = transport⁻¹ (_⊴ exp (α ^ₒ β) γ) (^ₒ-behaviour α (β ×ₒ γ)) III'
--       where
--        III' : sup (cases (λ _ → 𝟙ₒ) (λ x → α ^ₒ ((β ×ₒ γ) ↓ x) ×ₒ α))
--             ⊴ exp (α ^ₒ β) γ
--        III' = sup-is-lower-bound-of-upper-bounds _ _ ub
--         where
--          ub : (i : 𝟙 + ⟨ β ×ₒ γ ⟩)
--             → cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ ((β ×ₒ γ) ↓ b) ×ₒ α) i
--               ⊴ exp (α ^ₒ β) γ
--          ub (inl ⋆)       = exp-has-least-element (α ^ₒ β) γ
--          ub (inr (b , c)) = transport⁻¹ (_⊴ exp (α ^ₒ β) γ) eq IV
--           where
--            eq = α ^ₒ ((β ×ₒ γ) ↓ (b , c)) ×ₒ α                 ＝⟨ ap (λ - → α ^ₒ - ×ₒ α) (×ₒ-↓ β γ) ⟩
--                 α ^ₒ ((β ×ₒ (γ ↓ c)) +ₒ (β ↓ b)) ×ₒ α          ＝⟨ ap (_×ₒ α) (exp-+-distributes α (β ×ₒ (γ ↓ c)) (β ↓ b)) ⟩
--                 ((α ^ₒ (β ×ₒ (γ ↓ c))) ×ₒ α ^ₒ (β ↓ b)) ×ₒ α  ＝⟨ ap (λ - → (- ×ₒ α ^ₒ (β ↓ b)) ×ₒ α) ((IH c) ⁻¹) ⟩
--                 (exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ (β ↓ b)) ×ₒ α   ＝⟨ ×ₒ-assoc (exp (α ^ₒ β) (γ ↓ c)) (α ^ₒ (β ↓ b)) α ⟩
--                 (exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α)) ∎
--            IV : (exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α)) ⊴ exp (α ^ₒ β) γ
--            IV = transport⁻¹ ((exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α)) ⊴_) (^ₒ-behaviour (α ^ₒ β) γ) IV'
--             where
--              IV' : (exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α))
--                  ⊴ sup (cases (λ _ → 𝟙ₒ) (λ c → exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ β))
--              IV' = ⊴-trans
--                     (exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α))
--                     (exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ β)
--                     (sup (cases (λ _ → 𝟙ₒ) (λ c' → exp (α ^ₒ β) (γ ↓ c') ×ₒ α ^ₒ β)))
--                     IV''
--                     (sup-is-upper-bound _ (inr c))
--               where
--                IV'' : (exp (α ^ₒ β) (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α))
--                     ⊴ (exp (α ^ₒ β) (γ ↓ c) ×ₒ α ^ₒ β)
--                IV'' = ×ₒ-right-monotone-⊴
--                        (exp (α ^ₒ β) (γ ↓ c))
--                        (α ^ₒ (β ↓ b) ×ₒ α)
--                        (α ^ₒ β)
--                        (exp-component-⊴ α β)

-- \end{code}

-- Added 17 September 2024 by Tom de Jong.

-- \begin{code}

-- exp-⊲-lemma : (α β : Ordinal 𝓤)
--             → 𝟙ₒ ⊲ α
--             → {b : ⟨ β ⟩} → α ^ₒ (β ↓ b) ⊲ α ^ₒ β
-- exp-⊲-lemma {𝓤} α β (a₀ , e) {b} = x , (eq' ⁻¹ ∙ eq)
--  where
--   ⊥ : ⟨ α ^ₒ (β ↓ b) ⟩
--   ⊥ = pr₁ (𝟘ₒ-initial-segment-of-α ^ₒ (β ↓ b))

--   ⊥-is-least : (α ^ₒ (β ↓ b) ↓ ⊥) ＝ 𝟘ₒ
--   ⊥-is-least = (pr₂ (𝟘ₒ-initial-segment-of-α ^ₒ (β ↓ b))) ⁻¹

--   s : Ordinal 𝓤
--   s = sup (cases (λ _ → 𝟙ₒ) (λ b' → α ^ₒ (β ↓ b') ×ₒ α))

--   x' : ⟨ s ⟩
--   x' = [ α ^ₒ (β ↓ b) ×ₒ α , s ]⟨ sup-is-upper-bound _ (inr b) ⟩ (⊥ , a₀)

--   eq' : s ↓ x' ＝ α ^ₒ (β ↓ b)
--   eq' = s ↓ x' ＝⟨ initial-segment-of-sup-at-component _ (inr b) (⊥ , a₀) ⟩
--         (α ^ₒ (β ↓ b) ×ₒ α) ↓ (⊥ , a₀) ＝⟨ ×ₒ-↓ (α ^ₒ (β ↓ b)) α ⟩
--         (α ^ₒ (β ↓ b) ×ₒ (α ↓ a₀)) +ₒ (α ^ₒ (β ↓ b) ↓ ⊥) ＝⟨ ap ((α ^ₒ (β ↓ b) ×ₒ (α ↓ a₀)) +ₒ_) ⊥-is-least ⟩
--         (α ^ₒ (β ↓ b) ×ₒ (α ↓ a₀)) +ₒ 𝟘ₒ ＝⟨ 𝟘ₒ-right-neutral (α ^ₒ (β ↓ b) ×ₒ (α ↓ a₀)) ⟩
--         α ^ₒ (β ↓ b) ×ₒ (α ↓ a₀) ＝⟨ ap (α ^ₒ (β ↓ b) ×ₒ_) (e ⁻¹) ⟩
--         α ^ₒ (β ↓ b) ×ₒ 𝟙ₒ ＝⟨ 𝟙ₒ-right-neutral-×ₒ (α ^ₒ (β ↓ b)) ⟩
--         α ^ₒ (β ↓ b) ∎

--   x : ⟨ α ^ₒ β ⟩
--   x = Idtofun (ap ⟨_⟩ (^ₒ-behaviour α β ⁻¹)) x'

--   eq : s ↓ x' ＝ α ^ₒ β ↓ x
--   eq = lemma s (α ^ₒ β) (^ₒ-behaviour α β ⁻¹)
--    where
--     -- TODO: Upstream
--     lemma : (α' β' : Ordinal 𝓤) (e : α' ＝ β') {a : ⟨ α' ⟩}
--           → α' ↓ a ＝ β' ↓ Idtofun (ap ⟨_⟩ e) a
--     lemma α' β' refl = refl

-- exp-strictly-monotone : (α β γ : Ordinal 𝓤)
--                       → 𝟙ₒ ⊲ α → β ⊲ γ → α ^ₒ β ⊲ α ^ₒ γ
-- exp-strictly-monotone {𝓤} α β γ h (c , refl) = exp-⊲-lemma α γ h

-- Added 12 November 2024.
-- module _ {𝓤 : Universe}
--  where

--  [_]ₒ : (n : ℕ) → Ordinal 𝓤
--  [ 0 ]ₒ = 𝟘ₒ
--  [ 1 ]ₒ = 𝟙ₒ
--  [ succ n ]ₒ = [ n ]ₒ +ₒ 𝟙ₒ

--  -- TODO: Upstream(?)
--  {-
--  open import Naturals.Addition renaming (_+_ to _+ℕ_)
--  open import Naturals.Multiplication
--  []ₒ-preserves-addition : {n m : ℕ} → [ n ]ₒ +ₒ [ m ]ₒ ＝ [ n +ℕ m ]ₒ
--  []ₒ-preserves-addition {n} {0} = 𝟘ₒ-right-neutral [ n ]ₒ
--  []ₒ-preserves-addition {0} {1} = 𝟘ₒ-left-neutral 𝟙ₒ
--  []ₒ-preserves-addition {succ n} {1} = refl
--  []ₒ-preserves-addition {n} {succ (m'@(succ m))} =
--   ([ n ]ₒ +ₒ ([ m' ]ₒ +ₒ 𝟙ₒ)) ＝⟨ (+ₒ-assoc [ n ]ₒ [ m' ]ₒ 𝟙ₒ) ⁻¹ ⟩
--   (([ n ]ₒ +ₒ [ m' ]ₒ) +ₒ 𝟙ₒ) ＝⟨ ap (_+ₒ 𝟙ₒ) []ₒ-preserves-addition ⟩
--   ([ n +ℕ m' ]ₒ +ₒ 𝟙ₒ)        ∎

--  []ₒ-preserves-multiplication : {n m : ℕ} → [ n ]ₒ ×ₒ [ m ]ₒ ＝ [ n * m ]ₒ
--  []ₒ-preserves-multiplication {n} {0} = ×ₒ-𝟘ₒ-right [ n ]ₒ
--  []ₒ-preserves-multiplication {n} {1} = 𝟙ₒ-right-neutral-×ₒ [ n ]ₒ
--  []ₒ-preserves-multiplication {n} {succ (m'@(succ m))} =
--   [ n ]ₒ ×ₒ ([ m' ]ₒ +ₒ 𝟙ₒ)     ＝⟨ ×ₒ-successor [ n ]ₒ [ m' ]ₒ ⟩
--   ([ n ]ₒ ×ₒ [ m' ]ₒ) +ₒ [ n ]ₒ ＝⟨ ap (_+ₒ [ n ]ₒ) []ₒ-preserves-multiplication ⟩
--   [ n * m' ]ₒ +ₒ [ n ]ₒ         ＝⟨ []ₒ-preserves-addition ⟩
--   [ n * m' +ℕ n ]ₒ              ＝⟨ ap [_]ₒ (addition-commutativity (n * m') n) ⟩
--   [ n +ℕ (n * m') ]ₒ            ＝⟨ refl ⟩
--   [ n * succ m' ]ₒ              ∎
--  -}

-- -- TODO: Upstream and clean
-- holds-gives-equal-𝟙ₒ : {P : 𝓤 ̇ } (i : is-prop P) → P → prop-ordinal P i ＝ 𝟙ₒ
-- holds-gives-equal-𝟙ₒ {𝓤} {P} i p = eqtoidₒ (ua 𝓤) fe' (prop-ordinal P i) 𝟙ₒ (f , order-preserving-reflecting-equivs-are-order-equivs (prop-ordinal P i) 𝟙ₒ f (qinvs-are-equivs f ((λ _ → p) , (i p , 𝟙-is-prop ⋆))) (λ _ _ → 𝟘-elim) λ _ _ → 𝟘-elim)
--  where
--   f : P → 𝟙
--   f _ = ⋆

-- -- TODO: Think about a better name?
-- exp-weakly-monotone-in-base-implies-EM :
--    ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊲ β → (α ^ₒ γ ⊴ β ^ₒ γ))
--  → EM 𝓤
-- exp-weakly-monotone-in-base-implies-EM {𝓤} assumption P P-is-prop = VI (f x) refl
--  where
--   α β γ Pₒ : Ordinal 𝓤
--   α = [ 2 ]ₒ
--   Pₒ = prop-ordinal P P-is-prop
--   β = [ 3 ]ₒ +ₒ Pₒ
--   γ = [ 2 ]ₒ

--   I : α ⊲ β
--   I = (inl (inr ⋆) , ((successor-lemma-right α) ⁻¹ ∙ +ₒ-↓-left (inr ⋆)))

--   α-ineq : 𝟙ₒ ⊴ α
--   α-ineq = ⊲-gives-⊴ 𝟙ₒ α (successor-increasing 𝟙ₒ)

--   β-ineq : 𝟙ₒ ⊴ β
--   β-ineq = ⊴-trans 𝟙ₒ α β α-ineq (⊲-gives-⊴ α β I)

--   II : α ^ₒ γ ⊴ β ^ₒ γ
--   II = assumption α β γ α-ineq I

--   III : α ^ₒ γ ＝ α ×ₒ α
--   III = ^ₒ-𝟚ₒ-is-×ₒ α α-ineq

--   IV : β ^ₒ γ ＝ (β ×ₒ β)
--   IV = ^ₒ-𝟚ₒ-is-×ₒ β β-ineq

--   x : ⟨ α ×ₒ α ⟩
--   x = (inr ⋆ , inr ⋆)

--   𝕗 : (α ×ₒ α) ⊴ (β ×ₒ β)
--   𝕗 = ⊴-trans _ _ _ (≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ (III ⁻¹)))
--                     (⊴-trans _ _ _ II (≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ IV)))

--   f : ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
--   f = [ α ×ₒ α , β ×ₒ β ]⟨ 𝕗 ⟩

--   pattern ⊥β = inl (inl (inl ⋆))

--   f' : P → ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
--   f' p (inl ⋆ , inl ⋆) = (⊥β , ⊥β)
--   f' p (inr ⋆ , inl ⋆) = (inl (inl (inr ⋆)) , ⊥β)
--   f' p (inl ⋆ , inr ⋆) = (inl (inr ⋆) , ⊥β)
--   f' p (inr ⋆ , inr ⋆) = (inr p , ⊥β)

--   f'-simulation : (p : P) → is-simulation (α ×ₒ α) (β ×ₒ β) (f' p)
--   f'-simulation p = f'-initial-seg , f'-order-pres
--    where
--     f'-initial-seg : is-initial-segment (α ×ₒ α) (β ×ₒ β) (f' p)
--     f'-initial-seg (inr ⋆ , inl ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inr (refl , l) , refl
--     f'-initial-seg (inl ⋆ , inr ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inl ⋆ , inr ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = (inr ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = (inr ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inr ⋆) , .⊥β)       (inr (refl , l))
--      = (inl ⋆ , inr ⋆) , inr (refl , l) , refl
--     f'-initial-seg (inl ⋆ , inl ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inr ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inr ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inl ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inl ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inr ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inr ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l

--     f'-order-pres : is-order-preserving (α ×ₒ α) (β ×ₒ β) (f' p)
--     f'-order-pres (inl ⋆ , inl ⋆) (inl ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inl ⋆ , inl ⋆) (inr ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inr ⋆ , inl ⋆) (inl ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inr ⋆ , inl ⋆) (inr ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (x , inr ⋆) (y , inl ⋆) (inl l) = 𝟘-elim l
--     f'-order-pres (x , inr ⋆) (y , inr ⋆) (inl l) = 𝟘-elim l
--     f'-order-pres (inl ⋆ , inl ⋆) (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
--     f'-order-pres (inl ⋆ , inr ⋆) (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
--     f'-order-pres (inr ⋆ , x') (inl ⋆ , x') (inr (refl , l)) = 𝟘-elim l
--     f'-order-pres (inr ⋆ , x') (inr ⋆ , x') (inr (refl , l)) = 𝟘-elim l

--   V : (p : P) → f ∼ f' p
--   V p = at-most-one-simulation (α ×ₒ α) (β ×ₒ β) f (f' p) (pr₂ 𝕗) (f'-simulation p)

--   VI : (y : ⟨ β ×ₒ β ⟩) → f x ＝ y → P + ¬ P
--   VI (inl y , y') r = inr (λ p → +disjoint (ap pr₁ (VII p)))
--    where
--     VII : (p : P) → (inl y , y') ＝ (inr p , ⊥β)
--     VII p = (inl y , y') ＝⟨ r ⁻¹ ⟩
--             f x          ＝⟨ V p x ⟩
--             (inr p , ⊥β) ∎
--   VI (inr p , y') r = inl p

-- exp-monotone-in-base-implies-EM :
--    ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ))
--  → EM 𝓤
-- exp-monotone-in-base-implies-EM m =
--  exp-weakly-monotone-in-base-implies-EM (λ α β γ l i → m α β γ l (⊲-gives-⊴ α β i))

-- EM-implies-exp-monotone-in-base : EM 𝓤
--  → (α β γ : Ordinal 𝓤) → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ)
-- EM-implies-exp-monotone-in-base {𝓤} em α β γ l =
--  transfinite-induction-on-OO _ I γ
--  where
--   I : (γ : Ordinal 𝓤) → ((c : ⟨ γ ⟩) → (α ^ₒ (γ ↓ c) ⊴ β ^ₒ (γ ↓ c)))
--     → (α ^ₒ γ ⊴ β ^ₒ γ)
--   I γ IH = transport₂⁻¹ _⊴_ (^ₒ-behaviour α γ) (^ₒ-behaviour β γ)
--             (sup-monotone
--              (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α))
--              (cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β))
--              κ)
--    where
--     κ : (i : 𝟙 + ⟨ γ ⟩)
--       → cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α) i
--       ⊴ cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β) i
--     κ (inl ⋆) = ⊴-refl 𝟙ₒ
--     κ (inr c) = EM-implies-induced-⊴-on-×ₒ em (α ^ₒ (γ ↓ c)) α
--                                               (β ^ₒ (γ ↓ c)) β
--                                               (IH c) l




-- {-
-- exp-simulation-lemma : (α β γ : Ordinal 𝓤)
--                        (f : ⟨ α ^ₒ β ⟩ → ⟨ α ^ₒ γ ⟩)
--                      → is-simulation (α ^ₒ β) (α ^ₒ γ) f
--                      → (b : ⟨ β ⟩) (e : ⟨ α ^ₒ (β ↓ b) ⟩) (a : ⟨ α ⟩)
--                      → Σ c ꞉ ⟨ γ ⟩ , Σ e' ꞉ ⟨ α ^ₒ (γ ↓ c) ⟩ ,
--                        Σ p ꞉ (α ^ₒ (β ↓ b) ＝ α ^ₒ (γ ↓ c)) , (Idtofun (ap ⟨_⟩ p) e ＝ e') × -- Maybe ask for p : (β ↓ b) ＝ (γ ↓ c)?
--                            (f ((pr₁ (exp-component-⊴ α β)) (e , a)) ＝ pr₁ (exp-component-⊴ α γ) (e' , a))
-- exp-simulation-lemma α β γ f f-sim b e a = {!!}

-- f [b , e , a] : α ^ₒ γ

-- * f [b , e , a] = [inl ⋆ , ⋆] <- needs assumptions on e and/or a to dispell this case
-- * f [b , e , a] = [c , e' , a']

--   (α ^ₒ (β ↓ b) × α) ↓ (e , a) ＝ (α ^ₒ (γ ↓ c) × α) ↓ (e' , a')
--           ||
--   (α ^ₒ (β ↓ b) × (α ↓ a)) + ((α ^ₒ (β ↓ b)) ↓ e)


-- In the special case where (e , a) ＝ (⊥ , a₀), the LHS is
--   α ^ₒ (β ↓ b)

-- Does f give a simulation α ^ₒ (β ↓ b) × α ⊴ α ^ₒ (γ ↓ c) × α for some c : γ
-- -}

-- {-
-- For proving the following we should maybe follow a strategy similar to the one
-- we had for proving left cancellability of multiplication. The idea/hope would be
-- that
--   if 𝟙 ＝ α ↓ a₀, then a simulation f : α ^ₒ β ⊴ α ^ₒ γ
--   satisfies f [b , ⊥ , a₀] = [c , ⊥ , a₀] for some c : γ
--   (or maybe more generally for any a : α?)
-- Via the construction of exp-⊲-lemma, this should give
--   α ^ₒ (β ↓ b) ⊴ α ^ₒ (γ ↓ c)
-- and so
--   (β ↓ b) ⊴ (γ ↓ c) by induction
-- and hence (maybe with ＝ instead??)
--   β ⊴ γ.

-- (⊥ , a₀) : α ^ₒ (β ↓ b) ×ₒ α

-- (α ^ₒ (β ↓ b) ×ₒ α) ↓ (⊥ , a₀) ＝ α ^ₒ (β ↓ b)


-- exp-cancellable-exponent : (α β γ : Ordinal 𝓤)
--                          → 𝟙ₒ ⊲ α → α ^ₒ β ＝ α ^ₒ γ → β ＝ γ
-- exp-cancellable-exponent = ?
-- -}

-- -- Some failed attemps

-- {-
-- exp-order-reflecting-exponent : (α β γ : Ordinal 𝓤)
--                               → 𝟙ₒ ⊲ α → α ^ₒ β ⊲ α ^ₒ γ → β ⊲ γ
-- exp-order-reflecting-exponent {𝓤} α = transfinite-induction-on-OO _ I
--  where
--   I : (β : Ordinal 𝓤)
--     → ((b : ⟨ β ⟩ ) (γ : Ordinal 𝓤) → 𝟙ₒ ⊲ α → α ^ₒ (β ↓ b) ⊲ α ^ₒ γ → (β ↓ b) ⊲ γ)
--     → (γ : Ordinal 𝓤) → 𝟙ₒ ⊲ α → α ^ₒ β ⊲ α ^ₒ γ → β ⊲ γ
--   I β IH γ h l = {!!}
--    where
--     II : (b : ⟨ β ⟩) → α ^ₒ (β ↓ b) ⊲ α ^ₒ γ
--     II b = ⊲-is-transitive (α ^ₒ (β ↓ b)) (α ^ₒ β) (α ^ₒ γ) (exp-strictly-monotone α (β ↓ b) β h (b , refl)) l
--     III : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
--     III b = IH b γ h (II b)

-- exp-weak-order-reflecting-exponent : (α β γ : Ordinal 𝓤)
--                                    → 𝟙ₒ ⊲ α → α ^ₒ β ⊴ α ^ₒ γ → β ⊴ γ
-- exp-weak-order-reflecting-exponent {𝓤} α = transfinite-induction-on-OO _ I
--  where
--   I : (β : Ordinal 𝓤)
--     → ((b : ⟨ β ⟩) (γ : Ordinal 𝓤) → 𝟙ₒ ⊲ α → α ^ₒ (β ↓ b) ⊴ α ^ₒ γ → (β ↓ b) ⊴ γ)
--     → (γ : Ordinal 𝓤) → 𝟙ₒ ⊲ α → α ^ₒ β ⊴ α ^ₒ γ → β ⊴ γ
--   I β IH γ (a₀ , e) l = to-⊴ β γ II
--    where
--     IV : (b : ⟨ β ⟩) → (β ↓ b) ⊴ {!!}
--     IV b = IH b {!!} (a₀ , e) {!!}
--     III : (b : ⟨ β ⟩) → α ^ₒ (β ↓ b) ⊲ α ^ₒ γ
--     III b = ⊲-⊴-gives-⊲ (α ^ₒ (β ↓ b)) (α ^ₒ β) (α ^ₒ γ) (exp-strictly-monotone α (β ↓ b) β (a₀ , e) (b , refl)) l
--     II : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
--     II b = {!!}
-- -}



-- \end{code}
