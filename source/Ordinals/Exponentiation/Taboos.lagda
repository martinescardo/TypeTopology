Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
December 2024 (with results potentially going back to November 2023)

Taboos involving ordinal exponentation.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Taboos
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.ClassicalLogic

open suprema pt sr

\end{code}

\begin{code}

×ₒ-weakly-monotone-in-both-arguments-implies-EM :
   ((α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β)
 → EM 𝓤
×ₒ-weakly-monotone-in-both-arguments-implies-EM {𝓤} assumption P P-is-prop =
 IV (f x) refl
  where
   α β Pₒ : Ordinal 𝓤
   α = [ 2 ]ₒ
   Pₒ = prop-ordinal P P-is-prop
   β = [ 3 ]ₒ +ₒ Pₒ

   I : α ⊲ β
   I = inl (inr ⋆) , ((successor-lemma-right α) ⁻¹ ∙ +ₒ-↓-left (inr ⋆))

   α-ineq : 𝟙ₒ ⊴ α
   α-ineq = ⊲-gives-⊴ 𝟙ₒ α (successor-increasing 𝟙ₒ)

   II : α ×ₒ α ⊴ β ×ₒ β
   II = assumption α β α-ineq I

   x : ⟨ α ×ₒ α ⟩
   x = (inr ⋆ , inr ⋆)

   f : ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
   f = [ α ×ₒ α , β ×ₒ β ]⟨ II ⟩

   pattern ⊥β = inl (inl (inl ⋆))
   pattern ₀α = (inl ⋆ , inl ⋆)
   pattern ₁α = (inr ⋆ , inl ⋆)
   pattern ₂α = (inl ⋆ , inr ⋆)
   pattern ₃α = (inr ⋆ , inr ⋆)

   f' : P → ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
   f' p ₀α = (⊥β , ⊥β)
   f' p ₁α = (inl (inl (inr ⋆)) , ⊥β)
   f' p ₂α = (inl (inr ⋆) , ⊥β)
   f' p ₃α = (inr p , ⊥β)

   f'-simulation : (p : P) → is-simulation (α ×ₒ α) (β ×ₒ β) (f' p)
   f'-simulation p = f'-initial-seg , f'-order-pres
    where
     f'-initial-seg : is-initial-segment (α ×ₒ α) (β ×ₒ β) (f' p)
     f'-initial-seg ₁α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inr (refl , l) , refl
     f'-initial-seg ₂α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inl ⋆ , refl
     f'-initial-seg ₂α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inr ⋆) , .⊥β)       (inr (refl , l))
      = ₂α , inr (refl , l) , refl
     f'-initial-seg ₀α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = 𝟘-elim l
     f'-initial-seg ₀α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = 𝟘-elim l
     f'-initial-seg ₀α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₀α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l

     f'-order-pres : is-order-preserving (α ×ₒ α) (β ×ₒ β) (f' p)
     f'-order-pres ₀α ₂α (inl l) = inr (refl , l)
     f'-order-pres ₀α ₃α (inl l) = inr (refl , l)
     f'-order-pres ₁α ₂α (inl l) = inr (refl , l)
     f'-order-pres ₁α ₃α (inl l) = inr (refl , l)
     f'-order-pres (_ , inr ⋆) (_ , inl ⋆) (inl l) = 𝟘-elim l
     f'-order-pres (_ , inr ⋆) (_ , inr ⋆) (inl l) = 𝟘-elim l
     f'-order-pres ₀α (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
     f'-order-pres ₂α (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
     f'-order-pres (inr ⋆ , x') (inl ⋆ , x') (inr (refl , l)) = 𝟘-elim l
     f'-order-pres (inr ⋆ , x') (inr ⋆ , x') (inr (refl , l)) = 𝟘-elim l

   III : (p : P) → f ∼ f' p
   III p = at-most-one-simulation (α ×ₒ α) (β ×ₒ β)
            f (f' p)
            [ α ×ₒ α , β ×ₒ β ]⟨ II ⟩-is-simulation
            (f'-simulation p)

   IV : (y : ⟨ β ×ₒ β ⟩) → f x ＝ y → P + ¬ P
   IV (inl y , y') r = inr (λ p → +disjoint (ap pr₁ (V p)))
    where
     V : (p : P) → (inl y , y') ＝ (inr p , ⊥β)
     V p = (inl y , y') ＝⟨ r ⁻¹ ⟩
             f x          ＝⟨ III p x ⟩
             (inr p , ⊥β) ∎
   IV (inr p , y') r = inl p

\end{code}

\begin{code}

^ₒ-weakly-monotone-in-base-implies-EM :
   ((α β γ : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → (α ^ₒ γ ⊴ β ^ₒ γ))
 → EM 𝓤
^ₒ-weakly-monotone-in-base-implies-EM {𝓤} assumption =
 ×ₒ-weakly-monotone-in-both-arguments-implies-EM I
  where
   I : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β
   I α β l s = transport₂ _⊴_ II III (assumption α β 𝟚ₒ l s)
    where
     II : α ^ₒ 𝟚ₒ ＝ α ×ₒ α
     II = ^ₒ-𝟚ₒ-is-×ₒ α l
     III : β ^ₒ 𝟚ₒ ＝ β ×ₒ β
     III = ^ₒ-𝟚ₒ-is-×ₒ β (⊴-trans 𝟙ₒ α β l (⊲-gives-⊴ α β s))

^ₒ-monotone-in-base-implies-EM :
   ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ))
 → EM 𝓤
^ₒ-monotone-in-base-implies-EM m =
 ^ₒ-weakly-monotone-in-base-implies-EM
  (λ α β γ l i → m α β γ l (⊲-gives-⊴ α β i))

\end{code}

\begin{code}

EM-implies-exp-monotone-in-base : EM 𝓤
 → (α β γ : Ordinal 𝓤) → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ)
EM-implies-exp-monotone-in-base {𝓤} em α β γ l =
 transfinite-induction-on-OO _ I γ
 where
  I : (γ : Ordinal 𝓤)
    → ((c : ⟨ γ ⟩) → (α ^ₒ (γ ↓ c) ⊴ β ^ₒ (γ ↓ c)))
    → (α ^ₒ γ ⊴ β ^ₒ γ)
  I γ IH = transport₂⁻¹ _⊴_ (^ₒ-behaviour α γ) (^ₒ-behaviour β γ)
            (sup-monotone
             (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α))
             (cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β))
             κ)
   where
    κ : (i : 𝟙 + ⟨ γ ⟩)
      → cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α) i
      ⊴ cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β) i
    κ (inl ⋆) = ⊴-refl 𝟙ₒ
    κ (inr c) = EM-implies-induced-⊴-on-×ₒ em (α ^ₒ (γ ↓ c)) α
                                              (β ^ₒ (γ ↓ c)) β
                                              (IH c) l

\end{code}

The following is not used at the moment, but may come in useful in the future
when aiming to derive a constructive taboo.

\begin{code}

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