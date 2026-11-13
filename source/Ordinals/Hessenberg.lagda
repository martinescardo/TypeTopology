TODO

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Hessenberg
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Plus-Properties
open import MLTT.Spartan

open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open suprema pt sr
open PropositionalTruncation pt

-- TODO: Upstream
⊲-gives-successor-⊴ : (α β : Ordinal 𝓤) → α ⊲ β → α +ₒ 𝟙ₒ ⊴ β
⊲-gives-successor-⊴ α β (b , refl) =
 upper-bound-of-successors-of-initial-segments β b

successor-⊴-gives-⊲ : (α β : Ordinal 𝓤) → α +ₒ 𝟙ₒ ⊴ β → α ⊲ β
successor-⊴-gives-⊲ α β 𝕗@(f , f-sim) =
 b , (α                 ＝⟨ (successor-lemma-right α) ⁻¹ ⟩
      (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝⟨ simulations-preserve-↓ (α +ₒ 𝟙ₒ) β 𝕗 (inr ⋆) ⟩
      β ↓ b             ∎)
 where
  b : ⟨ β ⟩
  b = f (inr ⋆)

-- TODO: Upstream
double-transfinite-induction-on-OO
 : (P : Ordinal 𝓤 → Ordinal 𝓤 → 𝓥 ̇ )
 → ((α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → P (α ↓ a) β)
                      → ((b : ⟨ β ⟩) → P α (β ↓ b))
                      → P α β)
 → (α β : Ordinal 𝓤) → P α β
double-transfinite-induction-on-OO {𝓤} {𝓥} P h = λ α β → I (α , β)
 where
  I : ((α , β) : Ordinal 𝓤 × Ordinal 𝓤) → P α β
  I = Transfinite-induction (OO 𝓤 ×ₒ OO 𝓤) (uncurry P)
       (λ (α , β) h'
         → h α β
            (λ a → h' ((α ↓ a) , β) (inr (refl , a , refl)))
            (λ b → h' (α , (β ↓ b)) (inl (b , refl))))

double-transfinite-recursion-on-OO
 : {X : 𝓥 ̇ }
 → ((α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → X) → ((b : ⟨ β ⟩) → X) → X)
 → Ordinal 𝓤 → Ordinal 𝓤 → X
double-transfinite-recursion-on-OO = double-transfinite-induction-on-OO _

double-transfinite-recursion-on-OO-behaviour
 : {X : 𝓥 ̇ }
 → (r : (α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → X) → ((b : ⟨ β ⟩) → X) → X)
 → (α β : Ordinal 𝓤)
 → double-transfinite-recursion-on-OO r α β
   ＝ r α β (λ a → double-transfinite-recursion-on-OO r (α ↓ a) β)
            (λ b → double-transfinite-recursion-on-OO r α (β ↓ b))
double-transfinite-recursion-on-OO-behaviour {𝓥} {𝓤} {X} r = λ α β → I (α , β)
 where
  I : ((α , β) : Ordinal 𝓤 × Ordinal 𝓤)
    → double-transfinite-recursion-on-OO r α β ＝ r α β _ _
  I = Transfinite-induction-behaviour fe (OO 𝓤 ×ₒ OO 𝓤) (λ _ → X)
       (λ (α , β) h → r α β (λ a → h ((α ↓ a) , β) (inr (refl , (a , refl))))
                            (λ b → h (α , (β ↓ b)) (inl (b , refl))))

-- TODO: Upstream
module _
        {I : 𝓤 ̇ }
        (α : I → Ordinal 𝓤)
       where

 sup⁺ : Ordinal 𝓤
 sup⁺ = sup (λ i → α i +ₒ 𝟙ₒ)

 -- TODO. Make α implicit and i explicit?
 sup⁺-is-strict-upper-bound : {i : I} → α i ⊲ sup⁺
 sup⁺-is-strict-upper-bound {i} =
  ⊲-⊴-gives-⊲ (α i) (α i +ₒ 𝟙ₒ) sup⁺
   (successor-increasing (α i))
   (sup-is-upper-bound _ i)

 sup⁺-is-least-strict-upper-bound : (β : Ordinal 𝓤)
                                  → ((i : I) → α i ⊲ β) → sup⁺ ⊴ β
 sup⁺-is-least-strict-upper-bound β h =
  sup-is-lower-bound-of-upper-bounds (λ i → α i +ₒ 𝟙ₒ) β
   (λ i → ⊲-gives-successor-⊴ (α i) β (h i))

{-
private
 hessenberg-recursor
  : ((α , β) : Ordinal 𝓤 × Ordinal 𝓤)
  → (((γ , δ) : Ordinal 𝓤 × Ordinal 𝓤)
              → (γ , δ) ≺⟨ OO 𝓤 ×ₒ OO 𝓤 ⟩ (α , β) → Ordinal 𝓤)
  → Ordinal 𝓤
 hessenberg-recursor (α , β) r =
  sup⁺ (cases (λ a → r (α ↓ a , β) (inr (refl , a , refl)))
              (λ b → r (α , β ↓ b) (inl (b , refl))))
-}

abstract
 _⊕_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
 _⊕_ {𝓤} = double-transfinite-recursion-on-OO (λ α β r₁ r₂ → sup⁺ (cases r₁ r₂))

 ⊕-behaviour : (α β : Ordinal 𝓤)
             → α ⊕ β ＝ sup⁺ (cases (λ a → (α ↓ a) ⊕ β) (λ b → α ⊕ (β ↓ b)))
 ⊕-behaviour {𝓤} = double-transfinite-recursion-on-OO-behaviour
                    (λ α β r₁ r₂ → sup⁺ (cases r₁ r₂))

{-
 ∥∥-rec
  ∨-is-prop
  {!!}
  (initial-segment-of-sup-is-initial-segment-of-some-component {!λ y → cases r₁ r₂ y +ₒ 𝟙ₒ!} x)
   where

    I : (Σ y ꞉ (⟨ α ⟩ + ⟨ β ⟩) , Σ x' ꞉ ⟨ cases r₁ r₂ y +ₒ 𝟙ₒ ⟩ , {!!})
    {-
          , Σ x' ꞉ ⟨ (cases r₁ r₂ y) +ₒ 𝟙ₒ ⟩
            , (α ⊕ β) ↓ x ＝ ((cases r₁ r₂ y) +ₒ 𝟙ₒ) ↓ x') -}
      → (Σ a ꞉ ⟨ α ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ β)
        ∨ (Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ α ⊕ (β ↓ b))
    I = {!!}
-}

⊕-is-commutative : (α β : Ordinal 𝓤) → α ⊕ β ＝ β ⊕ α
⊕-is-commutative {𝓤} = double-transfinite-induction-on-OO _ I
 where
  I : (α β : Ordinal 𝓤)
    → ((a : ⟨ α ⟩) → ((α ↓ a) ⊕ β) ＝ (β ⊕ (α ↓ a)))
    → ((b : ⟨ β ⟩) → (α ⊕ (β ↓ b)) ＝ ((β ↓ b) ⊕ α))
    → (α ⊕ β) ＝ (β ⊕ α)
  I α β IH₁ IH₂ =
   α ⊕ β                                                ＝⟨ II  ⟩
   sup⁺ (cases (λ a → (α ↓ a) ⊕ β) (λ b → α ⊕ (β ↓ b))) ＝⟨ III ⟩
   sup⁺ (cases (λ a → β ⊕ (α ↓ a)) (λ b → (β ↓ b) ⊕ α)) ＝⟨ IV  ⟩
   sup⁺ (cases (λ b → (β ↓ b) ⊕ α) (λ a → β ⊕ (α ↓ a))) ＝⟨ V   ⟩
   β ⊕ α                                                ∎
    where
     f = cases (λ a → β ⊕ (α ↓ a)) (λ b → (β ↓ b) ⊕ α)
     g = cases (λ b → (β ↓ b) ⊕ α) (λ a → β ⊕ (α ↓ a))

     II  = ⊕-behaviour α β
     III = ap₂ (λ x y → sup⁺ (cases x y)) (dfunext fe' IH₁) (dfunext fe' IH₂)
     IV  = ⊴-antisym (sup⁺ f) (sup⁺ g)
            (sup⁺-is-least-strict-upper-bound f (sup⁺ g)
              (dep-cases (λ a → sup⁺-is-strict-upper-bound g {inr a})
                         (λ b → sup⁺-is-strict-upper-bound g {inl b})))
            (sup⁺-is-least-strict-upper-bound g (sup⁺ f)
              (dep-cases (λ b → sup⁺-is-strict-upper-bound f {inr b})
                         (λ a → sup⁺-is-strict-upper-bound f {inl a})))
     V   = (⊕-behaviour β α) ⁻¹

⊕-⊲-left : (α β : Ordinal 𝓤) {a : ⟨ α ⟩} → (α ↓ a) ⊕ β ⊲ α ⊕ β
⊕-⊲-left α β {a} = transport⁻¹ ((α ↓ a) ⊕ β ⊲_) (⊕-behaviour α β)
                    (sup⁺-is-strict-upper-bound _ {inl a})

⊕-⊲-right : (α β : Ordinal 𝓤) {b : ⟨ β ⟩} → α ⊕ (β ↓ b) ⊲ α ⊕ β
⊕-⊲-right α β {b} = transport⁻¹ (α ⊕ (β ↓ b) ⊲_) (⊕-behaviour α β)
                     (sup⁺-is-strict-upper-bound _ {inr b})

⊕-⊲-mixed : (α β : Ordinal 𝓤) {a : ⟨ α ⟩} {b : ⟨ β ⟩}
          → (α ↓ a) ⊕ (β ↓ b) ⊲ α ⊕ β
⊕-⊲-mixed α β {a} {b} =
 ⊲-is-transitive
  ((α ↓ a) ⊕ (β ↓ b))
  ((α ↓ a) ⊕ β)
  (α ⊕ β)
  (⊕-⊲-right (α ↓ a) β)
  (⊕-⊲-left α β)

⊕-is-order-preserving-left : (α β γ : Ordinal 𝓤) → α ⊲ β → α ⊕ γ ⊲ β ⊕ γ
⊕-is-order-preserving-left α β γ (b , refl) = ⊕-⊲-left β γ

⊕-is-order-preserving-right : (α β γ : Ordinal 𝓤) → β ⊲ γ → α ⊕ β ⊲ α ⊕ γ
⊕-is-order-preserving-right α β γ (c , refl) = ⊕-⊲-right α γ

⊕-is-order-preserving : (α α' β β' : Ordinal 𝓤) → α ⊲ α' → β ⊲ β' → α ⊕ β ⊲ α' ⊕ β'
⊕-is-order-preserving α α' β β' k l =
 ⊲-is-transitive (α ⊕ β) (α' ⊕ β) (α' ⊕ β')
  (⊕-is-order-preserving-left α α' β k)
  (⊕-is-order-preserving-right α' β β' l)

-- TODO: Refer to the above ⊲-left/right/mixed?
⊕-↓-characterization
 : (α β : Ordinal 𝓤) (x : ⟨ α ⊕ β ⟩)
 → ∥ (Σ a ꞉ ⟨ α ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ β)
      + (Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ α ⊕ (β ↓ b))
      + (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)) ∥
⊕-↓-characterization {𝓤} = double-transfinite-induction-on-OO _ I
 where
  P : (α β γ : Ordinal 𝓤) → 𝓤 ⁺ ̇
  P α β γ =
   (x : ⟨ γ ⟩) → ∥ (Σ a ꞉ ⟨ α ⟩ , γ ↓ x ＝ (α ↓ a) ⊕ β)
                    + (Σ b ꞉ ⟨ β ⟩ , γ ↓ x ＝ α ⊕ (β ↓ b))
                    + (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , γ ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)) ∥
  I : (α β : Ordinal 𝓤)
    → ((a : ⟨ α ⟩) → P (α ↓ a) β ((α ↓ a) ⊕ β))
    → ((b : ⟨ β ⟩) → P α (β ↓ b) (α ⊕ (β ↓ b)))
    → P α β (α ⊕ β)
  I α β IH₁ IH₂ = transport⁻¹ (P α β) (⊕-behaviour α β) II
   where
    r₁ : ⟨ α ⟩ → Ordinal 𝓤
    r₁ a = (α ↓ a) ⊕ β
    r₂ : ⟨ β ⟩ → Ordinal 𝓤
    r₂ b = α ⊕ (β ↓ b)
    σ = sup⁺ (cases r₁ r₂)

    II : P α β σ
    II s = ∥∥-rec ∨-is-prop III
             (initial-segment-of-sup-is-initial-segment-of-some-component _ s)
     where
      III : (Σ y ꞉ ⟨ α ⟩ + ⟨ β ⟩ , Σ x ꞉ ⟨ cases r₁ r₂ y +ₒ 𝟙ₒ ⟩ ,
              σ ↓ s ＝ cases r₁ r₂ y +ₒ 𝟙ₒ ↓ x)
          → ∥ (Σ a ꞉ ⟨ α ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ β)
               + (Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ α ⊕ (β ↓ b))
               + (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ (β ↓ b)) ∥
      III (inl a , inl x , e) = ∥∥-functor (+functor III₁ III₂) (IH₁ a x)
       where
        -- TODO. Avoid duplicating e ∙ (+ₒ-↓-left x) ⁻¹ ?
        III₁ : (Σ a' ꞉ ⟨ α ↓ a ⟩ , ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a ↓ a') ⊕ β))
             → Σ a ꞉ ⟨ α ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ β
        III₁ ((a' , l) , e') = a' ,
         (σ ↓ s                         ＝⟨ e ⟩
          (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          ((α ↓ a) ⊕ β) ↓ x             ＝⟨ e' ⟩
          ((α ↓ a ↓ (a' , l)) ⊕ β)      ＝⟨ ap (_⊕ β) (iterated-↓ α a a' l) ⟩
          ((α ↓ a') ⊕ β)                ∎)

        III₂ : ((Σ b ꞉ ⟨ β ⟩ , ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a) ⊕ (β ↓ b)))
                + (Σ a' ꞉ ⟨ α ↓ a ⟩ , Σ b ꞉ ⟨ β ⟩ ,
                    ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a ↓ a') ⊕ (β ↓ b))))
             → (Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ α ⊕ (β ↓ b))
               + (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ ((α ↓ a) ⊕ (β ↓ b)))
        III₂ (inl (b , e')) = inr (a , b ,
         (σ ↓ s                         ＝⟨ e ⟩
          (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          ((α ↓ a) ⊕ β) ↓ x             ＝⟨ e' ⟩
          ((α ↓ a) ⊕ (β ↓ b))           ∎))

        III₂ (inr ((a' , l) , b , e')) = inr (a' , b ,
         (σ ↓ s                          ＝⟨ e ⟩
          (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inl x  ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          ((α ↓ a) ⊕ β) ↓ x              ＝⟨ e' ⟩
          ((α ↓ a ↓ (a' , l)) ⊕ (β ↓ b)) ＝⟨ ap (_⊕ (β ↓ b))
                                                (iterated-↓ α a a' l) ⟩
          ((α ↓ a') ⊕ (β ↓ b))           ∎))

      III (inl a , inr u , e) = ∣ inl (a , e') ∣
       where
        e' = σ ↓ s                         ＝⟨ e ⟩
             (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             ((α ↓ a) ⊕ β) +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap (((α ↓ a) ⊕ β) +ₒ_) 𝟙ₒ-↓ ⟩
             ((α ↓ a) ⊕ β) +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral ((α ↓ a) ⊕ β) ⟩
             (α ↓ a) ⊕ β                   ∎

      -- These are symmetric to the above

      III (inr b , inl x , e) = ∥∥-functor III' (IH₂ b x)
       where
        -- TODO. Avoid duplicating e ∙ (+ₒ-↓-left x) ⁻¹ ?
        III' : ((Σ a ꞉ ⟨ α ⟩ , (α ⊕ (β ↓ b)) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b))
                + (Σ b' ꞉ ⟨ β ↓ b ⟩ , (α ⊕ (β ↓ b)) ↓ x ＝ α ⊕ (β ↓ b ↓ b'))
                + (Σ a ꞉ ⟨ α ⟩ , Σ b' ꞉ ⟨ β ↓ b ⟩ ,
                    (α ⊕ (β ↓ b)) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b ↓ b')))
             → (Σ a ꞉ ⟨ α ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ β)
               + (Σ b' ꞉ ⟨ β ⟩ , σ ↓ s ＝ α ⊕ (β ↓ b'))
               + (Σ a ꞉ ⟨ α ⟩ , Σ b' ꞉ ⟨ β ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ (β ↓ b'))

        III' (inl (a , e')) = inr (inr (a , b ,
         (σ ↓ s                         ＝⟨ e ⟩
          ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          (α ⊕ (β ↓ b)) ↓ x             ＝⟨ e' ⟩
          ((α ↓ a) ⊕ (β ↓ b))           ∎)))

        III' (inr (inl ((b' , l) , e'))) = inr (inl (b' ,
         (σ ↓ s                         ＝⟨ e ⟩
          ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          (α ⊕ (β ↓ b)) ↓ x             ＝⟨ e' ⟩
          (α ⊕ (β ↓ b ↓ (b' , l)))      ＝⟨ ap (α ⊕_) (iterated-↓ β b b' l) ⟩
          (α ⊕ (β ↓ b'))                ∎)))

        III' (inr (inr (a , (b' , l) , e'))) = inr (inr (a , b' ,
         (σ ↓ s                          ＝⟨ e ⟩
          ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inl x  ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
          (α ⊕ (β ↓ b)) ↓ x              ＝⟨ e' ⟩
          ((α ↓ a) ⊕ (β ↓ b ↓ (b' , l))) ＝⟨ ap ((α ↓ a) ⊕_)
                                                (iterated-↓ β b b' l) ⟩
          ((α ↓ a) ⊕ (β ↓ b'))           ∎)))

      III (inr b , inr u , e) = ∣ inr (inl (b , e')) ∣
       where
        e' = σ ↓ s                         ＝⟨ e ⟩
             ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             (α ⊕ (β ↓ b)) +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap ((α ⊕ (β ↓ b)) +ₒ_) 𝟙ₒ-↓ ⟩
             (α ⊕ (β ↓ b)) +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral (α ⊕ (β ↓ b)) ⟩
             (α ⊕ (β ↓ b))                 ∎

⊕-induction : (α β : Ordinal 𝓤) (P : Ordinal 𝓤 → 𝓥 ̇ )
            → ((γ : Ordinal 𝓤) → is-prop (P γ))
            → ((a : ⟨ α ⟩) → P ((α ↓ a) ⊕ β))
            → ((b : ⟨ β ⟩) → P (α ⊕ (β ↓ b)))
            → ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → P ((α ↓ a) ⊕ (β ↓ b)))
            → (x : ⟨ α ⊕ β ⟩) → P ((α ⊕ β) ↓ x)
⊕-induction α β P P-pv f g h x =
 ∥∥-rec (P-pv ((α ⊕ β) ↓ x)) I (⊕-↓-characterization α β x)
  where
   I : ((Σ a ꞉ ⟨ α ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ β)
        + (Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ α ⊕ (β ↓ b))
        + (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)))
     → P ((α ⊕ β) ↓ x)
   I (inl (a , e)) = transport⁻¹ P e (f a)
   I (inr (inl (b , e))) = transport⁻¹ P e (g b)
   I (inr (inr (a , b , e))) = transport⁻¹ P e (h a b)

-- TODO. Clean up
-- TODO. Explain that the IH is not too strong enough to prove the one-sided
-- version (α ⊕ β) ⊕ γ ⊴ α ⊕ (β ⊕ γ) first, which, using commutativity, would be
-- enough to derive the equality.
⊕-is-associative : (α β γ : Ordinal 𝓤)
                 → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
⊕-is-associative {𝓤} = λ α β γ → Transfinite-induction (OO³) _ I (α , β , γ)
 where
  OO³ = OO 𝓤 ×ₒ (OO 𝓤 ×ₒ OO 𝓤)

  I : (s@(α , β , γ) : ⟨ OO³ ⟩)
    → ((t@(γ , δ , ε) : ⟨ OO³ ⟩)
                      → t ≺⟨ OO³ ⟩ s
                      → (γ ⊕ δ) ⊕ ε ＝ γ ⊕ (δ ⊕ ε))
    → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
  I (α , β , γ) IH = ⊴-antisym ((α ⊕ β) ⊕ γ) (α ⊕ (β ⊕ γ))
                               (to-⊴ ((α ⊕ β) ⊕ γ) (α ⊕ (β ⊕ γ)) II)
                               (to-⊴ (α ⊕ (β ⊕ γ)) ((α ⊕ β) ⊕ γ) II')
   where
    II' : (y : ⟨ α ⊕ (β ⊕ γ) ⟩) → (α ⊕ (β ⊕ γ)) ↓ y ⊲ (α ⊕ β) ⊕ γ
    II' = ⊕-induction α (β ⊕ γ) (_⊲ (α ⊕ β) ⊕ γ) (λ _ → ⊲-is-prop-valued _ _) IIᵃ (III α (inr refl)) λ a x → III (α ↓ a) (inl (a , refl)) x
     where
      IIᵃ : (a : ⟨ α ⟩) → (α ↓ a) ⊕ (β ⊕ γ) ⊲ (α ⊕ β) ⊕ γ
      IIᵃ a = transport (_⊲ (α ⊕ β) ⊕ γ) (IH (α ↓ a , β , γ) (inr (refl , (a , refl)))) (⊕-is-order-preserving-left ((α ↓ a) ⊕ β) (α ⊕ β) γ (⊕-is-order-preserving-left (α ↓ a) α β (a , refl)))

      III : (δ : Ordinal 𝓤) → ((δ ⊲ α) + (δ ＝ α))
          → (x : ⟨ β ⊕ γ ⟩) → δ ⊕ ((β ⊕ γ) ↓ x) ⊲ (α ⊕ β) ⊕ γ
      III δ s = ⊕-induction β γ (λ - → δ ⊕ - ⊲ (α ⊕ β) ⊕ γ) (λ _ → ⊲-is-prop-valued _ _) IIIᵇ IIIᶜ IIIᵇᶜ
       where
        IIIᵇ : (b : ⟨ β ⟩) → δ ⊕ ((β ↓ b) ⊕ γ) ⊲ (α ⊕ β) ⊕ γ
        IIIᵇ b = transport (_⊲ (α ⊕ β) ⊕ γ) (IH (δ , β ↓ b , γ) (inl (inr (refl , (b , refl))))) (h s)
         where
          h : ((δ ⊲ α) + (δ ＝ α)) → (δ ⊕ (β ↓ b)) ⊕ γ ⊲ (α ⊕ β) ⊕ γ
          h (inl k) = ⊕-is-order-preserving-left (δ ⊕ (β ↓ b)) (α ⊕ β) γ (⊕-is-order-preserving δ α (β ↓ b) β k (b , refl))
          h (inr refl) = ⊕-is-order-preserving-left (α ⊕ (β ↓ b)) (α ⊕ β) γ (⊕-is-order-preserving-right α (β ↓ b) β (b , refl))
        IIIᶜ : (c : ⟨ γ ⟩) → δ ⊕ (β ⊕ (γ ↓ c)) ⊲ (α ⊕ β) ⊕ γ
        IIIᶜ c = transport (_⊲ (α ⊕ β) ⊕ γ) (IH (δ , β , γ ↓ c) (inl (inl (c , refl)))) (h s)
         where
         h : ((δ ⊲ α) + (δ ＝ α)) → (δ ⊕ β) ⊕ (γ ↓ c) ⊲ (α ⊕ β) ⊕ γ
         h (inl k) = ⊕-is-order-preserving (δ ⊕ β) (α ⊕ β) (γ ↓ c) γ (⊕-is-order-preserving-left δ α β k) (c , refl)
         h (inr refl) = ⊕-is-order-preserving-right (α ⊕ β) (γ ↓ c) γ (c , refl)
        IIIᵇᶜ : (b : ⟨ β ⟩) (c : ⟨ γ ⟩) → δ ⊕ ((β ↓ b) ⊕ (γ ↓ c)) ⊲ (α ⊕ β) ⊕ γ
        IIIᵇᶜ b c = transport (_⊲ (α ⊕ β) ⊕ γ) (IH (δ , β ↓ b , γ ↓ c) (inl (inl (c , refl)))) (h s)
         where
          h : ((δ ⊲ α) + (δ ＝ α)) → (δ ⊕ (β ↓ b)) ⊕ (γ ↓ c) ⊲ (α ⊕ β) ⊕ γ
          h (inl k) = ⊕-is-order-preserving (δ ⊕ (β ↓ b)) (α ⊕ β) (γ ↓ c) γ (⊕-is-order-preserving δ α (β ↓ b) β k (b , refl)) (c , refl)
          h (inr refl) = ⊕-is-order-preserving (α ⊕ (β ↓ b)) (α ⊕ β) (γ ↓ c) γ (⊕-is-order-preserving-right α (β ↓ b) β (b , refl)) (c , refl)

    II : (y : ⟨ (α ⊕ β) ⊕ γ ⟩) → ((α ⊕ β) ⊕ γ) ↓ y ⊲ α ⊕ (β ⊕ γ)
    II = ⊕-induction (α ⊕ β) γ (_⊲ α ⊕ (β ⊕ γ)) (λ _ → ⊲-is-prop-valued _ _) (III γ (inr refl)) III₂ (λ x c → III (γ ↓ c) (inl (c , refl)) x)
     where
      III₂ : (c : ⟨ γ ⟩) → (α ⊕ β) ⊕ (γ ↓ c) ⊲ α ⊕ (β ⊕ γ)
      III₂ c = transport⁻¹ (_⊲ α ⊕ (β ⊕ γ)) (IH (α , β , γ ↓ c) (inl (inl (c , refl)))) (⊕-is-order-preserving-right α (β ⊕ (γ ↓ c)) (β ⊕ γ) (⊕-is-order-preserving-right β (γ ↓ c) γ (c , refl)))

      III : (δ : Ordinal 𝓤) → ((δ ⊲ γ) + (δ ＝ γ))
          → (x : ⟨ α ⊕ β ⟩) → ((α ⊕ β) ↓ x) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
      III δ s = ⊕-induction α β (λ - → - ⊕ δ ⊲ α ⊕ (β ⊕ γ)) (λ _ → ⊲-is-prop-valued _ _) IIIᵃ IIIᵇ IIIᵃᵇ
       where
        l : (b : ⟨ β ⟩) → (β ↓ b) ⊕ δ ⊲ β ⊕ γ
        l b = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (β ↓ b) ⊕ δ ⊲ β ⊕ γ
          h (inl k) = ⊕-is-order-preserving (β ↓ b) β δ γ (b , refl) k
          h (inr refl) = ⊕-is-order-preserving-left (β ↓ b) β γ (b , refl)
        l' : (a : ⟨ α ⟩) → (α ↓ a) ⊕ (β ⊕ δ) ⊲ α ⊕ (β ⊕ γ)
        l' a = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (α ↓ a) ⊕ (β ⊕ δ) ⊲ α ⊕ (β ⊕ γ)
          h (inl k) = ⊕-is-order-preserving (α ↓ a) α (β ⊕ δ) (β ⊕ γ) (a , refl) (⊕-is-order-preserving-right β δ γ k)
          h (inr refl) = ⊕-is-order-preserving-left (α ↓ a) α (β ⊕ γ) (a , refl)

        foo : (a : ⟨ α ⟩) → (α ↓ a , β , δ) ≺⟨ OO³ ⟩ (α , β , γ)
        foo a = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (α ↓ a , β , δ) ≺⟨ OO³ ⟩ (α , β , γ)
          h (inl k) = inl (inl k)
          h (inr refl) = inr (refl , (a , refl))

        bar : (b : ⟨ β ⟩) (α' : Ordinal 𝓤)
            → (α' , β ↓ b , δ) ≺⟨ OO³ ⟩ (α , β , γ)
        bar b α' = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (α' , β ↓ b , δ) ≺⟨ OO³ ⟩ (α , β , γ)
          h (inl k) = inl (inl k)
          h (inr refl) = inl (inr (refl , (b , refl)))

        IIIᵃ : (a : ⟨ α ⟩) → ((α ↓ a) ⊕ β) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵃ a = transport⁻¹ (_⊲ α ⊕ (β ⊕ γ)) (IH (α ↓ a , β , δ) (foo a)) (l' a)
        IIIᵇ : (b : ⟨ β ⟩) → (α ⊕ (β ↓ b)) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵇ b = transport⁻¹ (_⊲ (α ⊕ (β ⊕ γ))) (IH (α , (β ↓ b) , δ) (bar b α)) (⊕-is-order-preserving-right α ((β ↓ b) ⊕ δ) (β ⊕ γ) (l b))
        IIIᵃᵇ : (a : ⟨ α ⟩) (b : ⟨ β ⟩) → ((α ↓ a) ⊕ (β ↓ b)) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵃᵇ a b = transport⁻¹ (_⊲ (α ⊕ (β ⊕ γ))) (IH (α ↓ a , β ↓ b , δ) (bar b (α ↓ a))) (⊕-is-order-preserving (α ↓ a) α ((β ↓ b) ⊕ δ) (β ⊕ γ) (a , refl) (l b))

\end{code}

\begin{code}

𝟘ₒ-is-right-neutral-⊕ : (α : Ordinal 𝓤) → α ⊕ 𝟘ₒ ＝ α
𝟘ₒ-is-right-neutral-⊕ {𝓤} = transfinite-induction-on-OO _ I
 where
  I : (α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → (α ↓ a) ⊕ 𝟘ₒ ＝ α ↓ a) → α ⊕ 𝟘ₒ ＝ α
  I α IH = ⊴-antisym (α ⊕ 𝟘ₒ) α (to-⊴ (α ⊕ 𝟘ₒ) α II) (to-⊴ α (α ⊕ 𝟘ₒ) III)
   where
    II : (x : ⟨ α ⊕ 𝟘ₒ ⟩) → (α ⊕ 𝟘ₒ) ↓ x ⊲ α
    II = ⊕-induction α 𝟘ₒ (_⊲ α) (λ _ → ⊲-is-prop-valued _ α)
          (λ a → (a , IH a))
          𝟘-induction
          (λ a → 𝟘-induction)
    III : (a : ⟨ α ⟩) → α ↓ a ⊲ α ⊕ 𝟘ₒ
    III a = transport (_⊲ α ⊕ 𝟘ₒ) (IH a) (⊕-⊲-left α 𝟘ₒ)

𝟘ₒ-is-left-neutral-⊕ : (α : Ordinal 𝓤) → 𝟘ₒ ⊕ α ＝ α
𝟘ₒ-is-left-neutral-⊕ α = ⊕-is-commutative 𝟘ₒ α ∙ 𝟘ₒ-is-right-neutral-⊕ α

⊕𝟙ₒ-is-strictly-increasing : (α : Ordinal 𝓤) → α ⊲ α ⊕ 𝟙ₒ
⊕𝟙ₒ-is-strictly-increasing α = transport (_⊲ α ⊕ 𝟙ₒ) (𝟘ₒ-is-right-neutral-⊕ α) I
 where
  I : α ⊕ 𝟘ₒ ⊲ α ⊕ 𝟙ₒ
  I = ⊕-is-order-preserving-right α 𝟘ₒ 𝟙ₒ (⋆ , (𝟙ₒ-↓ ⁻¹))

⊕-is-strictly-increasing : (α β : Ordinal 𝓤) → 𝟙ₒ ⊲ β → α ⊲ α ⊕ β
⊕-is-strictly-increasing α β l =
 ⊲-is-transitive α (α ⊕ 𝟙ₒ) (α ⊕ β)
  (⊕𝟙ₒ-is-strictly-increasing α)
  (⊕-is-order-preserving-right α 𝟙ₒ β l)

-- TODO. Clean up and rename
test : (P : 𝓤 ̇ ) (i : is-prop P)
     → let Pₒ = prop-ordinal P i in
       Pₒ ⊕ 𝟙ₒ ＝ Pₒ +ₒ 𝟙ₒ
test P i = transport⁻¹ (_＝ Pₒ +ₒ 𝟙ₒ) (⊕-behaviour Pₒ 𝟙ₒ ∙ II) I
 where
  Pₒ = prop-ordinal P i
  σ = sup (λ (b : P + 𝟙) → cases (λ p → (Pₒ ↓ p) ⊕ 𝟙ₒ) (λ u → Pₒ ⊕ (𝟙ₒ ↓ u)) b +ₒ 𝟙ₒ)
  τ = sup (λ (b : P + 𝟙) → cases (λ p → 𝟙ₒ) (λ u → Pₒ) b +ₒ 𝟙ₒ)
  II : σ ＝ τ
  II = sup-pointwise-equal _ _ h
   where
    h : (λ b → cases (λ p → (Pₒ ↓ p) ⊕ 𝟙ₒ) (λ u → Pₒ ⊕ (𝟙ₒ ↓ u)) b +ₒ 𝟙ₒ)
        ∼ (λ b → cases (λ p → 𝟙ₒ) (λ u → Pₒ) b +ₒ 𝟙ₒ)
    h (inl p) = ap (λ - → (- ⊕ 𝟙ₒ) +ₒ 𝟙ₒ) (prop-ordinal-↓ i p)
                ∙ ap (_+ₒ 𝟙ₒ) (𝟘ₒ-is-left-neutral-⊕ 𝟙ₒ)
    h (inr u) = ap (λ - → (Pₒ ⊕ -) +ₒ 𝟙ₒ) 𝟙ₒ-↓
                ∙ ap (_+ₒ 𝟙ₒ) (𝟘ₒ-is-right-neutral-⊕ Pₒ)
  I : τ ＝ Pₒ +ₒ 𝟙ₒ
  I = ⊴-antisym τ (Pₒ +ₒ 𝟙ₒ) (sup-is-lower-bound-of-upper-bounds _ (Pₒ +ₒ 𝟙ₒ) (dep-cases foo bar)) (sup-is-upper-bound _ (inr ⋆))
   where
    foo : (p : P) → 𝟙ₒ +ₒ 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ
    foo p = transport⁻¹ (λ - → 𝟙ₒ +ₒ 𝟙ₒ ⊴ - +ₒ 𝟙ₒ) (holds-gives-equal-𝟙ₒ i p) (⊴-refl 𝟚ₒ)
    bar : (u : 𝟙) → Pₒ +ₒ 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ
    bar _ = ⊴-refl (Pₒ +ₒ 𝟙ₒ)

⊕-monotone-gives-EM'
 : ((α β : Ordinal 𝓤) → α ⊴ β → α ⊕ 𝟙ₒ ⊴ β ⊕ 𝟙ₒ)
 → EM 𝓤
⊕-monotone-gives-EM' h P i = succ-of-prop-taboo P i I
 where
  Pₒ = prop-ordinal P i
  I : Pₒ +ₒ 𝟙ₒ ⊴ 𝟙ₒ +ₒ 𝟙ₒ
  I = transport₂ _⊴_
       (test P i)
       (test 𝟙 𝟙-is-prop)
       (h Pₒ 𝟙ₒ (prop-ordinal-⊴-𝟙ₒ i))

⊕-monotone-gives-EM
 : ((α β γ : Ordinal 𝓤) → α ⊴ β → α ⊕ γ ⊴ β ⊕ γ)
 → EM 𝓤
⊕-monotone-gives-EM h = ⊕-monotone-gives-EM' (λ α β → h α β 𝟙ₒ)

⊕-inflationary-gives-EM : ((α β : Ordinal 𝓤) → α ⊴ α ⊕ β) → EM 𝓤
⊕-inflationary-gives-EM h P i = II (h 𝟙ₒ Pₒ)
 where
  Pₒ = prop-ordinal P i

  I : 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ → P + ¬ P
  I 𝕗@(f , f-sim) = I' (f ⋆) (simulations-preserve-↓ 𝟙ₒ (Pₒ +ₒ 𝟙ₒ) 𝕗 ⋆)
   where
    I' : (y : P + 𝟙) → 𝟙ₒ ↓ ⋆ ＝ (Pₒ +ₒ 𝟙ₒ) ↓ y → P + ¬ P
    I' (inl p) e = inl p
    I' (inr u) e = inr (λ p → 𝟘ₒ-is-not-𝟙ₒ (e' p))
     where
      e' : (p : P) → 𝟘ₒ ＝ 𝟙ₒ
      e' p = 𝟘ₒ                 ＝⟨ 𝟙ₒ-↓ ⁻¹ ⟩
             𝟙ₒ ↓ ⋆             ＝⟨ e ⟩
             (Pₒ +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             Pₒ +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap (Pₒ +ₒ_) 𝟙ₒ-↓ ⟩
             Pₒ +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral Pₒ ⟩
             Pₒ                 ＝⟨ holds-gives-equal-𝟙ₒ i p ⟩
             𝟙ₒ                 ∎

  II : 𝟙ₒ ⊴ 𝟙ₒ ⊕ Pₒ → P + ¬ P
  II l = I (transport (𝟙ₒ ⊴_) e l)
   where
    e = 𝟙ₒ ⊕ Pₒ  ＝⟨ ⊕-is-commutative 𝟙ₒ Pₒ ⟩
        Pₒ ⊕ 𝟙ₒ  ＝⟨ test P i ⟩
        Pₒ +ₒ 𝟙ₒ ∎

\end{code}