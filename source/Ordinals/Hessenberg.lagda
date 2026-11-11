TODO

\begin{code}

-- TODO: Get rid of lossy-unification?
{-# OPTIONS --safe --without-K --lossy-unification #-}

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


{-
⊕-is-associative : (α β γ : Ordinal 𝓤) → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
⊕-is-associative {𝓤} = {!!}
 where
  I : ((α , (β , γ)) : Ordinal 𝓤 × Ordinal 𝓤 × Ordinal 𝓤)
    → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
  I = Transfinite-induction (OO 𝓤 ×ₒ (OO 𝓤 ×ₒ OO 𝓤)) _ II
   where
    O³ = Ordinal 𝓤 × Ordinal 𝓤 × Ordinal 𝓤
    II : (x@(α , (β , γ)) : O³)
       → ((y@(γ , (δ , ε)) : O³)
                           → y ≺⟨ OO 𝓤 ×ₒ (OO 𝓤 ×ₒ OO 𝓤) ⟩ x
                           → (γ ⊕ δ) ⊕ ε ＝ γ ⊕ (δ ⊕ ε))
       → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
    II (α , β , γ) IH =
     (α ⊕ β) ⊕ γ ＝⟨ ⊕-behaviour (α ⊕ β) γ ⟩
     sup⁺ (cases (λ x → ((α ⊕ β) ↓ x) ⊕ γ) (λ c → (α ⊕ β) ⊕ (γ ↓ c))) ＝⟨ {!!} ⟩
     {!!} ＝⟨ {!!} ⟩
     {!!} ＝⟨ {!!} ⟩
     sup⁺ (cases (λ a → ((α ↓ a) ⊕ β) ⊕ γ) (λ y → α ⊕ ((β ⊕ γ) ↓ y)))  ＝⟨ ap (λ - → sup⁺ (cases -  (λ y → α ⊕ ((β ⊕ γ) ↓ y)))) (dfunext fe' (λ a → IH (α ↓ a , β , γ) (inr (refl , (a , refl))))) ⟩
     sup⁺ (cases (λ a → (α ↓ a) ⊕ (β ⊕ γ)) (λ y → α ⊕ ((β ⊕ γ) ↓ y))) ＝⟨ (⊕-behaviour α (β ⊕ γ)) ⁻¹ ⟩
     (α ⊕ (β ⊕ γ)) ∎

-}

\end{code}
