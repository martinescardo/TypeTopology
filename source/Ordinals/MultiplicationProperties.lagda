Fredrik Nordvall Forsberg, 13 November 2023.
In collaboration with Tom de Jong, Nicolai Kraus and Chuangjie Xu.

Minor updates 9 September 2024.

We prove several properties of ordinal multiplication, including that it
preserves suprema of ordinals and that it enjoys a left-cancellation property.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.MultiplicationProperties
       (ua : Univalence)
       where

open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan
open import MLTT.Sigma
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.AdditionProperties ua

×ₒ-𝟘ₒ-right : (α : Ordinal 𝓤) → α ×ₒ 𝟘ₒ {𝓥} ＝ 𝟘ₒ
×ₒ-𝟘ₒ-right α = ⊴-antisym _ _
                 (to-⊴ (α ×ₒ 𝟘ₒ) 𝟘ₒ (λ (a , b) → 𝟘-elim b))
                 (𝟘ₒ-least-⊴ (α ×ₒ 𝟘ₒ))

×ₒ-𝟘ₒ-left : (α : Ordinal 𝓤) → 𝟘ₒ {𝓥} ×ₒ α ＝ 𝟘ₒ
×ₒ-𝟘ₒ-left α = ⊴-antisym _ _
                (to-⊴ (𝟘ₒ ×ₒ α) 𝟘ₒ (λ (b , a) → 𝟘-elim b))
                (𝟘ₒ-least-⊴ (𝟘ₒ ×ₒ α))

𝟙ₒ-left-neutral-×ₒ : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ×ₒ α ＝ α
𝟙ₒ-left-neutral-×ₒ {𝓤} α = eqtoidₒ (ua _) fe' _ _
                            (f , f-order-preserving ,
                             f-is-equiv , g-order-preserving)
 where
  f : 𝟙 × ⟨ α ⟩ → ⟨ α ⟩
  f = pr₂

  g : ⟨ α ⟩ → 𝟙 × ⟨ α ⟩
  g = ( ⋆ ,_)

  f-order-preserving : is-order-preserving (𝟙ₒ {𝓤} ×ₒ α) α f
  f-order-preserving x y (inl p) = p

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , (λ _ → refl) , (λ _ → refl))

  g-order-preserving : is-order-preserving α (𝟙ₒ {𝓤} ×ₒ α) g
  g-order-preserving x y p = inl p

𝟙ₒ-right-neutral-×ₒ : (α : Ordinal 𝓤) → α ×ₒ 𝟙ₒ {𝓤} ＝ α
𝟙ₒ-right-neutral-×ₒ {𝓤} α = eqtoidₒ (ua _) fe' _ _
                             (f , f-order-preserving ,
                              f-is-equiv , g-order-preserving)
 where
  f : ⟨ α ⟩ × 𝟙 → ⟨ α ⟩
  f = pr₁

  g : ⟨ α ⟩ → ⟨ α ⟩ × 𝟙
  g = (_, ⋆ )

  f-order-preserving : is-order-preserving (α ×ₒ 𝟙ₒ {𝓤}) α f
  f-order-preserving x y (inr (refl , p)) = p

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , (λ _ → refl) , (λ _ → refl))

  g-order-preserving : is-order-preserving α (α ×ₒ 𝟙ₒ {𝓤}) g
  g-order-preserving x y p = inr (refl , p)

\end{code}

Because we use --lossy-unification to speed up typechecking we have to
explicitly mention the universes in the lemma below; using them as variables (as
usual) results in a unification error.

\begin{code}

×ₒ-assoc : {𝓤 𝓥 𝓦 : Universe}
           (α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
         → (α ×ₒ β) ×ₒ γ ＝ α ×ₒ (β ×ₒ γ)
×ₒ-assoc α β γ =
 eqtoidₒ (ua _) fe' ((α  ×ₒ β) ×ₒ γ) (α  ×ₒ (β ×ₒ γ))
  (f , order-preserving-reflecting-equivs-are-order-equivs
   ((α  ×ₒ β) ×ₒ γ) (α  ×ₒ (β ×ₒ γ))
   f f-equiv f-preserves-order f-reflects-order)
  where
   f : ⟨ (α ×ₒ β) ×ₒ γ ⟩ → ⟨ α ×ₒ (β ×ₒ γ) ⟩
   f ((a , b) , c) = (a , (b , c))

   g : ⟨ α ×ₒ (β ×ₒ γ) ⟩ → ⟨ (α ×ₒ β) ×ₒ γ ⟩
   g (a , (b , c)) = ((a , b) , c)

   f-equiv : is-equiv f
   f-equiv = qinvs-are-equivs f (g , (λ x → refl) , (λ x → refl))

   f-preserves-order : is-order-preserving  ((α  ×ₒ β) ×ₒ γ) (α  ×ₒ (β ×ₒ γ)) f
   f-preserves-order _ _ (inl p) = inl (inl p)
   f-preserves-order _ _ (inr (r , inl p)) = inl (inr (r , p))
   f-preserves-order _ _ (inr (r , inr (u , q))) = inr (to-×-＝ u r , q)

   f-reflects-order : is-order-reflecting ((α  ×ₒ β) ×ₒ γ) (α  ×ₒ (β ×ₒ γ)) f
   f-reflects-order _ _ (inl (inl p)) = inl p
   f-reflects-order _ _ (inl (inr (r , q))) = inr (r , (inl q))
   f-reflects-order _ _ (inr (refl , q)) = inr (refl , (inr (refl , q)))

\end{code}

The lemma below is as general as possible in terms of universe parameters
because addition requires its arguments to come from the same universe, at least
at present.

\begin{code}

×ₒ-distributes-+ₒ-right : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
                        → α ×ₒ (β +ₒ γ) ＝ (α ×ₒ β) +ₒ (α ×ₒ γ)
×ₒ-distributes-+ₒ-right α β γ = eqtoidₒ (ua _) fe' _ _
                                 (f , f-order-preserving ,
                                  f-is-equiv , g-order-preserving)
 where
  f : ⟨ α ×ₒ (β +ₒ γ) ⟩ → ⟨ (α ×ₒ β) +ₒ (α ×ₒ γ) ⟩
  f (a , inl b) = inl (a , b)
  f (a , inr c) = inr (a , c)

  g : ⟨ (α ×ₒ β) +ₒ (α ×ₒ γ) ⟩ → ⟨ α ×ₒ (β +ₒ γ) ⟩
  g (inl (a , b)) = a , inl b
  g (inr (a , c)) = a , inr c

  f-order-preserving : is-order-preserving _ _ f
  f-order-preserving (a , inl b) (a' , inl b') (inl p) = inl p
  f-order-preserving (a , inl b) (a' , inr c') (inl p) = ⋆
  f-order-preserving (a , inr c) (a' , inr c') (inl p) = inl p
  f-order-preserving (a , inl b) (a' , inl .b) (inr (refl , q)) = inr (refl , q)
  f-order-preserving (a , inr c) (a' , inr .c) (inr (refl , q)) = inr (refl , q)

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)
   where
    η : g ∘ f ∼ id
    η (a , inl b) = refl
    η (a , inr c) = refl

    ε : f ∘ g ∼ id
    ε (inl (a , b)) = refl
    ε (inr (a , c)) = refl

  g-order-preserving : is-order-preserving _ _ g
  g-order-preserving (inl (a , b)) (inl (a' , b')) (inl p) = inl p
  g-order-preserving (inl (a , b)) (inl (a' , .b)) (inr (refl , q)) =
   inr (refl , q)
  g-order-preserving (inl (a , b)) (inr (a' , c')) p = inl ⋆
  g-order-preserving (inr (a , c)) (inr (a' , c')) (inl p) = inl p
  g-order-preserving (inr (a , c)) (inr (a' , c')) (inr (refl , q)) =
   inr (refl , q)

\end{code}

The following characterizes the initial segments of a product and is rather
useful when working with simulations between products.

\begin{code}

×ₒ-↓ : (α β : Ordinal 𝓤)
     → {a : ⟨ α ⟩} {b : ⟨ β ⟩}
     → (α ×ₒ β) ↓ (a , b) ＝ (α ×ₒ (β ↓ b)) +ₒ (α ↓ a)
×ₒ-↓ α β {a} {b} = eqtoidₒ (ua _) fe' _ _ (f , f-order-preserving ,
                                           f-is-equiv , g-order-preserving)
 where
  f : ⟨ (α ×ₒ β) ↓ (a , b) ⟩ → ⟨ (α ×ₒ (β ↓ b)) +ₒ (α ↓ a) ⟩
  f ((x , y) , inl p) = inl (x , (y , p))
  f ((x , y) , inr (r , q)) = inr (x , q)

  g : ⟨ (α ×ₒ (β ↓ b)) +ₒ (α ↓ a) ⟩ → ⟨ (α ×ₒ β) ↓ (a , b) ⟩
  g (inl (x , y , p)) = (x , y) , inl p
  g (inr (x , q)) = (x , b) , inr (refl , q)

  f-order-preserving : is-order-preserving _ _ f
  f-order-preserving ((x , y) , inl p) ((x' , y') , inl p') (inl l) = inl l
  f-order-preserving ((x , y) , inl p) ((x' , _)  , inl p') (inr (refl , l)) =
   inr ((ap (y ,_) (Prop-valuedness β _ _ p p')) , l)
  f-order-preserving ((x , y) , inl p) ((x' , y') , inr (r' , q')) l = ⋆
  f-order-preserving ((x , y) , inr (refl , q)) ((x' , y') , inl p') (inl l) =
   𝟘-elim (irrefl β y (Transitivity β _ _ _ l p'))
  f-order-preserving ((x , y) , inr (refl , q))
                     ((x' , _)  , inl p') (inr (refl , l)) = 𝟘-elim
                                                              (irrefl β y p')
  f-order-preserving ((x , y) , inr (refl , q))
                     ((x' , _)  , inr (refl , q')) (inl l) = 𝟘-elim
                                                              (irrefl β y l)
  f-order-preserving ((x , y) , inr (refl , q))
                     ((x' , _)  , inr (refl , q')) (inr (_ , l)) = l

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)
   where
    η : g ∘ f ∼ id
    η ((x , y) , inl p) = refl
    η ((x , y) , inr (refl , q)) = refl

    ε : f ∘ g ∼ id
    ε (inl (x , y)) = refl
    ε (inr x) = refl

  g-order-preserving : is-order-preserving _ _ g
  g-order-preserving (inl (x , y , p)) (inl (x' , y' , p')) (inl l) = inl l
  g-order-preserving (inl (x , y , p)) (inl (x' , y' , p')) (inr (refl , l)) =
   inr (refl , l)
  g-order-preserving (inl (x , y , p)) (inr (x' , q')) _ = inl p
  g-order-preserving (inr (x , q))     (inr (x' , q')) l = inr (refl , l)

\end{code}

We now prove several useful facts about (bounded) simulations between products.

TODO: Continue code review here.

\begin{code}

×ₒ-increasing-on-right : {α β γ : Ordinal 𝓤}
                       → 𝟘ₒ ⊲ α
                       → β ⊲ γ
                       → (α ×ₒ β) ⊲ (α ×ₒ γ)
×ₒ-increasing-on-right {α = α} {β} {γ} (a , α↓a=0) (c , r) = (a , c) , eq
 where
  eq = α ×ₒ β                    ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ β) ⁻¹ ⟩
       (α ×ₒ β) +ₒ 𝟘ₒ            ＝⟨ ap₂ (λ - ~ → (α ×ₒ -) +ₒ ~) r α↓a=0 ⟩
       (α ×ₒ (γ ↓ c)) +ₒ (α ↓ a) ＝⟨ ×ₒ-↓ α γ ⁻¹ ⟩
       (α ×ₒ γ) ↓ (a , c)        ∎

×ₒ-right-monotone-⊴ : (α : Ordinal 𝓤)(β γ : Ordinal 𝓥)
                    → β ⊴ γ
                    → (α ×ₒ β) ⊴ (α ×ₒ γ)
×ₒ-right-monotone-⊴ α β γ (g , sim-g) = f , f-initial-segment , f-order-preserving
 where
   f : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
   f (a , b) = a , g b

   f-initial-segment : is-initial-segment (α ×ₒ β) (α ×ₒ γ) f
   f-initial-segment (a , b) (a' , c') (inl p) = (a' , c) , inl r , ap (a' ,_) q
    where
     c  = pr₁ (simulations-are-initial-segments _ _ g sim-g b c' p)
     r = pr₁ (pr₂ (simulations-are-initial-segments _ _ g sim-g b c' p))
     q = pr₂ (pr₂ (simulations-are-initial-segments _ _ g sim-g b c' p))

   f-initial-segment (a , b) (a' , .(pr₂ (f (a , b)))) (inr (refl , q)) = (a' , b) , (inr (refl , q) , refl)

   f-order-preserving : is-order-preserving (α ×ₒ β) (α ×ₒ γ) f
   f-order-preserving (a , b) (a' , b') (inl p) = inl (simulations-are-order-preserving β γ g sim-g b b' p)
   f-order-preserving (a , b) (a' , b') (inr (refl , q)) = inr (refl , q)

×ₒ-≼-left : (α : Ordinal 𝓤)(β : Ordinal 𝓥)
          → {a a' : ⟨ α ⟩}
          → {b : ⟨ β ⟩}
          → a ≼⟨ α ⟩ a'
          → (a , b) ≼⟨ α ×ₒ β ⟩ (a' , b)
×ₒ-≼-left α β {a} {a'} {b} p (a₀ , b₀) (inl r) = inl r
×ₒ-≼-left α β {a} {a'} {b} p (a₀ , b₀) (inr (eq , r)) = inr (eq , (p a₀ r))

\end{code}

To prove that multiplication is left cancellable, we require the
following technical lemma: if α > 𝟘, then every simulation from α ×ₒ β
to α ×ₒ γ decomposes as the identity on the first component, and a
function from β → γ only on the second component (that is, independent
of the first component).

\begin{code}

simulation-product-decomposition : (α : Ordinal 𝓤)(β γ : Ordinal 𝓥)
                                 → (p : 𝟘ₒ ⊲ α)
                                 → (f : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩)
                                 → is-simulation (α ×ₒ β) (α ×ₒ γ) f
                                 → (a : ⟨ α ⟩)(b : ⟨ β ⟩)
                                 →  f (a , b) ＝ (a , pr₂ (f (pr₁ p , b)))
simulation-product-decomposition {𝓤} {𝓥} α β γ (a₀ , α↓a₀＝𝟘) f (sim , op) a b = Transfinite-induction (α ×ₒ β) P g (a , b)
 where
  f' : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
  f' (a , b) = (a , pr₂ (f (a₀ , b)))

  P : ⟨ α ×ₒ β ⟩ → 𝓤 ⊔ 𝓥 ̇
  P (a , b) = (f (a , b)) ＝ f' (a , b)

  g : (ab : ⟨ α ×ₒ β ⟩) → ((ab' : ⟨ α ×ₒ β ⟩) → ab' ≺⟨ α ×ₒ β ⟩ ab → P ab') → P ab
  g (a , b) ih = Extensionality (α ×ₒ γ) _ _ h₀ h₁
   where
    h₀ : (a'c' : ⟨ α ×ₒ γ ⟩) → a'c' ≺⟨ α ×ₒ γ ⟩ f (a , b) → a'c' ≺⟨ α ×ₒ γ ⟩ f' (a , b)
    h₀ (a' , c') p = transport (λ - → - ≺⟨ α ×ₒ γ ⟩ f' (a , b)) e goal
     where
      a₁ : ⟨ α ⟩
      a₁ = pr₁ (pr₁ (sim (a , b) (a' , c') p))
      b₁ : ⟨ β ⟩
      b₁ = pr₂ (pr₁ (sim (a , b) (a' , c') p))
      p' : (a₁ , b₁) ≺⟨ α ×ₒ β ⟩ (a , b)
      p' = pr₁ (pr₂ (sim (a , b) (a' , c') p))
      eq : f (a₁ , b₁) ＝ (a' , c')
      eq = pr₂ (pr₂ (sim (a , b) (a' , c') p))

      e : f' (a₁ , b₁) ＝ (a' , c')
      e = ih (a₁ , b₁) p' ⁻¹ ∙ eq

      a₀' : ⟨ α ⟩
      a₀' = pr₁ (f (a₀ , b))
      goal : (a₁ , pr₂ (f (a₀ , b₁))) ≺⟨ α ×ₒ γ ⟩  (a , pr₂ (f (a₀ , b)))
      goal = Cases p'
               (λ (r : b₁ ≺⟨ β ⟩ b)
                  → Cases (op (a₀' , b₁) (a₀ , b) (inl r))
                      (λ (rr : (pr₂ (f (a₀' , b₁)) ≺⟨ γ ⟩ pr₂ (f (a₀ , b))))
                              → inl (transport (λ - → - ≺⟨ γ ⟩ pr₂ (f (a₀ , b)))
                                               (ap pr₂ (ih (a₀' , b₁) (inl r)))
                                               rr))
                      (λ (rr : (pr₂ (f (a₀' , b₁)) ＝ pr₂ (f (a₀ , b))) × (pr₁ (f (a₀' , b₁))) ≺⟨ α ⟩ a₀')
                             → 𝟘-elim (irrefl α a₀' (transport (λ - → - ≺⟨ α ⟩ a₀')
                                                               (ap pr₁ (ih (a₀' , b₁) (inl r)))
                                                               (pr₂ rr)))))
               (λ (r : (b₁ ＝ b) × (a₁ ≺⟨ α ⟩ a)) → inr (ap (λ - → pr₂ (f (a₀ , -))) (pr₁ r) , pr₂ r))

    h₁ : (u : ⟨ α ×ₒ γ ⟩) → u ≺⟨ α ×ₒ γ ⟩ f' (a , b) → u ≺⟨ α ×ₒ γ ⟩ f  (a , b)
    h₁ (a' , c') (inl p) = q (a' , c') (inl p)
     where
      a₀≼a : a₀ ≼⟨ α ⟩ a
      a₀≼a x p = 𝟘-elim (transport ⟨_⟩ (α↓a₀＝𝟘 ⁻¹) (x , p))

      q : f (a₀ , b) ≼⟨ α ×ₒ γ ⟩ f (a , b)
      q = simulations-are-monotone _ _ f (sim , op) (a₀ , b) (a , b) (×ₒ-≼-left α β a₀≼a)

    h₁ (a' , c') (inr (r , q)) = transport⁻¹ (λ - → - ≺⟨ α ×ₒ γ ⟩ f  (a , b)) eq
                                             (op (a' , b) (a , b) (inr (refl , q)))
     where
      eq : (a' , c') ＝ f (a' , b)
      eq = (a' , c')               ＝⟨ ap (a' ,_) r ⟩
           (a' , pr₂ (f (a₀ , b))) ＝⟨ refl ⟩
           f' (a' , b)             ＝⟨ ih (a' , b) (inr (refl , q)) ⁻¹ ⟩
           f  (a' , b)             ∎

\end{code}

The following result states that multiplication for ordinals can be
cancelled on the left. Interestingly, Andrew Swan [Swa18] proved that
the corresponding result for mere sets is not provable constructively
already for α = 𝟚: there are toposes where the statement

𝟚 × X ≃ 𝟚 × Y → X ≃ Y

is not true for certain objects X and Y in the topos.

[Swa18] Andrew Swan
        On Dividing by Two in Constructive Mathematics
        2018
        https://arxiv.org/abs/1804.04490

\begin{code}

×ₒ-left-cancellable : (α β γ : Ordinal 𝓤)
                    → 𝟘ₒ ⊲ α
                    → (α ×ₒ β) ＝ (α ×ₒ γ)
                    → β ＝ γ
×ₒ-left-cancellable {𝓤} α β γ (a₀ , α↓a₀＝𝟘) m = transfinite-induction-on-OO P g β γ m
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β = (γ : Ordinal 𝓤) → (α ×ₒ β) ＝ (α ×ₒ γ) → β ＝ γ

  g : (β : Ordinal 𝓤) → ((b : ⟨ β ⟩) → P (β ↓ b)) → P β
  g β ih γ m = Extensionality (OO 𝓤) β γ (to-≼ u₀) (to-≼ u₁)
   where
    u : (β γ : Ordinal 𝓤) → (α ×ₒ β) ＝ (α ×ₒ γ)
      → (b : ⟨ β ⟩) → Σ c ꞉ ⟨ γ ⟩ , (α ×ₒ (β ↓ b) ＝ α ×ₒ (γ ↓ c))
    u β γ m b = c , eq
     where
      f : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
      f = ≃ₒ-to-fun _ _ (idtoeqₒ _ _ m)

      p : (α β : Ordinal 𝓤)
        → (a : ⟨ α ⟩)
        → (e : α ＝ β)
        → (α ↓ a) ＝ (β ↓ (≃ₒ-to-fun _ _ (idtoeqₒ _ _ e)) a)
      p α α a refl = refl

      a₀' : ⟨ α ⟩
      a₀' = pr₁ (f (a₀ , b))
      c : ⟨ γ ⟩
      c = pr₂ (f (a₀ , b))

      q : (a₀' , c) ＝ (a₀ , c)
      q = simulation-product-decomposition α β γ (a₀ , α↓a₀＝𝟘)
            f (order-equivs-are-simulations _ _ f
                   (≃ₒ-to-fun-is-order-equiv _ _ (idtoeqₒ _ _ m))) a₀ b

      eq : α ×ₒ (β ↓ b) ＝ α ×ₒ (γ ↓ c)
      eq = α ×ₒ (β ↓ b)                ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ (β ↓ b)) ⁻¹ ⟩
           (α ×ₒ (β ↓ b)) +ₒ 𝟘ₒ        ＝⟨ ap ((α ×ₒ (β ↓ b)) +ₒ_) α↓a₀＝𝟘 ⟩
           (α ×ₒ (β ↓ b)) +ₒ (α ↓ a₀)  ＝⟨ ×ₒ-↓ α β ⁻¹ ⟩
           (α ×ₒ β) ↓ (a₀ , b)         ＝⟨ p (α ×ₒ β) (α ×ₒ γ) (a₀ , b) m ⟩
           (α ×ₒ γ) ↓ (a₀' , c)        ＝⟨ ap ((α ×ₒ γ) ↓_) q ⟩
           (α ×ₒ γ) ↓ (a₀ , c)         ＝⟨ ×ₒ-↓ α γ ⟩
           (α ×ₒ (γ ↓ c)) +ₒ (α ↓ a₀)  ＝⟨ ap ((α ×ₒ (γ ↓ c)) +ₒ_) (α↓a₀＝𝟘 ⁻¹) ⟩
           (α ×ₒ (γ ↓ c)) +ₒ 𝟘ₒ        ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ (γ ↓ c)) ⟩
           α ×ₒ (γ ↓ c)                ∎

    u₀ : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
    u₀ b = let (c , eq) = u β γ m b in (c , ih b (γ ↓ c) eq)

    u₁ : (c : ⟨ γ ⟩) → (γ ↓ c) ⊲ β
    u₁ c = let (b , eq) = u γ β (m ⁻¹) c in b , (ih b (γ ↓ c) (eq ⁻¹) ⁻¹)

\end{code}

Finally, multiplication satisfies the expected recursive equations.

\begin{code}

×ₒ-zero : (α : Ordinal 𝓤) → α ×ₒ 𝟘ₒ {𝓤} ＝ 𝟘ₒ
×ₒ-zero = ×ₒ-𝟘ₒ-right

-- ×ₒ for successors is repeated addition
×ₒ-succ : (α β : Ordinal 𝓤) → α ×ₒ (β +ₒ 𝟙ₒ) ＝ (α ×ₒ β) +ₒ α
×ₒ-succ α β =
  α ×ₒ (β +ₒ 𝟙ₒ)          ＝⟨ ×ₒ-distributes-+ₒ-right α β 𝟙ₒ ⟩
  ((α ×ₒ β) +ₒ (α ×ₒ 𝟙ₒ)) ＝⟨ ap ((α ×ₒ β) +ₒ_) (𝟙ₒ-right-neutral-×ₒ α)  ⟩
  (α ×ₒ β) +ₒ α           ∎

open import UF.PropTrunc
open import UF.Size

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr
 open PropositionalTruncation pt

 -- ×ₒ commutes with suprema
 ×ₒ-sup : (α : Ordinal 𝓤){I : 𝓤 ̇ } (β : I → Ordinal 𝓤) → α ×ₒ sup β ＝ sup (λ i → α ×ₒ β i)
 ×ₒ-sup α {I} β = ⊴-antisym _ _ a b
   where
     a : (α ×ₒ sup β) ⊴ sup (λ i → α ×ₒ β i)
     a = ≼-gives-⊴ _ _ h
       where
        h : (u : Ordinal _) → u ⊲ (α ×ₒ sup β) → u ⊲ sup (λ i → α ×ₒ β i)
        h u ((a , y) , r) = transport (λ - → - ⊲ sup (λ i → α ×ₒ β i)) (r ⁻¹) g''
         where
          g' : Σ i ꞉ I , Σ z ꞉ ⟨ β i ⟩ , sup β ↓ y ＝ (β i) ↓ z → ((α ×ₒ sup β) ↓ (a , y)) ⊲ sup (λ i → α ×ₒ β i)
          g' (i , z , q) = _ , eq where
            eq =
              (α ×ₒ sup β) ↓ (a , y)        ＝⟨ ×ₒ-↓ α (sup β) ⟩
              (α ×ₒ (sup β ↓ y)) +ₒ (α ↓ a) ＝⟨ ap (λ - → ((α ×ₒ -) +ₒ (α ↓ a))) q ⟩
              (α ×ₒ (β i ↓ z)) +ₒ (α ↓ a)   ＝⟨ ×ₒ-↓ α (β i) ⁻¹ ⟩
              (α ×ₒ β i) ↓ (a , z)          ＝⟨ initial-segment-of-sup-at-component (λ j → α ×ₒ β j) i (a , z) ⁻¹ ⟩
              sup (λ i₁ → α ×ₒ β i₁) ↓ _    ∎

          g'' : ((α ×ₒ sup β) ↓ (a , y)) ⊲ sup (λ i → α ×ₒ β i)
          g'' = ∥∥-rec (⊲-is-prop-valued _ _) g' (initial-segment-of-sup-is-initial-segment-of-some-component β y)

     b' : (i : I) → (α ×ₒ β i) ⊴ (α ×ₒ sup β)
     b' i = ×ₒ-right-monotone-⊴ α (β i) (sup β) (sup-is-upper-bound β i)

     b : sup (λ i → α ×ₒ β i) ⊴ (α ×ₒ sup β)
     b = sup-is-lower-bound-of-upper-bounds (λ i → α ×ₒ β i) (α ×ₒ sup β) b'

\end{code}
