Fredrik Nordvall Forsberg, 13 November 2023.
In collaboration with Tom de Jong, Nicolai Kraus and Chuangjie Xu.

Minor updates 9 and 11 September 2024.

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

\begin{code}

×ₒ-increasing-on-right : (α β γ : Ordinal 𝓤)
                       → 𝟘ₒ ⊲ α
                       → β ⊲ γ
                       → (α ×ₒ β) ⊲ (α ×ₒ γ)
×ₒ-increasing-on-right α β γ (a , p) (c , q) = (a , c) , I
 where
  I = α ×ₒ β                    ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ β) ⁻¹ ⟩
      (α ×ₒ β) +ₒ 𝟘ₒ            ＝⟨ ap₂ (λ -₁ -₂ → (α ×ₒ -₁) +ₒ -₂) q p ⟩
      (α ×ₒ (γ ↓ c)) +ₒ (α ↓ a) ＝⟨ ×ₒ-↓ α γ ⁻¹ ⟩
      (α ×ₒ γ) ↓ (a , c)        ∎

×ₒ-right-monotone-⊴ : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
                    → β ⊴ γ
                    → (α ×ₒ β) ⊴ (α ×ₒ γ)
×ₒ-right-monotone-⊴ α β γ (g , sim-g) = f , f-initial-segment ,
                                            f-order-preserving
 where
   f : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
   f (a , b) = a , g b

   f-initial-segment : is-initial-segment (α ×ₒ β) (α ×ₒ γ) f
   f-initial-segment (a , b) (a' , c') (inl l) = (a' , b') , inl k , ap (a' ,_) q
    where
     I : Σ b' ꞉ ⟨ β ⟩ , b' ≺⟨ β ⟩ b × (g b' ＝ c')
     I = simulations-are-initial-segments β γ g sim-g b c' l
     b' = pr₁ I
     k = pr₁ (pr₂ I)
     q = pr₂ (pr₂ I)
   f-initial-segment (a , b) (a' , c') (inr (refl , q)) =
    (a' , b) , inr (refl , q) , refl

   f-order-preserving : is-order-preserving (α ×ₒ β) (α ×ₒ γ) f
   f-order-preserving (a , b) (a' , b') (inl p) =
    inl (simulations-are-order-preserving β γ g sim-g b b' p)
   f-order-preserving (a , b) (a' , b') (inr (refl , q)) = inr (refl , q)

×ₒ-≼-left : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
            {a a' : ⟨ α ⟩} {b : ⟨ β ⟩}
          → a ≼⟨ α ⟩ a'
          → (a , b) ≼⟨ α ×ₒ β ⟩ (a' , b)
×ₒ-≼-left α β p (a₀ , b₀) (inl r) = inl r
×ₒ-≼-left α β p (a₀ , b₀) (inr (eq , r)) = inr (eq , p a₀ r)

\end{code}

To prove that multiplication is left cancellable, we require the following
technical lemma: if α > 𝟘, then every simulation from α ×ₒ β to α ×ₒ γ
decomposes as the identity on the first component and a function β → γ on the
second component, viz. one that is independent of the first component.

\begin{code}

simulation-product-decomposition
 : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
   ((a₀ , a₀-least) : 𝟘ₒ ⊲ α)
   ((f , _) : (α ×ₒ β) ⊴ (α ×ₒ γ))
 → (a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ (a , pr₂ (f (a₀ , b)))
simulation-product-decomposition {𝓤} {𝓥} α β γ (a₀ , a₀-least)
                                 (f , sim@(init-seg , order-pres)) a b = I
 where
  f' : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
  f' (a , b) = (a , pr₂ (f (a₀ , b)))

  P : ⟨ α ×ₒ β ⟩ → 𝓤 ⊔ 𝓥 ̇
  P (a , b) = (f (a , b)) ＝ f' (a , b)

  I : P (a , b)
  I = Transfinite-induction (α ×ₒ β) P II (a , b)
   where
    II : (x : ⟨ α ×ₒ β ⟩)
       → ((y : ⟨ α ×ₒ β ⟩) → y ≺⟨ α ×ₒ β ⟩ x → P y)
       → P x
    II (a , b) IH = Extensionality (α ×ₒ γ) (f (a , b)) (f' (a , b)) III IV
     where
      III : (u : ⟨ α ×ₒ γ ⟩) → u ≺⟨ α ×ₒ γ ⟩ f (a , b) → u ≺⟨ α ×ₒ γ ⟩ f' (a , b)
      III (a' , c') p = transport (λ - → - ≺⟨ α ×ₒ γ ⟩ f' (a , b)) III₂ (III₃ p')
       where
        III₁ : Σ (a'' , b') ꞉ ⟨ α ×ₒ β ⟩ , (a'' , b') ≺⟨ α ×ₒ β ⟩ (a , b)
                                         × (f (a'' , b') ＝ a' , c')
        III₁ = init-seg (a , b) (a' , c') p
        a'' = pr₁ (pr₁ III₁)
        b' = pr₂ (pr₁ III₁)
        p' = pr₁ (pr₂ III₁)
        eq : f (a'' , b') ＝ (a' , c')
        eq = pr₂ (pr₂ III₁)

        III₂ : f' (a'' , b') ＝ (a' , c')
        III₂ = IH (a'' , b') p' ⁻¹ ∙ eq

        III₃ : (a'' , b') ≺⟨ α ×ₒ β ⟩ (a , b)
             → f' (a'' , b') ≺⟨ α ×ₒ γ ⟩ f' (a , b)
        III₃ (inl q) = h (order-pres (a₀' , b') (a₀ , b) (inl q))
         where
          a₀' : ⟨ α ⟩
          a₀' = pr₁ (f (a₀ , b))

          ih : (f (a₀' , b')) ＝ f' (a₀' , b')
          ih = IH (a₀' , b') (inl q)

          h : f  (a₀' , b') ≺⟨ α ×ₒ γ ⟩ f  (a₀ , b)
            → f' (a'' , b') ≺⟨ α ×ₒ γ ⟩ f' (a , b)
          h (inl r) = inl (transport (λ - → - ≺⟨ γ ⟩ pr₂ (f (a₀ , b)))
                                     (ap pr₂ ih) r)
          h (inr (_ , r)) = 𝟘-elim (irrefl α a₀' (transport (λ - → - ≺⟨ α ⟩ a₀')
                                                            (ap pr₁ ih) r))
        III₃ (inr (e , q)) = inr (ap (λ - → pr₂ (f (a₀ , -))) e , q)

      IV : (u : ⟨ α ×ₒ γ ⟩) → u ≺⟨ α ×ₒ γ ⟩ f' (a , b) → u ≺⟨ α ×ₒ γ ⟩ f  (a , b)
      IV (a' , c') (inl p) = l₂ (a' , c') (inl p)
       where
        l₁ : a₀ ≼⟨ α ⟩ a
        l₁ x p = 𝟘-elim (transport ⟨_⟩ (a₀-least ⁻¹) (x , p))
        l₂ : f (a₀ , b) ≼⟨ α ×ₒ γ ⟩ f (a , b)
        l₂ = simulations-are-monotone _ _
              f sim (a₀ , b) (a , b) (×ₒ-≼-left α β l₁)
      IV (a' , c') (inr (r , q)) =
       transport (λ - → - ≺⟨ α ×ₒ γ ⟩ f  (a , b)) eq
                 (order-pres (a' , b) (a , b) (inr (refl , q)))
        where
         eq = f  (a' , b)             ＝⟨ IH (a' , b) (inr (refl , q)) ⟩
              f' (a' , b)             ＝⟨ refl ⟩
              (a' , pr₂ (f (a₀ , b))) ＝⟨ ap (a' ,_) (r ⁻¹) ⟩
              (a' , c')               ∎

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
×ₒ-left-cancellable {𝓤} α β γ (a₀ , a₀-least) =
 transfinite-induction-on-OO P II β γ
  where
   P : Ordinal 𝓤 → 𝓤 ⁺ ̇
   P β = (γ : Ordinal 𝓤) → (α ×ₒ β) ＝ (α ×ₒ γ) → β ＝ γ

   I : (β γ : Ordinal 𝓤)
     → (α ×ₒ β) ＝ (α ×ₒ γ)
     → (b : ⟨ β ⟩) → Σ c ꞉ ⟨ γ ⟩ , (α ×ₒ (β ↓ b) ＝ α ×ₒ (γ ↓ c))
   I β γ e b = c , eq
    where
     𝕗 : (α ×ₒ β) ⊴ (α ×ₒ γ)
     𝕗 = ≃ₒ-to-⊴ (α ×ₒ β) (α ×ₒ γ) (idtoeqₒ _ _ e)
     f : ⟨ α ×ₒ β ⟩ → ⟨ α ×ₒ γ ⟩
     f = [ α ×ₒ β , α ×ₒ γ ]⟨ 𝕗 ⟩

     c : ⟨ γ ⟩
     c = pr₂ (f (a₀ , b))

     eq = α ×ₒ (β ↓ b)                ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ (β ↓ b)) ⁻¹ ⟩
          (α ×ₒ (β ↓ b)) +ₒ 𝟘ₒ        ＝⟨ ap ((α ×ₒ (β ↓ b)) +ₒ_) a₀-least ⟩
          (α ×ₒ (β ↓ b)) +ₒ (α ↓ a₀)  ＝⟨ ×ₒ-↓ α β ⁻¹ ⟩
          (α ×ₒ β) ↓ (a₀ , b)         ＝⟨ eq₁ ⟩
          (α ×ₒ γ) ↓ (a₀' , c)        ＝⟨ eq₂ ⟩
          (α ×ₒ γ) ↓ (a₀ , c)         ＝⟨ ×ₒ-↓ α γ ⟩
          (α ×ₒ (γ ↓ c)) +ₒ (α ↓ a₀)  ＝⟨ ap ((α ×ₒ (γ ↓ c)) +ₒ_) (a₀-least ⁻¹) ⟩
          (α ×ₒ (γ ↓ c)) +ₒ 𝟘ₒ        ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ (γ ↓ c)) ⟩
          α ×ₒ (γ ↓ c)                ∎
      where
       a₀' : ⟨ α ⟩
       a₀' = pr₁ (f (a₀ , b))

       eq₁ = simulations-preserve-↓ (α ×ₒ β) (α ×ₒ γ) 𝕗 (a₀ , b)
       eq₂ = ap ((α ×ₒ γ) ↓_)
                (simulation-product-decomposition α β γ (a₀ , a₀-least) 𝕗 a₀ b)

   II : (β : Ordinal 𝓤) → ((b : ⟨ β ⟩) → P (β ↓ b)) → P β
   II β IH γ e = Extensionality (OO 𝓤) β γ (to-≼ III) (to-≼ IV)
    where
     III : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
     III b = let (c , eq) = I β γ  e     b in (c , IH b (γ ↓ c) eq)
     IV  : (c : ⟨ γ ⟩) → (γ ↓ c) ⊲ β
     IV  c = let (b , eq) = I γ β (e ⁻¹) c in (b , (IH b (γ ↓ c) (eq ⁻¹) ⁻¹))

\end{code}

Finally, multiplication satisfies the expected recursive equations (which
classically define ordinal multiplication): zero is fixed by multiplication
(this is ×ₒ-𝟘ₒ-right above), multiplication for successors is repeated addition
and multiplication preserves suprema.

\begin{code}

×ₒ-successor : (α β : Ordinal 𝓤) → α ×ₒ (β +ₒ 𝟙ₒ) ＝ (α ×ₒ β) +ₒ α
×ₒ-successor α β =
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

 ×ₒ-preserves-suprema : (α : Ordinal 𝓤) {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                      → α ×ₒ sup β ＝ sup (λ i → α ×ₒ β i)
 ×ₒ-preserves-suprema {𝓤} α {I} β = ⊴-antisym (α ×ₒ sup β) (sup (λ i → α ×ₒ β i)) ⦅1⦆ ⦅2⦆
  where
   ⦅2⦆ : sup (λ i → α ×ₒ β i) ⊴ (α ×ₒ sup β)
   ⦅2⦆ = sup-is-lower-bound-of-upper-bounds (λ i → α ×ₒ β i) (α ×ₒ sup β)
          (λ i → ×ₒ-right-monotone-⊴ α (β i) (sup β) (sup-is-upper-bound β i))

   ⦅1⦆ : (α ×ₒ sup β) ⊴ sup (λ i → α ×ₒ β i)
   ⦅1⦆ = ≼-gives-⊴ (α ×ₒ sup β) (sup (λ i → α ×ₒ β i)) ⦅1⦆-I
    where
     ⦅1⦆-I : (γ : Ordinal 𝓤) → γ ⊲ (α ×ₒ sup β) → γ ⊲ sup (λ i → α ×ₒ β i)
     ⦅1⦆-I _ ((a , y) , refl) = ⦅1⦆-III
      where
       ⦅1⦆-II : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , sup β ↓ y ＝ (β i) ↓ b)
              → ((α ×ₒ sup β) ↓ (a , y)) ⊲ sup (λ j → α ×ₒ β j)
       ⦅1⦆-II (i , b , e) = σ (a , b) , eq
        where
         σ : ⟨ α ×ₒ β i ⟩ → ⟨ sup (λ j → α ×ₒ β j) ⟩
         σ = [ α ×ₒ β i , sup (λ j → α ×ₒ β j) ]⟨ sup-is-upper-bound _ i ⟩

         eq = (α ×ₒ sup β) ↓ (a , y)           ＝⟨ ×ₒ-↓ α (sup β) ⟩
              (α ×ₒ (sup β ↓ y)) +ₒ (α ↓ a)    ＝⟨ eq₁ ⟩
              (α ×ₒ (β i ↓ b)) +ₒ (α ↓ a)      ＝⟨ ×ₒ-↓ α (β i) ⁻¹ ⟩
              (α ×ₒ β i) ↓ (a , b)             ＝⟨ eq₂ ⟩
              sup (λ j → α ×ₒ β j) ↓ σ (a , b) ∎
          where
           eq₁ = ap (λ - → ((α ×ₒ -) +ₒ (α ↓ a))) e
           eq₂ = (initial-segment-of-sup-at-component
                  (λ j → α ×ₒ β j) i (a , b)) ⁻¹

       ⦅1⦆-III : ((α ×ₒ sup β) ↓ (a , y)) ⊲ sup (λ i → α ×ₒ β i)
       ⦅1⦆-III = ∥∥-rec (⊲-is-prop-valued _ _) ⦅1⦆-II
                  (initial-segment-of-sup-is-initial-segment-of-some-component
                    β y)

\end{code}
