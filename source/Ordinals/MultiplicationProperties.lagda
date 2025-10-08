Fredrik Nordvall Forsberg, 13 November 2023.
In collaboration with Tom de Jong, Nicolai Kraus and Chuangjie Xu.

Minor updates 9 and 11 September, 1 November 2024 and 15 July 2025.

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
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.ClassicalLogic

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
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

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

×ₒ-right-monotone-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
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

Multiplication satisfies the expected recursive equations (which
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

 ×ₒ-preserves-suprema : (α : Ordinal 𝓤) (I : 𝓤 ̇ ) (β : I → Ordinal 𝓤)
                      → α ×ₒ sup β ＝ sup (λ i → α ×ₒ β i)
 ×ₒ-preserves-suprema {𝓤} α I β = ⊴-antisym (α ×ₒ sup β) (sup (λ i → α ×ₒ β i)) ⦅1⦆ ⦅2⦆
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

11 September 2024, added by Tom de Jong following a question by Martin Escardo.

The equations for successor and suprema uniquely specify the multiplication
operation and lead to a definition by transfinite recursion.

\begin{code}

 private
  successor-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  successor-equation {𝓤} _⊗_ =
   (α β : Ordinal 𝓤) → α ⊗ (β +ₒ 𝟙ₒ) ＝ (α ⊗ β) +ₒ α

  suprema-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  suprema-equation {𝓤} _⊗_ =
   (α : Ordinal 𝓤) (I : 𝓤 ̇ ) (β : I → Ordinal 𝓤)
    → α ⊗ (sup β) ＝ sup (λ i → α ⊗ β i)

  recursive-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  recursive-equation {𝓤} _⊗_ =
   (α β : Ordinal 𝓤) → α ⊗ β ＝ sup (λ b → (α ⊗ (β ↓ b)) +ₒ α)

  successor-and-suprema-equations-give-recursive-equation
   : (_⊗_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
   → successor-equation _⊗_
   → suprema-equation _⊗_
   → recursive-equation _⊗_
  successor-and-suprema-equations-give-recursive-equation
   _⊗_ ⊗-succ ⊗-sup α β = α ⊗ β                           ＝⟨ I   ⟩
                          (α ⊗ sup (λ b → (β ↓ b) +ₒ 𝟙ₒ)) ＝⟨ II  ⟩
                          sup (λ b → α ⊗ ((β ↓ b) +ₒ 𝟙ₒ)) ＝⟨ III ⟩
                          sup (λ b → (α ⊗ (β ↓ b)) +ₒ α)  ∎
    where
     I   = ap (α ⊗_) (supremum-of-successors-of-initial-segments pt sr β)
     II  = ⊗-sup α ⟨ β ⟩ (λ b → (β ↓ b) +ₒ 𝟙ₒ)
     III = ap sup (dfunext fe' (λ b → ⊗-succ α (β ↓ b)))

 ×ₒ-recursive-equation : recursive-equation {𝓤} _×ₒ_
 ×ₒ-recursive-equation =
  successor-and-suprema-equations-give-recursive-equation
    _×ₒ_ ×ₒ-successor ×ₒ-preserves-suprema

 ×ₒ-is-uniquely-specified'
  : (_⊗_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
  → recursive-equation _⊗_
  → (α β : Ordinal 𝓤) → α ⊗ β ＝ α ×ₒ β
 ×ₒ-is-uniquely-specified' {𝓤} _⊗_ ⊗-rec α =
  transfinite-induction-on-OO (λ - → (α ⊗ -) ＝ (α ×ₒ -)) I
   where
    I : (β : Ordinal 𝓤)
      → ((b : ⟨ β ⟩) → (α ⊗ (β ↓ b)) ＝ (α ×ₒ (β ↓ b)))
      → (α ⊗ β) ＝ (α ×ₒ β)
    I β IH = α ⊗ β                            ＝⟨ II  ⟩
             sup (λ b → (α ⊗ (β ↓ b)) +ₒ α)   ＝⟨ III ⟩
             sup (λ b → (α ×ₒ (β ↓ b)) +ₒ α)  ＝⟨ IV  ⟩
             α ×ₒ β                           ∎
     where
      II  = ⊗-rec α β
      III = ap sup (dfunext fe' (λ b → ap (_+ₒ α) (IH b)))
      IV  = ×ₒ-recursive-equation α β ⁻¹

 ×ₒ-is-uniquely-specified
  : ∃! _⊗_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
     (successor-equation _⊗_) × (suprema-equation _⊗_)
 ×ₒ-is-uniquely-specified {𝓤} =
  (_×ₒ_ , (×ₒ-successor , ×ₒ-preserves-suprema)) ,
  (λ (_⊗_ , ⊗-succ , ⊗-sup) →
   to-subtype-＝
    (λ F → ×-is-prop (Π₂-is-prop fe'
                       (λ _ _ → underlying-type-is-set fe (OO 𝓤)))
                     (Π₃-is-prop fe'
                       (λ _ _ _ → underlying-type-is-set fe (OO 𝓤))))
    (dfunext fe'
      (λ α → dfunext fe'
       (λ β →
        (×ₒ-is-uniquely-specified' _⊗_
          (successor-and-suprema-equations-give-recursive-equation
            _⊗_ ⊗-succ ⊗-sup)
        α β) ⁻¹))))

\end{code}

Added 17 September 2024 by Fredrik Nordvall Forsberg:

Multiplication being monotone in the left argument is a constructive taboo.

Addition 22 November 2024: monotonicity in the left argument is
equivalent to Excluded Middle.

\begin{code}

×ₒ-minimal : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (a₀ : ⟨ α ⟩) (b₀ : ⟨ β ⟩)
           → is-least α a₀ → is-least β b₀ → is-minimal (α ×ₒ β) (a₀ , b₀)
×ₒ-minimal α β a₀ b₀ a₀-least b₀-least (a , b) (inl l)
 = irrefl β b (b₀-least b b l)
×ₒ-minimal α β a₀ b₀ a₀-least b₀-least (a , b) (inr (refl , l))
 = irrefl α a (a₀-least a a l)

×ₒ-least : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (a₀ : ⟨ α ⟩) (b₀ : ⟨ β ⟩)
         → is-least α a₀ → is-least β b₀ → is-least (α ×ₒ β) (a₀ , b₀)
×ₒ-least α β  a₀ b₀ a₀-least b₀-least =
 minimal-is-least (α ×ₒ β) (a₀ , b₀) (×ₒ-minimal α β a₀ b₀ a₀-least b₀-least)

×ₒ-left-monotonicity-implies-EM
  : ((α β : Ordinal 𝓤) (γ : Ordinal 𝓥) → α ⊴ β → α ×ₒ γ ⊴ β ×ₒ γ)
  → EM 𝓤
×ₒ-left-monotonicity-implies-EM hyp P isprop-P = III (f (⋆ , inr ⋆)) refl
 where
  α = 𝟙ₒ
  Pₒ = prop-ordinal P isprop-P
  β = 𝟙ₒ +ₒ Pₒ
  γ = 𝟚ₒ

  I : α ⊴ β
  I = ≼-gives-⊴ α β
       (transport
         (_≼ β)
         (𝟘ₒ-right-neutral 𝟙ₒ)
         (+ₒ-right-monotone 𝟙ₒ 𝟘ₒ Pₒ
         (𝟘ₒ-least Pₒ)))

  II : (α ×ₒ γ) ⊴ (β ×ₒ γ)
  II = hyp α β γ I

  f = pr₁ II
  f-sim = pr₂ II

  f-preserves-least : f (⋆ , inl ⋆) ＝ (inl ⋆ , inl ⋆)
  f-preserves-least = simulations-preserve-least (α ×ₒ γ) (β ×ₒ γ)
                        (⋆ , inl ⋆)
                        (inl ⋆ , inl ⋆)
                        f f-sim
                        (×ₒ-least α γ ⋆ (inl ⋆)
                          ⋆-least
                          (left-preserves-least 𝟙ₒ 𝟙ₒ ⋆ ⋆-least))
                        (×ₒ-least β γ (inl ⋆) (inl ⋆)
                         (left-preserves-least 𝟙ₒ Pₒ ⋆ ⋆-least)
                         (left-preserves-least 𝟙ₒ 𝟙ₒ ⋆ ⋆-least))
   where
    ⋆-least : is-least (𝟙ₒ {𝓤}) ⋆
    ⋆-least ⋆ ⋆ = 𝟘-elim

  III : (x : ⟨ β ×ₒ γ ⟩) → f (⋆ , inr ⋆) ＝ x → P + ¬ P
  III (inl ⋆ , inl ⋆) r = 𝟘-elim (+disjoint' III₂)
   where
    III₁ = f (⋆ , inr ⋆)   ＝⟨ r ⟩
           (inl ⋆ , inl ⋆) ＝⟨ f-preserves-least ⁻¹ ⟩
           f (⋆ , inl ⋆)   ∎
    III₂ : inr ⋆ ＝ inl ⋆
    III₂ = ap pr₂ (simulations-are-lc _ _ f f-sim III₁)
  III (inl ⋆ , inr ⋆) r = inr (λ p → 𝟘-elim (+disjoint (III₆ p)))
   where
    III₃ : (p : P)
         → Σ x ꞉ ⟨ 𝟙ₒ ×ₒ 𝟚ₒ ⟩ ,
             (x ≺⟨ 𝟙ₒ ×ₒ 𝟚ₒ ⟩ (⋆ , inr ⋆)) × (f x ＝ (inr p , inl ⋆))
    III₃ p = simulations-are-initial-segments (α ×ₒ γ) (β ×ₒ γ) f f-sim
               (⋆ , inr ⋆) (inr p , inl ⋆)
               (transport⁻¹ (λ - → (inr p , inl ⋆) ≺⟨ β ×ₒ γ ⟩ - ) r (inl ⋆))
    III₄ : (p : P)
         → Σ x ꞉ ⟨ 𝟙ₒ ×ₒ 𝟚ₒ ⟩ ,
             (x ≺⟨ 𝟙ₒ ×ₒ 𝟚ₒ ⟩ (⋆ , inr ⋆)) × (f x ＝ (inr p , inl ⋆))
         → f (⋆ , inl ⋆) ＝ (inr p , inl ⋆)
    III₄ p ((⋆ , inl ⋆) , l , q) = q
    III₄ p ((⋆ , inr ⋆) , l , q) = 𝟘-elim (irrefl (𝟙ₒ ×ₒ 𝟚ₒ) (⋆ , inr ⋆) l)

    III₅ : (p : P) → (inl ⋆ , inl ⋆) ＝ (inr p , inl ⋆)
    III₅ p = (inl ⋆ , inl ⋆) ＝⟨ f-preserves-least ⁻¹ ⟩
             f (⋆ , inl ⋆)   ＝⟨ III₄ p (III₃ p) ⟩
             (inr p , inl ⋆) ∎

    III₆ : (p : P) → inl ⋆ ＝ inr p
    III₆ p = ap pr₁ (III₅ p)

  III (inr p , c) r = inl p

EM-implies-×ₒ-left-monotonicity
 : EM (𝓤 ⊔ 𝓥)
 → (α β : Ordinal 𝓤) (γ : Ordinal 𝓥) → α ⊴ β → (α ×ₒ γ) ⊴ (β ×ₒ γ)
EM-implies-×ₒ-left-monotonicity em α β γ (g , g-sim)
 = ≼-gives-⊴ (α ×ₒ γ) (β ×ₒ γ)
             (EM-implies-order-preserving-gives-≼ em (α ×ₒ γ)
                                                     (β ×ₒ γ)
                                                     (f , f-order-preserving))
  where
   f : ⟨  α ×ₒ γ ⟩ → ⟨ β ×ₒ γ ⟩
   f (a , c) = (g a , c)

   f-order-preserving : is-order-preserving (α ×ₒ γ) (β ×ₒ γ) f
   f-order-preserving (a , c) (a' , c') (inl l) = inl l
   f-order-preserving (a , c) (a' , c) (inr (refl , l))
    = inr (refl , simulations-are-order-preserving α β g g-sim a a' l)

EM-implies-induced-⊴-on-×ₒ : EM 𝓤
                           → (α β γ δ : Ordinal 𝓤)
                           → α ⊴ γ → β ⊴ δ → (α ×ₒ β) ⊴ (γ ×ₒ δ)
EM-implies-induced-⊴-on-×ₒ em α β γ δ 𝕗 𝕘 =
 ⊴-trans (α ×ₒ β) (α ×ₒ δ) (γ ×ₒ δ)
         (×ₒ-right-monotone-⊴ α β δ 𝕘)
         (EM-implies-×ₒ-left-monotonicity em α γ δ 𝕗)

\end{code}

To prove that multiplication is left cancellable, we require the following
technical lemma: if α > 𝟘, then every simulation from α ×ₒ β to α ×ₒ γ + α ↓ a₁
firstly never hits the second summand, and secondly, in the first component, it
decomposes as the identity on the first component and a function β → γ on the
second component, viz. one that is independent of the first component. The
inspiration for this lemma is the lemma simulation-product-decomposition below,
which only deals with simulations f : α ×ₒ β ⊴ α ×ₒ γ (ie, with α ↓ a₁ = 𝟘ₒ in
the context of the current lemma). However the more general statement seems to
be necessary for proving left cancellability with respect to ⊴, rather than
just with respect to ＝.

\begin{code}

simulation-product-decomposition-generalized
 : (α : Ordinal 𝓤)
 → 𝟘ₒ ⊲ α
 → (β γ : Ordinal 𝓤)
 → (a₁ : ⟨ α ⟩)
 → ((f , _) : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a₁))
 → Σ g ꞉ (⟨ β ⟩ → ⟨ γ ⟩) , ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ inl (a , g b))
simulation-product-decomposition-generalized {𝓤} α (a₀ , a₀-least) = II
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β =   (γ : Ordinal 𝓤) (a₁ : ⟨ α ⟩)
          ((f , _) : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a₁))
        → (b : ⟨ β ⟩) → Σ c ꞉ ⟨ γ ⟩ , ((a : ⟨ α ⟩) → f (a , b) ＝ inl (a , c))

  P₀ : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P₀ β =   (a₁ : ⟨ α ⟩) (γ : Ordinal 𝓤)
           ((f , _) : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a₁))
           (b : ⟨ β ⟩)
           (x : ⟨ (α ×ₒ γ) +ₒ (α ↓ a₁) ⟩)
         → f (a₀ , b) ＝ x
         → Σ c ꞉ ⟨ γ ⟩ , f (a₀ , b) ＝ inl (a₀ , c)

  I : (β γ : Ordinal 𝓤) (a₁ : ⟨ α ⟩)
      ((f , _) : α ×ₒ β ⊴ (α ×ₒ γ) +ₒ (α ↓ a₁))
      (b : ⟨ β ⟩)
    → α ×ₒ (β ↓ b) ＝ α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a₀ , b)
  I β γ a₁ 𝕗@(f , f-sim) b =
   α ×ₒ (β ↓ b)                      ＝⟨ I₁ ⟩
   α ×ₒ (β ↓ b) +ₒ (α ↓ a₀)          ＝⟨ ×ₒ-↓ α β ⁻¹ ⟩
   α ×ₒ β ↓ (a₀ , b)                 ＝⟨ I₂ ⟩
   α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a₀ , b)   ∎
    where
     I₁ = 𝟘ₒ-right-neutral
             (α ×ₒ (β ↓ b)) ⁻¹ ∙ ap (α ×ₒ (β ↓ b) +ₒ_)
             a₀-least
     I₂ = simulations-preserve-↓ _ _ 𝕗 (a₀ , b)

  𝕘₁ : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → P (β ↓ b))
     → P₀ β
  𝕘₁ β IH a₁ γ 𝕗@(f , _) b (inl (a' , c)) e = c , III
    where
     eq = α ×ₒ (β ↓ b)                      ＝⟨ I β γ a₁ 𝕗 b ⟩
          α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a₀ , b)   ＝⟨ ap ((α ×ₒ γ +ₒ (α ↓ a₁)) ↓_) e ⟩
          α ×ₒ γ +ₒ (α ↓ a₁) ↓ inl (a' , c) ＝⟨ +ₒ-↓-left (a' , c) ⁻¹ ⟩
          α ×ₒ γ ↓ (a' , c)                 ＝⟨ ×ₒ-↓ α γ ⟩
          α ×ₒ (γ ↓ c) +ₒ (α ↓ a')          ∎

     𝕗' :  α ×ₒ (β ↓ b) ⊴ α ×ₒ (γ ↓ c) +ₒ (α ↓ a')
     f' = Idtofunₒ eq
     𝕗' = f' , Idtofunₒ-is-simulation eq

     𝕗'⁻¹ : α ×ₒ (γ ↓ c) +ₒ (α ↓ a') ⊴ α ×ₒ (β ↓ b)
     f'⁻¹ = Idtofunₒ (eq ⁻¹)
     𝕗'⁻¹ = f'⁻¹ , Idtofunₒ-is-simulation (eq ⁻¹)

     II : a' ＝ a₀
     II = Extensionality α a' a₀
           (λ x l → 𝟘-elim (II₁ x l))
           (λ x l → 𝟘-elim (transport⁻¹ ⟨_⟩ a₀-least (x , l)))
      where
       II₁ : (x : ⟨ α ⟩) → ¬ (x ≺⟨ α ⟩ a')
       II₁ x l = +disjoint II₂
        where
         y : ⟨ α ×ₒ (β ↓ b) ⟩
         y = f'⁻¹ (inr (x , l))
         y₁ = pr₁ y
         y₂ = pr₂ y

         z : ⟨ γ ↓ c ⟩
         z = pr₁ (IH b (γ ↓ c) a' 𝕗' y₂)

         II₂ = inl (y₁ , z)            ＝⟨ pr₂ (IH b (γ ↓ c) a' 𝕗' y₂) y₁ ⁻¹ ⟩
               f' (f'⁻¹ (inr (x , l))) ＝⟨ Idtofunₒ-retraction eq (inr (x , l)) ⟩
               inr (x , l)             ∎

     III = f (a₀ , b)   ＝⟨ e ⟩
           inl (a' , c) ＝⟨ ap (λ - → inl (- , c)) II ⟩
           inl (a₀ , c) ∎

  𝕘₁ β _ a₁ γ 𝕗@(f , f-sim) b (inr (x , p)) e = 𝟘-elim (ν (a₁ , refl))
   where
    eq-I = α ×ₒ (β ↓ b)                     ＝⟨ I β γ a₁ 𝕗 b ⟩
           α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a₀ , b)  ＝⟨ ap ((α ×ₒ γ +ₒ (α ↓ a₁)) ↓_) e ⟩
           α ×ₒ γ +ₒ (α ↓ a₁) ↓ inr (x , p) ＝⟨ +ₒ-↓-right (x , p) ⁻¹ ⟩
           α ×ₒ γ +ₒ (α ↓ a₁ ↓ (x , p))     ＝⟨ eq-I₁ ⟩
           α ×ₒ γ  +ₒ (α ↓ x)               ∎
     where
      eq-I₁ = ap ((α ×ₒ γ) +ₒ_) (iterated-↓  α a₁ x p)

    eq-II = α ×ₒ γ +ₒ ((α ↓ x) +ₒ α) ＝⟨ +ₒ-assoc (α ×ₒ γ) (α ↓ x) α ⁻¹ ⟩
            α ×ₒ γ +ₒ (α ↓ x) +ₒ α   ＝⟨ ap (_+ₒ α) eq-I ⁻¹ ⟩
            α ×ₒ (β ↓ b) +ₒ α        ＝⟨ ×ₒ-successor α (β ↓ b) ⁻¹ ⟩
            α ×ₒ ((β ↓ b) +ₒ 𝟙ₒ)      ∎

    ineq-I : α ×ₒ γ +ₒ ((α ↓ x) +ₒ α) ⊴ α ×ₒ γ +ₒ (α ↓ a₁)
    ineq-I = transport⁻¹
              (λ - → - ⊴ α ×ₒ γ +ₒ (α ↓ a₁))
              eq-II
              (⊴-trans
               (α ×ₒ ((β ↓ b) +ₒ 𝟙ₒ))
               (α ×ₒ β)
               (α ×ₒ γ +ₒ (α ↓ a₁))
               (×ₒ-right-monotone-⊴ α ((β ↓ b) +ₒ 𝟙ₒ) β
                 (upper-bound-of-successors-of-initial-segments β b))
               𝕗)

    ineq-II : (α ↓ x) +ₒ α ⊴ α ↓ a₁
    ineq-II = +ₒ-left-reflects-⊴ (α ×ₒ γ) ((α ↓ x) +ₒ α) (α ↓ a₁) ineq-I

    h : ⟨ α ⟩ → ⟨ α ↓ a₁ ⟩
    h a = [ (α ↓ x) +ₒ α ,  α ↓ a₁ ]⟨ ineq-II ⟩ (inr a)

    h-order-preserving : is-order-preserving α (α ↓ a₁) h
    h-order-preserving a a' l =
     simulations-are-order-preserving
      ((α ↓ x) +ₒ α)
      (α ↓ a₁)
      [ (α ↓ x) +ₒ α ,  α ↓ a₁ ]⟨ ineq-II ⟩
      ([ (α ↓ x) +ₒ α ,  α ↓ a₁ ]⟨ ineq-II ⟩-is-simulation)
      (inr a) (inr a') l

    ν : ¬ (α ↓ a₁ ⊲ α)
    ν = order-preserving-gives-not-⊲ α (α ↓ a₁)
         (h , h-order-preserving)

  𝕘₂ : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → P (β ↓ b))
     → P β
  𝕘₂ β IH γ a₁ 𝕗@(f , f-sim) b = c , c-satisfies-equation
   where
    c : ⟨ γ ⟩
    c = pr₁ (𝕘₁ β IH a₁ γ 𝕗 b (f (a₀ , b)) refl)

    c-spec : f (a₀ , b) ＝ inl (a₀ , c)
    c-spec = pr₂ (𝕘₁ β IH a₁ γ 𝕗 b (f (a₀ , b)) refl)

    c-satisfies-equation : (a : ⟨ α ⟩) → f (a , b) ＝ inl (a , c)
    c-satisfies-equation a = ↓-lc (α ×ₒ γ +ₒ (α ↓ a₁)) _ _ eq-II
     where
      eq-I = α ×ₒ (β ↓ b)                      ＝⟨ I β γ a₁ 𝕗 b ⟩
             α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a₀ , b)   ＝⟨ eq-I₁ ⟩
             α ×ₒ γ +ₒ (α ↓ a₁) ↓ inl (a₀ , c) ＝⟨ +ₒ-↓-left (a₀ , c) ⁻¹ ⟩
             α ×ₒ γ ↓ (a₀ , c)                 ＝⟨ ×ₒ-↓ α γ ⟩
             α ×ₒ (γ ↓ c) +ₒ (α ↓ a₀)          ＝⟨ eq-I₂ ⟩
             α ×ₒ (γ ↓ c)                      ∎
       where
        eq-I₁ = ap (((α ×ₒ γ) +ₒ (α ↓ a₁)) ↓_) c-spec
        eq-I₂ = ap ((α ×ₒ (γ ↓ c)) +ₒ_) a₀-least ⁻¹
                ∙ 𝟘ₒ-right-neutral (α ×ₒ (γ ↓ c))

      eq-II = α ×ₒ γ +ₒ (α ↓ a₁) ↓ f (a , b)   ＝⟨ eq-II₁ ⟩
              α ×ₒ β ↓ (a , b)                 ＝⟨ ×ₒ-↓ α β ⟩
              α ×ₒ (β ↓ b) +ₒ (α ↓ a)          ＝⟨ ap (_+ₒ (α ↓ a)) eq-I ⟩
              α ×ₒ (γ ↓ c) +ₒ (α ↓ a)          ＝⟨ ×ₒ-↓ α γ ⁻¹ ⟩
              α ×ₒ γ ↓ (a , c)                 ＝⟨ +ₒ-↓-left (a , c) ⟩
              α ×ₒ γ +ₒ (α ↓ a₁) ↓ inl (a , c) ∎
       where
        eq-II₁ = (simulations-preserve-↓ _ _ 𝕗 (a , b)) ⁻¹

  𝕘 : (β : Ordinal 𝓤) → P β
  𝕘 = transfinite-induction-on-OO P 𝕘₂

  II : (β γ : Ordinal 𝓤)
     → (a₁ : ⟨ α ⟩)
     → ((f , _) : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a₁))
     → Σ g ꞉ (⟨ β ⟩ → ⟨ γ ⟩) ,
        ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ inl (a , g b))
  II β γ a₁ 𝕗 = (λ   b → pr₁ (𝕘 β γ a₁ 𝕗 b)) ,
                (λ a b → pr₂ (𝕘 β γ a₁ 𝕗 b) a)

×ₒ-left-cancellable-⊴-generalized : (α β γ : Ordinal 𝓤) (a₁ : ⟨ α ⟩)
                                  → 𝟘ₒ ⊲ α
                                  → α ×ₒ β ⊴ (α ×ₒ γ) +ₒ (α ↓ a₁)
                                  → β ⊴ γ
×ₒ-left-cancellable-⊴-generalized α β γ a₁ p@(a₀ , a₀-least) 𝕗@(f , f-sim) =
 (g , g-is-initial-segment , g-is-order-preserving)
 where
  g : ⟨ β ⟩ → ⟨ γ ⟩
  g = pr₁ (simulation-product-decomposition-generalized α p β γ a₁ 𝕗)

  g-property : (a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ inl (a , g b)
  g-property = pr₂ (simulation-product-decomposition-generalized α p β γ a₁ 𝕗)

  g-is-order-preserving : is-order-preserving β γ g
  g-is-order-preserving b b' l = III II
   where
    I : f (a₀ , b) ≺⟨ (α ×ₒ γ) +ₒ (α ↓ a₁) ⟩ f (a₀ , b')
    I = simulations-are-order-preserving _ _ f f-sim (a₀ , b) (a₀ , b') (inl l)

    II : inl (a₀ , g b) ≺⟨ (α ×ₒ γ) +ₒ (α ↓ a₁) ⟩ inl (a₀ , g b')
    II = transport₂ (λ x y → x ≺⟨ ((α ×ₒ γ) +ₒ (α ↓ a₁))⟩ y)
                    (g-property a₀ b)
                    (g-property a₀ b')
                    I

    III : (a₀ , g b) ≺⟨ (α ×ₒ γ) ⟩ (a₀ , g b') → g b ≺⟨ γ ⟩ g b'
    III (inl p) = p
    III (inr (r , q)) = 𝟘-elim (irrefl α a₀ q)

  g-is-initial-segment : is-initial-segment β γ g
  g-is-initial-segment b c l = b' , II k , III
   where
    l₁ : inl (a₀ , c) ≺⟨ (α ×ₒ γ) +ₒ (α ↓ a₁) ⟩ inl (a₀ , g b)
    l₁ = inl l

    l₂ : inl (a₀ , c) ≺⟨ (α ×ₒ γ) +ₒ (α ↓ a₁) ⟩ f (a₀ , b)
    l₂ = transport⁻¹ (λ - → inl (a₀ , c) ≺⟨ ((α ×ₒ γ) +ₒ (α ↓ a₁))⟩ -)
                     (g-property a₀ b)
                     l₁

    σ : Σ y ꞉ ⟨ α ×ₒ β ⟩ , (y ≺⟨ α ×ₒ β ⟩ (a₀ , b)) × (f y ＝ (inl (a₀ , c)))
    σ = simulations-are-initial-segments _ _ f f-sim (a₀ , b) (inl (a₀ , c)) l₂
    a' = pr₁ (pr₁ σ)
    b' = pr₂ (pr₁ σ)
    k  = pr₁ (pr₂ σ)
    e  = pr₂ (pr₂ σ)

    II : (a' , b') ≺⟨ α ×ₒ β ⟩ (a₀ , b) → b' ≺⟨ β ⟩ b
    II (inl p) = p
    II (inr (r , q)) = 𝟘-elim (Idtofunₒ (a₀-least ⁻¹) (a' , q))

    III : g b' ＝ c
    III = ap pr₂ (inl-lc (inl (a' , g b') ＝⟨ g-property a' b' ⁻¹ ⟩
                          f (a' , b')     ＝⟨ e ⟩
                          inl (a₀ , c)    ∎))

×ₒ-left-cancellable-⊴ : (α β γ : Ordinal 𝓤)
                      → 𝟘ₒ ⊲ α
                      → (α ×ₒ β) ⊴ (α ×ₒ γ)
                      → β ⊴ γ
×ₒ-left-cancellable-⊴ α β γ p@(a₀ , a₀-least) 𝕗 =
 ×ₒ-left-cancellable-⊴-generalized α β γ a₀ p
  (transport (α ×ₒ β ⊴_)
             (α ×ₒ γ             ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ γ) ⁻¹ ⟩
              α ×ₒ γ +ₒ 𝟘ₒ       ＝⟨ ap ((α ×ₒ γ) +ₒ_) a₀-least ⟩
              α ×ₒ γ +ₒ (α ↓ a₀) ∎)
             𝕗)

\end{code}

The following result states that multiplication for ordinals can be cancelled on
the left. Interestingly, Andrew Swan [Swa18] proved that the corresponding
result for sets is not provable constructively already for α = 𝟚: there are
toposes where the statement

  𝟚 × X ≃ 𝟚 × Y → X ≃ Y

is not true for certain objects X and Y in the topos.

[Swa18] Andrew Swan. On Dividing by Two in Constructive Mathematics
        2018. https://arxiv.org/abs/1804.04490

\begin{code}

×ₒ-left-cancellable : (α β γ : Ordinal 𝓤)
                    → 𝟘ₒ ⊲ α
                    → (α ×ₒ β) ＝ (α ×ₒ γ)
                    → β ＝ γ
×ₒ-left-cancellable {𝓤 = 𝓤} α β γ p e = ⊴-antisym β γ (f β γ e) (f γ β (e ⁻¹))
 where
  f : (β γ : Ordinal 𝓤) → (α ×ₒ β) ＝ (α ×ₒ γ) → β ⊴ γ
  f β γ e = ×ₒ-left-cancellable-⊴ α β γ p (≃ₒ-to-⊴ (α ×ₒ β) (α ×ₒ γ)
                                                   (idtoeqₒ (α ×ₒ β) (α ×ₒ γ) e))

\end{code}

As mentioned above, the generalized decomposition lemma for simulation from a
product was inspired by the following less general lemma for which we give both
an indirect and a direct proof (with more general universe levels).

\begin{code}

simulation-product-decomposition' : (α β γ : Ordinal 𝓤)
                                    ((a₀ , a₀-least) : 𝟘ₒ ⊲ α)
                                    ((f , _) : (α ×ₒ β) ⊴ (α ×ₒ γ))
                                    (a : ⟨ α ⟩) (b : ⟨ β ⟩)
                                  → f (a , b) ＝ (a , pr₂ (f (a₀ , b)))
simulation-product-decomposition' α β γ (a₀ , a₀-least) 𝕗@(f , f-sim) a = III
  where
   𝕗' : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a)
   𝕗' = ⊴-trans (α ×ₒ β) (α ×ₒ γ) (α ×ₒ γ +ₒ (α ↓ a))
                𝕗
                (+ₒ-left-⊴ (α ×ₒ γ) (α ↓ a))
   f' = [ α ×ₒ β , α ×ₒ γ +ₒ (α ↓ a) ]⟨ 𝕗' ⟩

   I : Σ g ꞉ (⟨ β ⟩ → ⟨ γ ⟩) ,
        ((a' : ⟨ α ⟩) (b : ⟨ β ⟩) → f' (a' , b) ＝ inl (a' , g b))
   I = simulation-product-decomposition-generalized α (a₀ , a₀-least) β γ a 𝕗'

   g = pr₁ I
   g-property = pr₂ I

   II : (b : ⟨ β ⟩) → g b ＝ pr₂ (f (a₀ , b))
   II b = ap pr₂ (inl-lc (inl (a₀ , g b)   ＝⟨ (g-property a₀ b) ⁻¹ ⟩
                          f' (a₀ , b)      ＝⟨ refl ⟩
                          inl (f (a₀ , b)) ∎))

   III : (b : ⟨ β ⟩)
       → f (a , b) ＝ a , pr₂ (f (a₀ , b))
   III b =
    inl-lc (inl (f (a , b))            ＝⟨ g-property a b ⟩
            inl (a , g b)              ＝⟨ ap (λ - → inl (a , -)) (II b) ⟩
            inl (a , pr₂ (f (a₀ , b))) ∎)

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

Using similar techniques, we can also prove that multiplication is
left cancellable with respect to ⊲.

\begin{code}

simulation-product-decomposition-leftover-empty
 : (α β γ : Ordinal 𝓤)
 → 𝟘ₒ ⊲ α
 → (a : ⟨ α ⟩)
 → (α ×ₒ β) ＝ (α ×ₒ γ +ₒ (α ↓ a))
 → (α ×ₒ β) ＝ (α ×ₒ γ)
simulation-product-decomposition-leftover-empty α β γ (a₀ , p) a e = II
 where
  a-least : (x : ⟨ α ⟩) → ¬ (x ≺⟨ α ⟩ a)
  a-least x l = +disjoint (ν ⁻¹)
   where
    𝕗 : α ×ₒ β ⊴ α ×ₒ γ +ₒ (α ↓ a)
    f = Idtofunₒ e
    𝕗 = f , Idtofunₒ-is-simulation e

    𝕗⁻¹ : α ×ₒ γ +ₒ (α ↓ a) ⊴ α ×ₒ β
    f⁻¹ = Idtofunₒ (e ⁻¹)
    𝕗⁻¹ = f⁻¹ , Idtofunₒ-is-simulation (e ⁻¹)

    f-decomposition
     : Σ g ꞉ (⟨ β ⟩ → ⟨ γ ⟩) ,
        ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ inl (a , g b) )
    f-decomposition =
      simulation-product-decomposition-generalized α (a₀ , p) β γ a 𝕗

    g = pr₁ f-decomposition

    ν = (inr (x , l))         ＝⟨ (Idtofunₒ-retraction e (inr (x , l))) ⁻¹ ⟩
        f (f⁻¹ (inr (x , l))) ＝⟨ pr₂ (f-decomposition) x' y' ⟩
        inl (x' , g y')       ∎
     where
      x' = pr₁ (f⁻¹ (inr (x , l)))
      y' = pr₂ (f⁻¹ (inr (x , l)))

  I : a ＝ a₀
  I = Extensionality α a a₀ (λ x l → 𝟘-elim (a-least x l))
                            (λ x l → 𝟘-elim (Idtofunₒ (p ⁻¹) (x , l)))

  II = α ×ₒ β            ＝⟨ e ⟩
       α ×ₒ γ +ₒ (α ↓ a) ＝⟨ ap ((α ×ₒ γ) +ₒ_) (ap (α ↓_) I ∙ p ⁻¹) ⟩
       α ×ₒ γ +ₒ 𝟘ₒ      ＝⟨ 𝟘ₒ-right-neutral (α ×ₒ γ) ⟩
       α ×ₒ γ            ∎

×ₒ-left-cancellable-⊲ : (α β γ : Ordinal 𝓤)
                      → 𝟘ₒ ⊲ α
                      → α ×ₒ β ⊲ α ×ₒ γ
                      → β ⊲ γ
×ₒ-left-cancellable-⊲ α β γ α-positive ((a , c) , p) = c , III
 where
  I : α ×ₒ β ＝ α ×ₒ (γ ↓ c) +ₒ (α ↓ a)
  I = p ∙ ×ₒ-↓ α γ

  II : α ×ₒ β ＝ α ×ₒ (γ ↓ c)
  II = simulation-product-decomposition-leftover-empty α β (γ ↓ c) α-positive a I

  III : β ＝ γ ↓ c
  III = ×ₒ-left-cancellable α β (γ ↓ c) α-positive II

\end{code}

Added 15 July 2025 by Tom de Jong.

\begin{code}

×ₒ-as-large-as-right-factor-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β) → EM 𝓤
×ₒ-as-large-as-right-factor-implies-EM  hyp P P-is-prop = IV (f (inr ⋆)) refl
 where
  Pₒ = prop-ordinal P P-is-prop
  α = 𝟙ₒ +ₒ Pₒ
  β = 𝟚ₒ
  𝕗 : β ⊴ α ×ₒ β
  𝕗 = hyp α β (inl ⋆ , (𝟙ₒ-↓ ⁻¹ ∙ +ₒ-↓-left ⋆))
  f = [ β , α ×ₒ β ]⟨ 𝕗 ⟩
  f-is-sim : is-simulation β (α ×ₒ β) f
  f-is-sim = [ β , α ×ₒ β ]⟨ 𝕗 ⟩-is-simulation

  I : (p : P) → f (inr ⋆) ＝ (inr p , inl ⋆)
  I p = ↓-lc (α ×ₒ β) (f (inr ⋆)) (inr p , inl ⋆) e
   where
    e = (α ×ₒ β) ↓ f (inr ⋆)            ＝⟨ e₁ ⟩
        β ↓ inr ⋆                       ＝⟨ e₂ ⟩
        𝟙ₒ                              ＝⟨ e₃ ⟩
        α ↓ inr p                       ＝⟨ e₄ ⟩
        α ×ₒ 𝟘ₒ +ₒ (α ↓ inr p)          ＝⟨ e₅ ⟩
        α ×ₒ (β ↓ inl ⋆) +ₒ (α ↓ inr p) ＝⟨ ×ₒ-↓ α β ⁻¹ ⟩
        (α ×ₒ β) ↓ (inr p , inl ⋆)      ∎
     where
      e₁ = (simulations-preserve-↓ β (α ×ₒ β) 𝕗 (inr ⋆)) ⁻¹
      e₂ = +ₒ-↓-right ⋆ ⁻¹ ∙ ap (𝟙ₒ +ₒ_) 𝟙ₒ-↓ ∙ 𝟘ₒ-right-neutral 𝟙ₒ
      e₃ = (𝟘ₒ-right-neutral 𝟙ₒ) ⁻¹
           ∙ ap (𝟙ₒ +ₒ_) ((prop-ordinal-↓ P-is-prop p) ⁻¹) ∙ +ₒ-↓-right p
      e₄ = (ap (_+ₒ (α ↓ inr p)) (×ₒ-𝟘ₒ-right α)
           ∙ 𝟘ₒ-left-neutral (α ↓ inr p)) ⁻¹
      e₅ = ap (λ - → α ×ₒ - +ₒ (α ↓ inr p)) (𝟙ₒ-↓ ⁻¹ ∙ +ₒ-↓-left ⋆)
  II : (x : ⟨ α ⟩) → f (inr ⋆) ＝ (x , inr ⋆) → ¬ P
  II x e p = +disjoint (ap pr₂ ((I p) ⁻¹ ∙ e))
  III : f (inr ⋆) ≠ (inl ⋆ , inl ⋆)
  III h = +disjoint (simulations-are-lc β (α ×ₒ β) f f-is-sim (e ∙ h ⁻¹))
   where
    e : f (inl ⋆) ＝ (inl ⋆ , inl ⋆)
    e = simulations-preserve-least
         β (α ×ₒ β) (inl ⋆) (inl ⋆ , inl ⋆) f f-is-sim
         β-least
         (×ₒ-least α β (inl ⋆) (inl ⋆) (+ₒ-least 𝟙ₒ Pₒ ⋆ 𝟙ₒ-least) β-least)
     where
      β-least : is-least β (inl ⋆)
      β-least = +ₒ-least 𝟙ₒ 𝟙ₒ ⋆ 𝟙ₒ-least
  IV : (x : ⟨ α ×ₒ β ⟩) → f (inr ⋆) ＝ x → P + ¬ P
  IV (inl ⋆ , inl ⋆) e = 𝟘-elim (III e)
  IV (inr p , inl ⋆) e = inl p
  IV (inl ⋆ , inr ⋆) e = inr (II (inl ⋆) e)
  IV (inr p , inr ⋆) e = inl p

EM-implies-×ₒ-as-large-as-right-factor
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β
EM-implies-×ₒ-as-large-as-right-factor em α β (a₀ , _) =
 ≼-gives-⊴ β (α ×ₒ β)
             (EM-implies-order-preserving-gives-≼ em β (α ×ₒ β) (f , I))
  where
   f : ⟨ β ⟩ → ⟨ α ×ₒ β ⟩
   f b = (a₀ , b)
   I : is-order-preserving β (α ×ₒ β) f
   I b b' l = inl l

\end{code}

Added in September 2025 by Fredrik Nordvall Forsberg.
Moved here from ArithmeticReflection by Tom de Jong in October 2025.

Some special cases of multiplication by ω.

\begin{code}

𝟙ₒ×ₒω-is-ω : 𝟙ₒ ×ₒ ω ＝ ω
𝟙ₒ×ₒω-is-ω = 𝟙ₒ-left-neutral-×ₒ ω

𝟚ₒ×ₒω-is-ω : 𝟚ₒ ×ₒ ω ＝ ω
𝟚ₒ×ₒω-is-ω = eqtoidₒ (ua _) fe' (𝟚ₒ ×ₒ ω) ω h
 where
  open import Naturals.Addition hiding (_+_)
  open import Naturals.Division
  open import Naturals.Order
  open import Naturals.Properties
  f : ⟨ 𝟚ₒ ⟩ × ℕ → ℕ
  f (inl ⋆ , n) = double n
  f (inr ⋆ , n) = sdouble n

  g' : (n : ℕ) → division-theorem n 1 → ⟨ 𝟚ₒ ⟩ × ℕ
  g' n (k , 0 , p , l) = inl ⋆ , k
  g' n (k , 1 , p , l) = inr ⋆ , k

  g : ℕ → ⟨ 𝟚ₒ ⟩ × ℕ
  g n = g' n (division n 1)

  f-equiv : is-equiv f
  f-equiv = qinvs-are-equivs f (g , (η , ϵ))
   where
    η' : (x : ⟨ 𝟚ₒ ⟩ × ℕ)(m : ℕ) → m ＝ f x → (d : division-theorem m 1)
       → g' m d ＝ x
    η' (inl ⋆ , n) m r (k , 0 , p , l) = ap (inl ⋆ ,_) (double-lc τ)
     where
      τ : double k ＝ double n
      τ = double-is-self-addition k ∙ p ⁻¹ ∙ r
    η' (inr ⋆ , n) m r (k , 0 , p , l) = 𝟘-elim (double-is-not-sdouble τ)
     where
      τ : double k ＝ sdouble n
      τ = double-is-self-addition k ∙ p ⁻¹  ∙ r
    η' (inl ⋆ , n) m r (k , 1 , p , l) = 𝟘-elim (double-is-not-sdouble τ)
     where
      τ : double n ＝ sdouble k
      τ = r ⁻¹ ∙ p ∙ ap succ (double-is-self-addition k ⁻¹)
    η' (inr ⋆ , n) m r (k , 1 , p , l) = ap (inr ⋆ ,_) (sdouble-lc τ)
     where
      τ : sdouble k ＝ sdouble n
      τ = ap succ (double-is-self-addition k) ∙ p ⁻¹ ∙ r

    η : (λ x → g (f x)) ∼ id
    η x = η' x (f x) refl (division (f x) 1)

    ϵ' : (n : ℕ) → (d : division-theorem n 1) → f (g' n d) ＝ n
    ϵ' n (k , 0 , refl , l) = double-is-self-addition k
    ϵ' n (k , 1 , refl , l) = ap succ (double-is-self-addition k)

    ϵ : (λ n → f (g n)) ∼ id
    ϵ n = ϵ' n (division n 1)

  f-preserves-order : (x y : ⟨ 𝟚ₒ ⟩ × ℕ) → x ≺⟨ 𝟚ₒ ×ₒ ω ⟩ y → f x ≺⟨ ω ⟩ f y
  f-preserves-order (inl ⋆ , x) (inl ⋆ , y) (inl p) =
   transport₂⁻¹ (λ - → succ - ≤ℕ_)
                (double-is-self-addition x)
                (double-is-self-addition y)
                (≤-adding x y (succ x) y (≤-trans x (succ x) y (≤-succ x) p) p)
  f-preserves-order (inl ⋆ , x) (inr ⋆ , y) (inl p) =
   transport₂⁻¹ _≤ℕ_ (double-is-self-addition x) (double-is-self-addition y)
    (≤-adding x y x y (≤-trans x (succ x) y (≤-succ x) p)
                      (≤-trans x (succ x) y (≤-succ x) p))
  f-preserves-order (inr ⋆ , x) (inl ⋆ , y) (inl p) =
   transport₂⁻¹ (λ - → succ - ≤ℕ_)
                (ap succ (double-is-self-addition x) ∙ succ-left x x ⁻¹)
                (double-is-self-addition y)
                (≤-adding (succ x) y (succ x) y p p)
  f-preserves-order (inr ⋆ , x) (inr ⋆ , y) (inl p) =
   transport₂⁻¹ (λ - → succ - ≤ℕ_)
                (double-is-self-addition x)
                (double-is-self-addition y)
                (≤-adding x y (succ x) y (≤-trans x (succ x) y (≤-succ x) p) p)
  f-preserves-order (inl ⋆ , x) (inr ⋆ , x) (inr (refl , _)) = ≤-refl _
  f-preserves-order (inr ⋆ , x) (inl ⋆ , x) (inr (refl , q)) = 𝟘-elim q
  f-preserves-order (inr ⋆ , x) (inr ⋆ , x) (inr (refl , q)) = 𝟘-elim q

  f-reflects-order : (x y : ⟨ 𝟚ₒ ⟩ × ℕ) → f x ≺⟨ ω ⟩ f y → x ≺⟨ 𝟚ₒ ×ₒ ω ⟩ y
  f-reflects-order (inl ⋆ , x) (inl ⋆ , y) p = inl (double-reflects-< p)
  f-reflects-order (inl ⋆ , x) (inr ⋆ , y) p = τ (<-trichotomous x y)
   where
    τ : (x <ℕ y) + (x ＝ y) + (y <ℕ x) → (x <ℕ y) + (x ＝ y) × 𝟙
    τ (inl l) = inl l
    τ (inr (inl e)) = inr (e , ⋆)
    τ (inr (inr g)) =
     𝟘-elim (less-than-not-equal y y (<-≤-trans y x y g (double-reflects-≤ p)) refl)
  f-reflects-order (inr ⋆ , x) (inl ⋆ , y) p = inl (double-reflects-≤ p)
  f-reflects-order (inr ⋆ , x) (inr ⋆ , y) p = inl (double-reflects-< p)

  h : (𝟚ₒ ×ₒ ω) ≃ₒ ω
  h = f , order-preserving-reflecting-equivs-are-order-equivs (𝟚ₒ ×ₒ ω) ω f
           f-equiv f-preserves-order f-reflects-order

\end{code}