Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
26 November 2024.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.TrichotomyAndIsolation
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
open import UF.UA-FunExt
open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

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
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderingTaboo
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open import Ordinals.Exponentiation.DecreasingList ua pt sr

open PropositionalTruncation pt

open suprema pt sr

\end{code}

Let α be an ordinal. Its order relation ≺ is locally trichotomous at
an element x if x ≺ y or x = y or y ≺ x for all y : α, and we say x is
trichotomous in α.

\begin{code}

is-locally-trichotomous-at : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-locally-trichotomous-at α x = (y : ⟨ α ⟩) → (y ≺⟨ α ⟩ x) + (x ＝ y) + (x ≺⟨ α ⟩ y)

syntax is-locally-trichotomous-at α x = x is-trichotomous-in α

\end{code}

We say x is isolated in α if there is an e: α = β + 𝟙 + γ for some
ordinals β and γ such that e maps x to in(⋆).

\begin{code}

is-decomposed-at : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ⁺ ̇
is-decomposed-at {𝓤} α x =
  Σ β ꞉ Ordinal 𝓤 , Σ γ ꞉ Ordinal 𝓤 , Σ e ꞉ α ≃ₒ (β +ₒ (𝟙ₒ +ₒ γ)) , ≃ₒ-to-fun _ _ e x ＝ inr (inl ⋆)

syntax is-decomposed-at α x = x is-isolated-in α

\end{code}

An element x is trichotomous in ordinal α iff it is isolated in α.

\begin{code}

trichotomoy-to-isolation : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
    → x is-trichotomous-in α → x is-isolated-in α
trichotomoy-to-isolation {𝓤} α x tri = β , γ , e , e-spec
 where
  _<_ = underlying-order α

  ⟨β⟩ : 𝓤 ̇
  ⟨β⟩ = Σ y ꞉ ⟨ α ⟩ , y < x
  _<'_ : ⟨β⟩ → ⟨β⟩ → 𝓤 ̇
  _<'_ = subtype-order α (λ - → - < x)
  <'-propvalued : is-prop-valued _<'_
  <'-propvalued = subtype-order-propositional α (λ - → - < x)
  <'-wellfounded : is-well-founded _<'_
  <'-wellfounded = subtype-order-wellfounded α (λ - → - < x)
  <'-extensional : is-extensional _<'_
  <'-extensional (y , y-lt-x) (z , z-lt-x) f g = to-subtype-＝ (λ a → Prop-valuedness α a x)
                                                               (Extensionality α y z u v)
   where
    u : (a : ⟨ α ⟩) → a < y → a < z
    u a a-lt-y = f (a , Transitivity α a y x a-lt-y y-lt-x) a-lt-y
    v : (a : ⟨ α ⟩) → a < z → a < y
    v a a-lt-z = g (a , Transitivity α a z x a-lt-z z-lt-x) a-lt-z
  <'-transitive : is-transitive _<'_
  <'-transitive = subtype-order-transitive α (λ - → - < x)
  β : Ordinal 𝓤
  β = ⟨β⟩ , _<'_ , <'-propvalued , <'-wellfounded , <'-extensional , <'-transitive


  ⟨γ⟩ : 𝓤 ̇
  ⟨γ⟩ = Σ y ꞉ ⟨ α ⟩ , x < y
  _<″_ : ⟨γ⟩ → ⟨γ⟩ → 𝓤 ̇
  _<″_ = subtype-order α (λ - → x < -)
  <″-propvalued : is-prop-valued _<″_
  <″-propvalued = subtype-order-propositional α (λ - → x < -)
  <″-wellfounded : is-well-founded _<″_
  <″-wellfounded = subtype-order-wellfounded α (λ - → x < -)
  <″-extensional : is-extensional _<″_
  <″-extensional (y , x-lt-y) (z , x-lt-z) f g = to-subtype-＝ (Prop-valuedness α x)
                                                               (Extensionality α y z u v)
   where
    u : (a : ⟨ α ⟩) → a < y → a < z
    u a a-lt-y = u' (tri a)
     where
      u' : (a < x) + (x ＝ a) + (x < a) → a < z
      u' (inl a-lt-x) = Transitivity α a x z a-lt-x x-lt-z
      u' (inr (inl refl)) = x-lt-z
      u' (inr (inr x-lt-a)) = f (a , x-lt-a) a-lt-y
    v : (a : ⟨ α ⟩) → a < z → a < y
    v a a-lt-z = v' (tri a)
     where
      v' : (a < x) + (x ＝ a) + (x < a) → a < y
      v' (inl a-lt-x) = Transitivity α a x y a-lt-x x-lt-y
      v' (inr (inl refl)) = x-lt-y
      v' (inr (inr x-lt-a)) = g (a , x-lt-a) a-lt-z
  <″-transitive : is-transitive _<″_
  <″-transitive = subtype-order-transitive α (λ - → x < -)
  γ : Ordinal 𝓤
  γ = ⟨γ⟩ , _<″_ , <″-propvalued , <″-wellfounded , <″-extensional , <″-transitive

  f' : (a : ⟨ α ⟩) → (a < x) + (x ＝ a) + (x < a) → ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩
  f' a (inl a-lt-x) = inl (a , a-lt-x)
  f' a (inr (inl e)) = inr (inl ⋆)
  f' a (inr (inr x-lt-a)) = inr (inr (a , x-lt-a))
  f : ⟨ α ⟩ → ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩
  f a = f' a (tri a)

  g : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ → ⟨ α ⟩
  g (inl (a , _)) = a
  g (inr (inl ⋆)) = x
  g (inr (inr (a , _))) = a

  f-equiv : is-order-equiv α (β +ₒ (𝟙ₒ +ₒ γ)) f
  f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
   where
    f-order-preserving' : (a b : ⟨ α ⟩)
                        → (tri-a : (a < x) + (x ＝ a) + (x < a))
                        → (tri-b : (b < x) + (x ＝ b) + (x < b))
                        → a < b → f' a tri-a ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ f' b tri-b
    f-order-preserving' a b (inl a-lt-x)       (inl b-lt-x)       a-lt-b = a-lt-b
    f-order-preserving' a _ (inl a-lt-x)       (inr (inl refl))   a-lt-_ = ⋆
    f-order-preserving' a b (inl a-lt-x)       (inr (inr x-lt-b)) a-lt-b = ⋆
    f-order-preserving' _ b (inr (inl refl))   (inl b-lt-x)       x-lt-b = 𝟘-elim (irrefl α x x-lt-x)
     where
      x-lt-x : x < x
      x-lt-x = (Transitivity α x b x x-lt-b b-lt-x)
    f-order-preserving' _ _ (inr (inl refl))   (inr (inl refl))   x-lt-x = 𝟘-elim (irrefl α x x-lt-x)
    f-order-preserving' a b (inr (inl refl))   (inr (inr x-lt-b)) a-lt-b = ⋆
    f-order-preserving' a b (inr (inr x-lt-a)) (inl b-lt-x)       a-lt-b = 𝟘-elim (irrefl α x x-lt-x)
     where
      x-lt-x : x < x
      x-lt-x = Transitivity α x a x x-lt-a (Transitivity α a b x a-lt-b b-lt-x)
    f-order-preserving' a _ (inr (inr x-lt-a)) (inr (inl refl))   a-lt-x = 𝟘-elim (irrefl α x x-lt-x)
     where
      x-lt-x : x < x
      x-lt-x = Transitivity α x a x x-lt-a a-lt-x
    f-order-preserving' a b (inr (inr x-lt-a)) (inr (inr x-lt-b)) a-lt-b = a-lt-b
    f-order-preserving : is-order-preserving α (β +ₒ (𝟙ₒ +ₒ γ)) f
    f-order-preserving a b = f-order-preserving' a b (tri a) (tri b)
    g-order-preserving : is-order-preserving (β +ₒ (𝟙ₒ +ₒ γ)) α g
    g-order-preserving (inl (a , a-lt-x)) (inl (b , b-lt-x))       a-lt-b = a-lt-b
    g-order-preserving (inl (a , a-lt-x)) (inr (inl ⋆))            ⋆      = a-lt-x
    g-order-preserving (inl (a , a-lt-x)) (inr (inr (b , x-lt-b))) ⋆      = a-lt-b
     where
      a-lt-b : a < b
      a-lt-b = Transitivity α a x b a-lt-x x-lt-b
    g-order-preserving (inr (inl ⋆))            (inr (inr (b , x-lt-b))) ⋆      = x-lt-b
    g-order-preserving (inr (inr (a , a-lt-x))) (inr (inr (b , x-lt-b))) a-lt-b = a-lt-b
    η' : (a : ⟨ α ⟩) → (tri-a : (a < x) + (x ＝ a) + (x < a))
       → g (f' a tri-a) ＝ a
    η' a (inl a-lt-x)       = refl
    η' _ (inr (inl refl))   = refl
    η' a (inr (inr x-lt-a)) = refl
    η : (a : ⟨ α ⟩) → g (f a) ＝ a
    η a = η' a (tri a)
    ϵ' : (w : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩) → (tri-gw : (g w < x) + (x ＝ g w) + (x < g w))
      → f' (g w) tri-gw ＝ w
    ϵ' (inl (a , a-lt-x)) (inl a-lt-x') = ap inl (to-subtype-＝ ((λ z → Prop-valuedness α z x)) refl)
    ϵ' (inl (_ , x-lt-x)) (inr (inl refl)) = 𝟘-elim (irrefl α x x-lt-x)
    ϵ' (inl (a , a-lt-x)) (inr (inr x-lt-a)) = 𝟘-elim (irrefl α x x-lt-x)
     where
      x-lt-x : x < x
      x-lt-x = Transitivity α x a x x-lt-a a-lt-x
    ϵ' (inr (inl ⋆)) (inl x-lt-x) = 𝟘-elim (irrefl α x x-lt-x)
    ϵ' (inr (inl ⋆)) (inr (inl e)) = refl
    ϵ' (inr (inl ⋆)) (inr (inr x-lt-x)) = 𝟘-elim (irrefl α x x-lt-x)
    ϵ' (inr (inr (b , x-lt-b))) (inl b-lt-x) = 𝟘-elim (irrefl α x x-lt-x)
     where
      x-lt-x : x < x
      x-lt-x = Transitivity α x b x x-lt-b b-lt-x
    ϵ' (inr (inr (_ , x-lt-x))) (inr (inl refl)) = 𝟘-elim (irrefl α x x-lt-x)
    ϵ' (inr (inr (b , x-lt-b))) (inr (inr x-lt-b')) =
        ap (inr ∘ inr) (to-subtype-＝ (Prop-valuedness α x) refl)
    ϵ : (w : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩) → f (g w) ＝ w
    ϵ w = ϵ' w (tri (g w))

  e : α ≃ₒ (β +ₒ (𝟙ₒ +ₒ γ))
  e = f , f-equiv

  f'x-spec : (tri-x : (x < x) + (x ＝ x) + (x < x)) → f' x tri-x ＝ inr (inl ⋆)
  f'x-spec (inl x-lt-x) = 𝟘-elim (irrefl α x x-lt-x)
  f'x-spec (inr (inl e)) = refl
  f'x-spec (inr (inr x-lt-x)) = 𝟘-elim (irrefl α x x-lt-x)

  e-spec : ≃ₒ-to-fun _ _ e x ＝ inr (inl ⋆)
  e-spec = f'x-spec (tri x)


isolation-to-trichotomy : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
    → x is-isolated-in α → x is-trichotomous-in α
isolation-to-trichotomy α x (β , γ , (f , f-equiv) , p) y = goal
 where
  f-order-reflecting : is-order-reflecting α (β +ₒ (𝟙ₒ +ₒ γ)) f
  f-order-reflecting = order-equivs-are-order-reflecting α (β +ₒ (𝟙ₒ +ₒ γ)) f f-equiv
  f-left-cancellable : left-cancellable f
  f-left-cancellable = equivs-are-lc f (pr₁ (pr₂ f-equiv))
  u : f y ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ f x → y ≺⟨ α ⟩ x
  u = f-order-reflecting y x
  v : f x ＝ f y → x ＝ y
  v = f-left-cancellable
  w : f x ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ f y → x ≺⟨ α ⟩ y
  w = f-order-reflecting x y
  tri-⋆ : (inr (inl ⋆)) is-trichotomous-in (β +ₒ (𝟙ₒ +ₒ γ))
  tri-⋆ (inl β) = inl ⋆
  tri-⋆ (inr (inl ⋆)) = (inr (inl refl))
  tri-⋆ (inr (inr γ)) = (inr (inr ⋆))
  tri-fx : (f x) is-trichotomous-in (β +ₒ (𝟙ₒ +ₒ γ))
  tri-fx = transport (λ w → w is-trichotomous-in (β +ₒ (𝟙ₒ +ₒ γ))) (p ⁻¹) tri-⋆
  goal : (y ≺⟨ α ⟩ x) + (x ＝ y) + (x ≺⟨ α ⟩ y)
  goal = +functor u (+functor v w) (tri-fx (f y))

\end{code}
