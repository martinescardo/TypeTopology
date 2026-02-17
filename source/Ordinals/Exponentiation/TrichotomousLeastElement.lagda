Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
26 November and 11 December 2024.

The main purpose of this file is to show that an ordinal α has a trichotomous
least element if and only if it can be decomposed as 𝟙ₒ +ₒ α' for a necessarily
unique ordinal α'.

The relevance of this result for our work lies in the fact that our concrete
construction of ordinal exponentiation only considers base ordinals with a
trichotomous least element.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.Exponentiation.TrichotomousLeastElement
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import MLTT.Plus-Properties
open import MLTT.Spartan

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt

\end{code}

Let α be an ordinal. Its order relation ≺ is locally trichotomous at
an element x if x ≺ y or x = y or y ≺ x for all y : α. Abusing
terminology, we will also say that x is trichotomous in α.

\begin{code}

is-locally-trichotomous-at : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-locally-trichotomous-at α x = is-trichotomous-element (underlying-order α) x

locally-trichotomous-at-is-prop : (α : Ordinal 𝓤) → (x : ⟨ α ⟩)
                                → is-prop (is-locally-trichotomous-at α x)
locally-trichotomous-at-is-prop α x =
 Π-is-prop fe' (in-trichotomy-is-prop (underlying-order α) fe
                                      (is-well-ordered α)
                                      x)
\end{code}

We say α is decomposed at x if there is an e: α = β + 𝟙 + γ for some
ordinals β and γ such that e maps x to in(⋆). Since such β and γ are
necessarily unique, if they exist, there is no difference between
formulating this property using Σ or ∃. We use Σ, for convenience.

\begin{code}

is-decomposed-at : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ⁺ ̇
is-decomposed-at {𝓤} α x =
  Σ β ꞉ Ordinal 𝓤 ,
  Σ γ ꞉ Ordinal 𝓤 ,
  Σ e ꞉ α ＝ β +ₒ (𝟙ₒ +ₒ γ) , Idtofunₒ e x ＝ inr (inl ⋆)

is-decomposed-at-is-prop : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
                         → is-prop (is-decomposed-at α x)
is-decomposed-at-is-prop {𝓤} α x (β , γ , e , p) (β' , γ' , e' , p') =
 to-subtype-＝
  (λ β (γ , e , p) (γ' , e' , p') →
    to-subtype-＝ (λ γ → Σ-is-prop
                          (the-type-of-ordinals-is-a-set (ua 𝓤) fe')
                          (λ e → underlying-type-is-set fe (β +ₒ (𝟙ₒ +ₒ γ))))
                  (III β γ γ' (e ⁻¹ ∙ e')))
    II
 where
  I : (δ ε : Ordinal 𝓥) → δ +ₒ (𝟙ₒ +ₒ ε) ↓ inr (inl ⋆) ＝ δ
  I δ ε = δ +ₒ (𝟙ₒ +ₒ ε) ↓ inr (inl ⋆) ＝⟨ +ₒ-↓-right (inl ⋆) ⁻¹ ⟩
          δ +ₒ (𝟙ₒ +ₒ ε ↓ inl ⋆)       ＝⟨ ap (δ +ₒ_) (+ₒ-↓-left ⋆) ⁻¹ ⟩
          δ +ₒ (𝟙ₒ ↓ ⋆)                ＝⟨ ap (δ +ₒ_)
                                              (prop-ordinal-↓ 𝟙-is-prop ⋆) ⟩
          δ +ₒ 𝟘ₒ                      ＝⟨ 𝟘ₒ-right-neutral δ ⟩
          δ                            ∎

  II = β                                ＝⟨ I β γ ⁻¹ ⟩
       β +ₒ (𝟙ₒ +ₒ γ) ↓ inr (inl ⋆)     ＝⟨ ap (β +ₒ (𝟙ₒ +ₒ γ) ↓_) p ⁻¹ ⟩
       β +ₒ (𝟙ₒ +ₒ γ) ↓ Idtofunₒ e x    ＝⟨ (Idtofunₒ-↓-lemma e) ⁻¹ ⟩
       α ↓ x                            ＝⟨ Idtofunₒ-↓-lemma e' ⟩
       β' +ₒ (𝟙ₒ +ₒ γ') ↓ Idtofunₒ e' x ＝⟨ ap (β' +ₒ (𝟙ₒ +ₒ γ') ↓_) p' ⟩
       β' +ₒ (𝟙ₒ +ₒ γ') ↓ inr (inl ⋆)   ＝⟨ I β' γ' ⟩
       β'                               ∎

  III : (β γ γ' : Ordinal 𝓤) → β +ₒ (𝟙ₒ +ₒ γ) ＝ β +ₒ (𝟙ₒ +ₒ γ') → γ ＝ γ'
  III β γ γ' r = +ₒ-left-cancellable (β +ₒ 𝟙ₒ) γ γ' r'
   where
    r' = (β +ₒ 𝟙ₒ) +ₒ γ  ＝⟨ +ₒ-assoc β 𝟙ₒ γ ⟩
         β +ₒ (𝟙ₒ +ₒ γ)  ＝⟨ r ⟩
         β +ₒ (𝟙ₒ +ₒ γ') ＝⟨ +ₒ-assoc β 𝟙ₒ γ' ⁻¹ ⟩
         (β +ₒ 𝟙ₒ) +ₒ γ' ∎

\end{code}

An element x is trichotomous in ordinal α iff α is decomposed at x.

\begin{code}

decomposed-at-to-trichotomy : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
                            → is-decomposed-at α x
                            → is-locally-trichotomous-at α x
decomposed-at-to-trichotomy α x (β , γ , e , p) y = III (II (f y))
 where
  f = Idtofunₒ e
  f-equiv = Idtofunₒ-is-order-equiv e

  I : is-locally-trichotomous-at (β +ₒ (𝟙ₒ +ₒ γ)) (inr (inl ⋆))
  I (inl b) = inr (inr ⋆)
  I (inr (inl ⋆)) = inr (inl refl)
  I (inr (inr c)) = inl ⋆

  II : is-locally-trichotomous-at (β +ₒ (𝟙ₒ +ₒ γ)) (f x)
  II = transport (is-locally-trichotomous-at (β +ₒ (𝟙ₒ +ₒ γ))) (p ⁻¹) I

  III : in-trichotomy (underlying-order (β +ₒ (𝟙ₒ +ₒ γ))) (f x) (f y)
      → in-trichotomy (underlying-order α) x y
  III = +functor (f-order-reflecting x y)
                 (+functor f-lc (f-order-reflecting y x))
   where
    f-order-reflecting : is-order-reflecting α (β +ₒ (𝟙ₒ +ₒ γ)) f
    f-order-reflecting =
     order-equivs-are-order-reflecting α (β +ₒ (𝟙ₒ +ₒ γ)) f f-equiv

    f-lc : left-cancellable f
    f-lc = equivs-are-lc f (order-equivs-are-equivs α (β +ₒ (𝟙ₒ +ₒ γ)) f-equiv)

trichotomy-to-decomposed-at : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
                            → is-locally-trichotomous-at α x
                            → is-decomposed-at α x
trichotomy-to-decomposed-at {𝓤} α x tri = β , γ , p , p-spec
 where
  _<_ = underlying-order α

  β : Ordinal 𝓤
  β = ⟨β⟩ , _<'_ ,
      <'-propvalued , <'-well-founded , <'-extensional , <'-transitive
   where
    ⟨β⟩ : 𝓤 ̇
    ⟨β⟩ = Σ y ꞉ ⟨ α ⟩ , y < x
    _<'_ : ⟨β⟩ → ⟨β⟩ → 𝓤 ̇
    _<'_ = subtype-order α (_< x)
    <'-propvalued : is-prop-valued _<'_
    <'-propvalued = subtype-order-is-prop-valued α (_< x)
    <'-well-founded : is-well-founded _<'_
    <'-well-founded = subtype-order-is-well-founded α (_< x)
    <'-transitive : is-transitive _<'_
    <'-transitive = subtype-order-is-transitive α (_< x)
    <'-extensional : is-extensional _<'_
    <'-extensional (y , k) (y' , k') f g =
     to-subtype-＝ (λ a → Prop-valuedness α a x) (Extensionality α y y' u v)
      where
       u : (a : ⟨ α ⟩) → a < y → a < y'
       u a l = f (a , Transitivity α a y x l k) l
       v : (a : ⟨ α ⟩) → a < y' → a < y
       v a l = g (a , Transitivity α a y' x l k') l

  γ : Ordinal 𝓤
  γ = ⟨γ⟩ , _<″_ ,
      <″-propvalued , <″-well-founded , <″-extensional , <″-transitive
   where
    ⟨γ⟩ : 𝓤 ̇
    ⟨γ⟩ = Σ y ꞉ ⟨ α ⟩ , x < y
    _<″_ : ⟨γ⟩ → ⟨γ⟩ → 𝓤 ̇
    _<″_ = subtype-order α (λ - → x < -)
    <″-propvalued : is-prop-valued _<″_
    <″-propvalued = subtype-order-is-prop-valued α (λ - → x < -)
    <″-well-founded : is-well-founded _<″_
    <″-well-founded = subtype-order-is-well-founded α (λ - → x < -)
    <″-transitive : is-transitive _<″_
    <″-transitive = subtype-order-is-transitive α (λ - → x < -)
    <″-extensional : is-extensional _<″_
    <″-extensional (y , k) (y' , k') f g =
     to-subtype-＝ (Prop-valuedness α x) (Extensionality α y y' u v)
      where
       u : (a : ⟨ α ⟩) → a < y → a < y'
       u a l = u' (tri a)
        where
         u' : (x < a) + (x ＝ a) + (a < x) → a < y'
         u' (inl v) = f (a , v) l
         u' (inr (inl refl)) = k'
         u' (inr (inr v)) = Transitivity α a x y' v k'
       v : (a : ⟨ α ⟩) → a < y' → a < y
       v a l = v' (tri a)
        where
         v' : (x < a) + (x ＝ a) + (a < x) → a < y
         v' (inl u) = g (a , u) l
         v' (inr (inl refl)) = k
         v' (inr (inr u)) = Transitivity α a x y u k

  f' : (a : ⟨ α ⟩) → (x < a) + (x ＝ a) + (a < x) → ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩
  f' a (inl l) = inr (inr (a , l))
  f' a (inr (inl e)) = inr (inl ⋆)
  f' a (inr (inr l)) = inl (a , l)
  f : ⟨ α ⟩ → ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩
  f a = f' a (tri a)

  g : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ → ⟨ α ⟩
  g (inl (a , _)) = a
  g (inr (inl ⋆)) = x
  g (inr (inr (a , _))) = a

  f-equiv : is-order-equiv α (β +ₒ (𝟙ₒ +ₒ γ)) f
  f-equiv = f-order-preserving ,
            (qinvs-are-equivs f (g , η , ϵ)) ,
            g-order-preserving
   where
    f-order-preserving : is-order-preserving α (β +ₒ (𝟙ₒ +ₒ γ)) f
    f-order-preserving a b = f-order-preserving' a b (tri a) (tri b)
     where
      f-order-preserving' : (a b : ⟨ α ⟩)
                          → (tri-a : (x < a) + (x ＝ a) + (a < x))
                          → (tri-b : (x < b) + (x ＝ b) + (b < x))
                          → a < b → f' a tri-a ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ f' b tri-b
      f-order-preserving' a b (inl l)          (inl u)          v = v
      f-order-preserving' a _ (inl l)          (inr (inl refl)) v =
       𝟘-elim (irrefl α a (Transitivity α a x a v l))
      f-order-preserving' a b (inl l)          (inr (inr u))    v =
       𝟘-elim (irrefl α a (Transitivity α a x a (Transitivity α a b x v u) l))
      f-order-preserving' _ b (inr (inl refl)) (inl u)          v = ⋆
      f-order-preserving' _ _ (inr (inl refl)) (inr (inl refl)) v =
       𝟘-elim (irrefl α x v)
      f-order-preserving' a b (inr (inl refl)) (inr (inr u))    v =
       𝟘-elim (irrefl α a (Transitivity α a b a v u))
      f-order-preserving' a b (inr (inr l))    (inl u)          v = ⋆
      f-order-preserving' a _ (inr (inr l))    (inr (inl refl)) v = ⋆
      f-order-preserving' a b (inr (inr l))    (inr (inr u))    v = v

    g-order-preserving : is-order-preserving (β +ₒ (𝟙ₒ +ₒ γ)) α g
    g-order-preserving (inl (a , _))       (inl (b , _))       v = v
    g-order-preserving (inl (a , l))       (inr (inl ⋆))       _ = l
    g-order-preserving (inl (a , l))       (inr (inr (b , u))) _ =
     Transitivity α a x b l u
    g-order-preserving (inr (inl _))       (inr (inr (b , u))) _ = u
    g-order-preserving (inr (inr (a , _))) (inr (inr (b , _))) v = v

    η : (a : ⟨ α ⟩) → g (f a) ＝ a
    η a = η' a (tri a)
     where
      η' : (a : ⟨ α ⟩)
         → (tri-a : (x < a) + (x ＝ a) + (a < x))
         → g (f' a tri-a) ＝ a
      η' a (inl u) = refl
      η' a (inr (inl refl)) = refl
      η' a (inr (inr u)) = refl

    ϵ : (w : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩) → f (g w) ＝ w
    ϵ w = ϵ' w (tri (g w))
     where
      ϵ' : (w : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩)
         → (tri-gw : (x < g w) + (x ＝ g w) + (g w < x))
         → f' (g w) tri-gw ＝ w
      ϵ' (inl (a , u)) (inl v) = 𝟘-elim (irrefl α x (Transitivity α x a x v u))
      ϵ' (inl (a , u)) (inr (inl refl)) = 𝟘-elim (irrefl α x u)
      ϵ' (inl (a , u)) (inr (inr v)) =
       ap inl (to-subtype-＝ (λ z → Prop-valuedness α z x) refl)
      ϵ' (inr (inl ⋆)) (inl v) = 𝟘-elim (irrefl α x v)
      ϵ' (inr (inl ⋆)) (inr (inl _)) = refl
      ϵ' (inr (inl ⋆)) (inr (inr v)) = 𝟘-elim (irrefl α x v)
      ϵ' (inr (inr (b , u))) (inl v) =
       ap (inr ∘ inr) (to-subtype-＝ (Prop-valuedness α x) refl)
      ϵ' (inr (inr (_ , u))) (inr (inl refl)) = 𝟘-elim (irrefl α x u)
      ϵ' (inr (inr (b , u))) (inr (inr v)) =
       𝟘-elim (irrefl α x (Transitivity α x b x u v))

  e : α ≃ₒ β +ₒ (𝟙ₒ +ₒ γ)
  e = f , f-equiv
  p : α ＝ β +ₒ (𝟙ₒ +ₒ γ)
  p = eqtoidₒ (ua 𝓤) fe' α (β +ₒ (𝟙ₒ +ₒ γ)) e

  f-spec : f x ＝ inr (inl ⋆)
  f-spec = f-spec' (tri x)
   where
    f-spec' : (tri-x : (x < x) + (x ＝ x) + (x < x))
            → f' x tri-x ＝ inr (inl ⋆)
    f-spec' (inl l) = 𝟘-elim (irrefl α x l)
    f-spec' (inr (inl _)) = refl
    f-spec' (inr (inr l)) = 𝟘-elim (irrefl α x l)

  p-spec = Idtofunₒ p x ＝⟨ happly (Idtofunₒ-eqtoidₒ (ua 𝓤) fe' e) x ⟩
           f x          ＝⟨ f-spec ⟩
           inr (inl ⋆)  ∎

\end{code}

Now we are interested in elements x of α which are both trichotomous
and the least element of α. These two properties can be combined into
a single property as follows: for each y : α, either x ＝ y or x ≺ y.

\begin{code}

is-trichotomous-least : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-trichotomous-least α x = (y : ⟨ α ⟩) → (x ＝ y) + (x ≺⟨ α ⟩ y)

being-trichotomous-least-is-prop
 : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-prop (is-trichotomous-least α x)
being-trichotomous-least-is-prop α x =
 Π-is-prop (fe _ _) (λ y → +-is-prop I (Prop-valuedness α x y) (II y))
  where
   I : is-set ⟨ α ⟩
   I = underlying-type-is-set fe α

   II : (y : ⟨ α ⟩) → x ＝ y → ¬ (x ≺⟨ α ⟩ y)
   II _ refl = irrefl α x

\end{code}

We prove that indeed being trichotomous least is equivalent to being
trichotomous and least.

\begin{code}

is-trichotomous-least-implies-is-least : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
                                       → is-trichotomous-least α x
                                       → is-least α x
is-trichotomous-least-implies-is-least α x tri-least y z l = I (tri-least z)
 where
  I : (x ＝ z) + (x ≺⟨ α ⟩ z) → z ≺⟨ α ⟩ y
  I (inl refl) = 𝟘-elim (irrefl α x l)
  I (inr u) = 𝟘-elim (irrefl α x (Transitivity α x z x u l))

is-trichotomous-least-implies-is-locally-trichotomous
  : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
  → is-trichotomous-least α x
  → is-locally-trichotomous-at α x
is-trichotomous-least-implies-is-locally-trichotomous α x tri-least y =
 I (tri-least y)
  where
   I : (x ＝ y) + (x ≺⟨ α ⟩ y) → in-trichotomy (underlying-order α) x y
   I (inl e) = inr (inl e)
   I (inr u) = inl u

is-trichotomous-and-least-implies-is-trichotomous-least
  : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
  → is-locally-trichotomous-at α x
  → is-least α x
  → is-trichotomous-least α x
is-trichotomous-and-least-implies-is-trichotomous-least α x tri least y =
 I (tri y)
  where
   I : (x ≺⟨ α ⟩ y) + (x ＝ y) + (y ≺⟨ α ⟩ x) → (x ＝ y) + (x ≺⟨ α ⟩ y)
   I (inl u) = inr u
   I (inr (inl e)) = inl e
   I (inr (inr u)) = 𝟘-elim (irrefl α y (least y y u))

\end{code}

We now show that α having a trichotomous least element is equivalent to α being
decomposable as α = 𝟙 + α' for some necessarily unique ordinal α'.

\begin{code}

is-decomposable-into-one-plus : Ordinal 𝓤 → 𝓤 ⁺ ̇
is-decomposable-into-one-plus {𝓤} α = Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α'

has-trichotomous-least-element : Ordinal 𝓤 → 𝓤 ̇
has-trichotomous-least-element α = Σ x ꞉ ⟨ α ⟩ , is-trichotomous-least α x

being-decomposable-into-one-plus-is-prop
 : (α : Ordinal 𝓤) → is-prop (is-decomposable-into-one-plus α)
being-decomposable-into-one-plus-is-prop {𝓤} α (α' , p) (α″ , q) = II
 where
  I : α' ＝ α″
  I = +ₒ-left-cancellable 𝟙ₒ α' α″ (p ⁻¹ ∙ q)

  II : (α' , p) ＝ (α″ , q)
  II = to-subtype-＝ (λ γ → the-type-of-ordinals-is-a-set (ua 𝓤) fe') I

having-trichotomous-least-element-is-prop
 : (α : Ordinal 𝓤) → is-prop (has-trichotomous-least-element α)
having-trichotomous-least-element-is-prop α (x , p) (y , q) = II
 where
  I : ((x ＝ y) + (x ≺⟨ α ⟩ y)) → ((y ＝ x) + (y ≺⟨ α ⟩ x)) → x ＝ y
  I (inl e) q' = e
  I (inr u) (inl e) = e ⁻¹
  I (inr u) (inr v) = 𝟘-elim (irrefl α x (Transitivity α x y x u v))

  II : (x , p) ＝ (y , q)
  II = to-subtype-＝ (being-trichotomous-least-is-prop α) (I (p y) (q x))

decomposable-to-trichotomous-least
  : (α : Ordinal 𝓤)
  → is-decomposable-into-one-plus α
  → has-trichotomous-least-element α
decomposable-to-trichotomous-least α (γ , refl) = (inl ⋆ , III)
 where
  I : is-least (𝟙ₒ +ₒ γ) (inl ⋆)
  I _ (inl ⋆) l = 𝟘-elim l
  I _ (inr c) l = 𝟘-elim l

  II : is-locally-trichotomous-at (𝟙ₒ +ₒ γ) (inl ⋆)
  II = decomposed-at-to-trichotomy α (inl ⋆) (𝟘ₒ , γ , p , p-spec)
   where
    p : 𝟙ₒ +ₒ γ ＝ 𝟘ₒ +ₒ (𝟙ₒ +ₒ γ)
    p = (𝟘ₒ-left-neutral (𝟙ₒ +ₒ γ)) ⁻¹

    p-spec : Idtofunₒ p (inl ⋆) ＝ inr (inl ⋆)
    p-spec = ↓-lc (𝟘ₒ +ₒ (𝟙ₒ +ₒ γ)) (Idtofunₒ p (inl ⋆)) (inr (inl ⋆)) (e ⁻¹)
     where
      e = 𝟘ₒ +ₒ (𝟙ₒ +ₒ γ) ↓ inr (inl ⋆)        ＝⟨ (+ₒ-↓-right (inl ⋆)) ⁻¹ ⟩
          𝟘ₒ +ₒ (𝟙ₒ +ₒ γ ↓ inl ⋆)              ＝⟨ 𝟘ₒ-left-neutral _ ⟩
          𝟙ₒ +ₒ γ ↓ inl ⋆                      ＝⟨ Idtofunₒ-↓-lemma p ⟩
          𝟘ₒ +ₒ (𝟙ₒ +ₒ γ) ↓ Idtofunₒ p (inl ⋆) ∎

  III : is-trichotomous-least (𝟙ₒ +ₒ γ) (inl ⋆)
  III = is-trichotomous-and-least-implies-is-trichotomous-least α (inl ⋆) II I

\end{code}

In the converse direction, our strategy is to reuse our previous
result that trichotomous elements x : α decomposes α as α = β + 𝟙 + γ;
we show that if x is also least, then in fact β = 𝟘.

\begin{code}

is-least-and-decomposable-implies-nothing-below
 : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
 → is-least α x
 → ((β , γ , e , p) : is-decomposed-at α x)
 → β ＝ 𝟘ₒ
is-least-and-decomposable-implies-nothing-below α x least (β , γ , e , p) =
 ⊴-antisym β 𝟘ₒ (≼-gives-⊴ β 𝟘ₒ II) (≼-gives-⊴ 𝟘ₒ β (𝟘ₒ-least β))
  where
   e-sim : is-simulation α (β +ₒ (𝟙ₒ +ₒ γ)) (Idtofunₒ e)
   e-sim = order-equivs-are-simulations
            α (β +ₒ (𝟙ₒ +ₒ γ))
            (Idtofunₒ e) (Idtofunₒ-is-order-equiv e)
   e-equiv : is-equiv (Idtofunₒ e)
   e-equiv = order-equivs-are-equivs α (β +ₒ (𝟙ₒ +ₒ γ))
                                     (Idtofunₒ-is-order-equiv e)
   e⁻¹ : ⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ → ⟨ α ⟩
   e⁻¹ = inverse (Idtofunₒ e) e-equiv

   I : ¬ ⟨ β ⟩
   I b = irrefl (β +ₒ (𝟙ₒ +ₒ γ)) (inl b) u'''
    where
     u : x ≼⟨ α ⟩ e⁻¹ (inl b)
     u = least (e⁻¹ (inl b))

     u' : Idtofunₒ e x ≼⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ Idtofunₒ e (e⁻¹ (inl b))
     u' = simulations-are-monotone _ _ (Idtofunₒ e) e-sim x (e⁻¹ (inl b)) u

     u'' : inr (inl ⋆) ≼⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ (inl b)
     u'' = transport₂ (λ - -' → - ≼⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ -')
                      p
                      (inverses-are-sections (Idtofunₒ e) e-equiv (inl b))
                      u'

     u''' : inl b ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ inl b
     u''' = ≺-≼-gives-≺ (β +ₒ (𝟙ₒ +ₒ γ)) (inl b) (inr (inl ⋆)) (inl b) ⋆ u''

   II : β ≼ 𝟘ₒ
   II = to-≼ (λ b → 𝟘-elim (I b))

trichotomous-least-to-decomposable
  : (α : Ordinal 𝓤)
  → has-trichotomous-least-element α
  → is-decomposable-into-one-plus α
trichotomous-least-to-decomposable α (x , tri-least) = (γ , III)
 where
  tri : is-locally-trichotomous-at α x
  tri = is-trichotomous-least-implies-is-locally-trichotomous α x tri-least
  least : is-least α x
  least = is-trichotomous-least-implies-is-least α x tri-least

  I : is-decomposed-at α x
  I = trichotomy-to-decomposed-at α x tri
  β = pr₁ I
  γ = pr₁ (pr₂ I)
  e = pr₁ (pr₂ (pr₂ I))
  p = pr₂ (pr₂ (pr₂ I))

  II : β ＝ 𝟘ₒ
  II = is-least-and-decomposable-implies-nothing-below α x least I

  III = α               ＝⟨ e ⟩
        β +ₒ (𝟙ₒ +ₒ γ)  ＝⟨ ap (_+ₒ (𝟙ₒ +ₒ γ)) II ⟩
        𝟘ₒ +ₒ (𝟙ₒ +ₒ γ) ＝⟨ 𝟘ₒ-left-neutral (𝟙ₒ +ₒ γ) ⟩
        𝟙ₒ +ₒ γ         ∎

\end{code}

The following provides an interface to the subordinal of positive elements in
case we are given an ordinal with a trichotomous least element.

\begin{code}

_⁺[_] : (α : Ordinal 𝓤) → has-trichotomous-least-element α → Ordinal 𝓤
α ⁺[ d⊥ ] = pr₁ (trichotomous-least-to-decomposable α d⊥)

_⁺[_]-part-of-decomposition : (α : Ordinal 𝓤)
                            → (d⊥ : has-trichotomous-least-element α)
                            → α ＝ 𝟙ₒ +ₒ α ⁺[ d⊥ ]
α ⁺[ d⊥ ]-part-of-decomposition = pr₂ (trichotomous-least-to-decomposable α d⊥)

module _
        (α : Ordinal 𝓤)
        (h@(⊥ , _) : has-trichotomous-least-element α)
       where

 ⁺-is-subtype-of-positive-elements : ⟨ α ⁺[ h ] ⟩ ＝ (Σ a ꞉ ⟨ α ⟩ , ⊥ ≺⟨ α ⟩ a)
 ⁺-is-subtype-of-positive-elements = refl

 ⁺-underlying-element : ⟨ α ⁺[ h ] ⟩ → ⟨ α ⟩
 ⁺-underlying-element = pr₁

 to-⁺-＝ : {x y : ⟨ α ⁺[ h ] ⟩}
         → ⁺-underlying-element x ＝ ⁺-underlying-element y
         → x ＝ y
 to-⁺-＝ e = to-subtype-＝ (Prop-valuedness α ⊥) e

\end{code}

We record that any ordinal with a trichotomous least element is at
least as big as 𝟙ₒ.

\begin{code}

trichotomous-least-element-gives-𝟙ₒ-⊴ : (α : Ordinal 𝓤)
                                      → has-trichotomous-least-element α
                                      → 𝟙ₒ ⊴ α
trichotomous-least-element-gives-𝟙ₒ-⊴ α h =
 transport⁻¹ (𝟙ₒ ⊴_) (α ⁺[ h ]-part-of-decomposition) (+ₒ-left-⊴ 𝟙ₒ (α ⁺[ h ]))

\end{code}

Classically, any ordinal is either 𝟘ₒ, or it has a trichotomous least element.

\begin{code}

has-trichotomous-least-element-or-is-zero : Ordinal 𝓤 → 𝓤 ⁺ ̇
has-trichotomous-least-element-or-is-zero α =
 has-trichotomous-least-element α + (α ＝ 𝟘ₒ)

Has-trichotomous-least-element-or-is-zero : 𝓤 ⁺ ̇
Has-trichotomous-least-element-or-is-zero {𝓤} =
 (α : Ordinal 𝓤) → has-trichotomous-least-element-or-is-zero α

EM-gives-Has-trichotomous-least-element-or-is-zero
 : EM 𝓤
 → Has-trichotomous-least-element-or-is-zero {𝓤}
EM-gives-Has-trichotomous-least-element-or-is-zero em α =
 II (em ∥ ⟨ α ⟩ ∥ ∥∥-is-prop)
  where
   open import Ordinals.WellOrderingTaboo fe' pe
   open ClassicalWellOrder pt

   has-minimal = Σ x₀ ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → ¬ (x ≺⟨ α ⟩ x₀))

   I : ∥ ⟨ α ⟩ ∥ → has-minimal
   I i = pr₁ I' , (λ x → pr₂ (pr₂ I') x ⋆)
    where
     I' : Σ x₀ ꞉ ⟨ α ⟩ , 𝟙 × ((x : ⟨ α ⟩) → 𝟙 → ¬ (x ≺⟨ α ⟩ x₀))
     I' = well-order-gives-minimal (underlying-order α) em (is-well-ordered α)
           (λ _ → 𝟙) (λ _ → 𝟙-is-prop) (∥∥-functor (λ x → x , ⋆) i)

   II : is-decidable ∥ ⟨ α ⟩ ∥ → has-trichotomous-least-element-or-is-zero α
   II (inl  i) = inl (x₀ ,
                      τ (classical-well-orders-are-uniquely-trichotomous
                          (underlying-order α)
                          (inductive-well-order-is-classical
                            (underlying-order α) em (is-well-ordered α))))
    where
     x₀ = pr₁ (I i)
     x₀-is-minimal = pr₂ (I i)

     τ : ((x y : ⟨ α ⟩) → is-singleton ((x ≺⟨ α ⟩ y) + (x ＝ y) + (y ≺⟨ α ⟩ x)))
       → is-trichotomous-least α x₀
     τ σ x = κ (center (σ x₀ x))
      where
       κ : (x₀ ≺⟨ α ⟩ x) + (x₀ ＝ x) + (x ≺⟨ α ⟩ x₀)
         → (x₀ ＝ x) + (x₀ ≺⟨ α ⟩ x)
       κ (inl u)       = inr u
       κ (inr (inl e)) = inl e
       κ (inr (inr v)) = 𝟘-elim (x₀-is-minimal x v)
   II (inr ni) = inr (⊴-antisym α 𝟘ₒ
                       (to-⊴ α 𝟘ₒ λ x → 𝟘-elim (ni ∣ x ∣))
                       (≼-gives-⊴ 𝟘ₒ α (𝟘ₒ-least α)))

\end{code}
