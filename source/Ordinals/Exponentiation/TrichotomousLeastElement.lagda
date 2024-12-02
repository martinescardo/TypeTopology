Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
26 November 2024.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.TrichotomousLeastElement
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
an element x if y ≺ x or x = y or x ≺ y for all y : α, and we say x is
trichotomous. Furthermore, x is called a trichotomous least element if
x = y or x ≺ y for all y : α.

\begin{code}

is-trichotomous-least : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-trichotomous-least α x = (y : ⟨ α ⟩) → (x ＝ y) + (x ≺⟨ α ⟩ y)

has-a-trichotomous-least-element : Ordinal 𝓤 → 𝓤 ̇
has-a-trichotomous-least-element α = Σ x ꞉ ⟨ α ⟩ , is-trichotomous-least α x

being-trichotomous-least-is-prop-valued : (α : Ordinal 𝓤) (x : ⟨ α ⟩)
    → is-prop (is-trichotomous-least α x)
being-trichotomous-least-is-prop-valued α x = Π-is-prop (fe _ _) in-trichotomous-least-is-prop
 where
  ⟨α⟩-is-set : is-set ⟨ α ⟩
  ⟨α⟩-is-set = well-ordered-types-are-sets (underlying-order α) fe (is-well-ordered α)
  irrefl-fact : (y : ⟨ α ⟩) → x ＝ y → ¬ (x ≺⟨ α ⟩ y)
  irrefl-fact .x refl = irrefl α x
  in-trichotomous-least-is-prop : (y : ⟨ α ⟩) → is-prop ((x ＝ y) + (x ≺⟨ α ⟩ y))
  in-trichotomous-least-is-prop y = +-is-prop ⟨α⟩-is-set (Prop-valuedness α x y) (irrefl-fact y)

having-a-trichotomous-least-element-is-prop-valued : (α : Ordinal 𝓤)
    → is-prop (has-a-trichotomous-least-element α)
having-a-trichotomous-least-element-is-prop-valued α (x , p) (y , q) = goal
 where
  eq : x ＝ y
  eq with (p y) with (q x)
  eq | inl e | _ = e
  eq | inr u | inl e = e ⁻¹
  eq | inr u | inr v = 𝟘-elim (irrefl α x (Transitivity α x y x u v))
  goal : (x , p) ＝ (y , q)
  goal = to-Σ-＝ (eq , being-trichotomous-least-is-prop-valued α y _ _)

\end{code}

An ordinal α having a trichotomous least element is equivalent to
being decomposable as α = 𝟙 + α' for some ordinal α'.

\begin{code}

is-decomposable-into-one-plus : Ordinal 𝓤 → 𝓤 ⁺ ̇
is-decomposable-into-one-plus {𝓤} α = Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α'

being-decomposable-into-one-plus-is-prop-valued : (α : Ordinal 𝓤)
    → is-prop (is-decomposable-into-one-plus α)
being-decomposable-into-one-plus-is-prop-valued {𝓤} α (α' , p) (α″ , q) = goal
 where
  eq : α' ＝ α″
  eq = +ₒ-left-cancellable 𝟙ₒ α' α″ (p ⁻¹ ∙ q)
  Ordinal-is-set : is-set (Ordinal 𝓤)
  Ordinal-is-set = well-ordered-types-are-sets _⊲_ fe ⊲-is-well-order
  goal : (α' , p) ＝ (α″ , q)
  goal = to-Σ-＝ (eq , Ordinal-is-set _ _)


trichotomous-least-to-decomposible : (α : Ordinal 𝓤)
    → has-a-trichotomous-least-element α → Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α'
trichotomous-least-to-decomposible {𝓤} α (a₀ , a₀-least) = α' , eq
 where
  ⟨α'⟩ : 𝓤 ̇
  ⟨α'⟩ = Σ a ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ a

  _<'_ : ⟨α'⟩ → ⟨α'⟩ → _
  _<'_ = subtype-order α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-propvalued : is-prop-valued _<'_
  <'-propvalued = subtype-order-propositional α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-wellfounded : is-well-founded _<'_
  <'-wellfounded = subtype-order-wellfounded α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-extensional : is-extensional _<'_
  <'-extensional (x , p) (y , q) f g = to-subtype-＝ (Prop-valuedness α a₀)
                                                     (Extensionality α x y u v)
   where
    u : (z : ⟨ α ⟩) → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y
    u z r with a₀-least z
    ... | inl refl = q
    ... | inr s = f (z , s) r
    v : (z : ⟨ α ⟩) → z ≺⟨ α ⟩ y → z ≺⟨ α ⟩ x
    v z r with a₀-least z
    ... | inl refl = p
    ... | inr s = g (z , s) r

  <'-transitive : is-transitive _<'_
  <'-transitive = subtype-order-transitive α (λ - → a₀ ≺⟨ α ⟩ -)

  α' : Ordinal 𝓤
  α' = ⟨α'⟩ , _<'_ , <'-propvalued , <'-wellfounded , <'-extensional , <'-transitive

  f' : (x : ⟨ α ⟩) → (a₀ ＝ x) + (a₀ ≺⟨ α ⟩ x) → 𝟙 + ⟨ α' ⟩
  f' x (inl _) = inl ⋆
  f' x (inr q) = inr (x , q)

  f : ⟨ α ⟩ → 𝟙 + ⟨ α' ⟩
  f x = f' x (a₀-least x)

  g : 𝟙 + ⟨ α' ⟩ → ⟨ α ⟩
  g (inl ⋆) = a₀
  g (inr (x , _)) = x

  f-equiv : is-order-equiv α (𝟙ₒ +ₒ α') f
  f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
   where
    f'-order-preserving : (x y : ⟨ α ⟩)
                        → (dx : (a₀ ＝ x) + (a₀ ≺⟨ α ⟩ x))
                        → (dy : (a₀ ＝ y) + (a₀ ≺⟨ α ⟩ y))
                        → x ≺⟨ α ⟩ y → f' x dx ≺⟨ 𝟙ₒ +ₒ α' ⟩ f' y dy
    f'-order-preserving .a₀ .a₀ (inl refl) (inl refl) r = 𝟘-elim (irrefl α a₀ r)
    f'-order-preserving .a₀ y (inl refl) (inr q) r = ⋆
    f'-order-preserving x .a₀ (inr p) (inl refl) r = 𝟘-elim (irrefl α x (Transitivity α x a₀ x r p))
    f'-order-preserving x y (inr p) (inr q) r = r
    f-order-preserving : is-order-preserving α (𝟙ₒ +ₒ α') f
    f-order-preserving x y = f'-order-preserving x y (a₀-least x) (a₀-least y)
    g-order-preserving : is-order-preserving (𝟙ₒ +ₒ α') α g
    g-order-preserving (inl ⋆) (inr (y , p)) q = p
    g-order-preserving (inr x) (inr (y , p)) q = q
    η' : (x : ⟨ α ⟩) → (d : (a₀ ＝ x) + (a₀ ≺⟨ α ⟩ x)) → g (f' x d) ＝ x
    η' .a₀ (inl refl) = refl
    η' x (inr p) = refl
    η : (x : ⟨ α ⟩) → g (f x) ＝ x
    η x = η' x (a₀-least x)
    ϵ' : (y : 𝟙 + ⟨ α' ⟩) → (d : (a₀ ＝ g y) + (a₀ ≺⟨ α ⟩ g y)) → f' (g y) d ＝ y
    ϵ' (inl ⋆) (inl e) = refl
    ϵ' (inl ⋆) (inr q) = 𝟘-elim (irrefl α a₀ q)
    ϵ' (inr (.a₀ , p)) (inl refl) = 𝟘-elim (irrefl α a₀ p)
    ϵ' (inr (x , p)) (inr q) = ap inr (to-subtype-＝ ((λ x → Prop-valuedness α a₀ x)) refl)
    ϵ : (y : 𝟙 + ⟨ α' ⟩) → f (g y) ＝ y
    ϵ y = ϵ' y (a₀-least (g y))

  eq : α ＝ 𝟙ₒ +ₒ α'
  eq = eqtoidₒ (ua _) fe' α (𝟙ₒ +ₒ α') (f , f-equiv)

{-
decomposible-to-trichotomous-least : (α : Ordinal 𝓤)
    → (Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α') → has-a-trichotomous-least-element α
decomposible-to-trichotomous-least α (α' , e) = {!!}
-}

\end{code}


\begin{code}

_⁺[_] : (α : Ordinal 𝓤) → has-a-trichotomous-least-element α → Ordinal 𝓤
α ⁺[ d⊥ ] = pr₁ (trichotomous-least-to-decomposible α d⊥)

\end{code}

For any ordinal α that has a trichotomous least element, and for any
arbitrary ordinal β, we can define the eponentaital α^β.

\begin{code}

exp : (α : Ordinal 𝓤) → has-a-trichotomous-least-element α → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
exp α d⊥ β = [𝟙+ (α ⁺[ d⊥ ]) ]^ β

exp-dle-0-spec : (α : Ordinal 𝓤) (d⊥ : has-a-trichotomous-least-element α)
    → exp α _ (𝟘ₒ {𝓥}) ＝ 𝟙ₒ
exp-dle-0-spec α d⊥ = exp-0-spec (α ⁺[ d⊥ ])

exp-dle-succ-spec : (α : Ordinal 𝓤) (d⊥ : has-a-trichotomous-least-element α)
    → (β : Ordinal 𝓤)
    → exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ α
exp-dle-succ-spec α d⊥ β = goal
 where
  fact : exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ (𝟙ₒ +ₒ (α ⁺[ d⊥ ]))
  fact = exp-succ-spec (α ⁺[ d⊥ ]) β
  eq : α ＝ 𝟙ₒ +ₒ (α ⁺[ d⊥ ])
  eq = pr₂ (trichotomous-least-to-decomposible α d⊥)
  goal : exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ α
  goal = transport (λ x → exp α d⊥ (β +ₒ 𝟙ₒ) ＝ exp α d⊥ β ×ₒ x) (eq ⁻¹) fact

exp-dle-sup-spec : (α : Ordinal 𝓤) (d⊥ : has-a-trichotomous-least-element α)
    → {I : 𝓤 ̇} → ∥ I ∥ → (β : I → Ordinal 𝓤)
    → sup (λ i → exp α _ (β i)) ＝ exp α _ (sup β)
exp-dle-sup-spec α d⊥ = exp-sup-spec (α ⁺[ d⊥ ])

\end{code}
