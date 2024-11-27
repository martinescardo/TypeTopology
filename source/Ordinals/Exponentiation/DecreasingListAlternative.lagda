Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
26 November 2024.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.DecreasingListAlternative
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

Detachable least element

\begin{code}

has-a-detachable-least-element : Ordinal 𝓤 → 𝓤 ̇
has-a-detachable-least-element α = Σ a₀ ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → is-decidable (x ＝ a₀)) ×
                                                  ((x : ⟨ α ⟩) → ¬ (x ＝ a₀) → a₀ ≺⟨ α ⟩ x)

has-a-detachable-least-element' : Ordinal 𝓤 → 𝓤 ̇
has-a-detachable-least-element' α = Σ a₀ ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → is-decidable (x ＝ a₀)) ×
                                                   is-minimal α a₀
                                                -- ((x : ⟨ α ⟩) → ¬ (x ≺⟨ α ⟩ a₀))

has-a-detachable-least-element'' : Ordinal 𝓤 → 𝓤 ̇
has-a-detachable-least-element'' α = (x : ⟨ α ⟩)
                                   → is-decidable ((y : ⟨ α ⟩) → ¬ (y ＝ x) → x ≺⟨ α ⟩ y)

has-a-detachable-least-element''' : Ordinal 𝓤 → 𝓤 ̇
has-a-detachable-least-element''' α = (x : ⟨ α ⟩) → is-decidable (is-minimal α x)


positive-sub-oridnal : (α : Ordinal 𝓤) → has-a-detachable-least-element α → Ordinal 𝓤
positive-sub-oridnal α (a₀ , a₀-dec , a₀-least) =
  ⟨α'⟩ , _<'_ , <'-propvalued , <'-wellfounded , <'-extensional , <'-transitive
 where
  ⟨α'⟩ = Σ a ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ a

  _<'_ : ⟨α'⟩ → ⟨α'⟩ → _
  _<'_ = subtype-order α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-propvalued : is-prop-valued _<'_
  <'-propvalued = subtype-order-propositional α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-wellfounded : is-well-founded _<'_
  <'-wellfounded = subtype-order-wellfounded α (λ - → a₀ ≺⟨ α ⟩ -)

  <'-extensional : is-extensional _<'_
  <'-extensional (x , p) (y , q) f g = to-subtype-＝ (λ x → Prop-valuedness α a₀ x)
                                                     (Extensionality α x y u v)
   where
    u : (z : ⟨ α ⟩) → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y
    u z r with a₀-dec z
    ... | inl refl = q
    ... | inr s = f (z , a₀-least z s) r
    v : (z : ⟨ α ⟩) → z ≺⟨ α ⟩ y → z ≺⟨ α ⟩ x
    v z r with a₀-dec z
    ... | inl refl = p
    ... | inr s = g (z , a₀-least z s) r

  <'-transitive : is-transitive _<'_
  <'-transitive = subtype-order-transitive α (λ - → a₀ ≺⟨ α ⟩ -)


_⁺[_] : (α : Ordinal 𝓤) → has-a-detachable-least-element α → Ordinal 𝓤
α ⁺[ d⊥ ] = positive-sub-oridnal α d⊥


has-a-detachable-least-element-lemma : (α : Ordinal 𝓤) (d⊥ : has-a-detachable-least-element α)
    → α ＝ 𝟙ₒ +ₒ (α ⁺[ d⊥ ])
has-a-detachable-least-element-lemma α d⊥@(a₀ , a₀-dec , a₀-least) = eq
 where
  α' = α ⁺[ d⊥ ]

  f' : (x : ⟨ α ⟩) → is-decidable (x ＝ a₀) → 𝟙 + ⟨ α' ⟩
  f' x (inl _) = inl ⋆
  f' x (inr q) = inr (x , a₀-least x q)

  f : ⟨ α ⟩ → 𝟙 + ⟨ α' ⟩
  f x = f' x (a₀-dec x)

  g : 𝟙 + ⟨ α' ⟩ → ⟨ α ⟩
  g (inl ⋆) = a₀
  g (inr (x , _)) = x

  f-equiv : is-order-equiv α (𝟙ₒ +ₒ α') f
  f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
   where
    f'-order-preserving : (x y : ⟨ α ⟩)
                        → (dx : is-decidable (x ＝ a₀))
                        → (dy : is-decidable (y ＝ a₀))
                        → x ≺⟨ α ⟩ y → f' x dx ≺⟨ 𝟙ₒ +ₒ α' ⟩ f' y dy
    f'-order-preserving .a₀ .a₀ (inl refl) (inl refl) r = 𝟘-elim (irrefl α a₀ r)
    f'-order-preserving .a₀ y (inl refl) (inr q) r = ⋆
    f'-order-preserving x .a₀ (inr p) (inl refl) r = 𝟘-elim (irrefl α x x<x)
     where
      x<x : x ≺⟨ α ⟩ x
      x<x = Transitivity α x a₀ x r (a₀-least x p)
    f'-order-preserving x y (inr p) (inr q) r = r
    f-order-preserving : is-order-preserving α (𝟙ₒ +ₒ α') f
    f-order-preserving x y = f'-order-preserving x y (a₀-dec x) (a₀-dec y)
    g-order-preserving : is-order-preserving (𝟙ₒ +ₒ α') α g
    g-order-preserving (inl ⋆) (inr (y , p)) q = p
    g-order-preserving (inr x) (inr (y , p)) q = q
    η' : (x : ⟨ α ⟩) → (d : is-decidable (x ＝ a₀)) → g (f' x d) ＝ x
    η' .a₀ (inl refl) = refl
    η' x (inr p) = refl
    η : (x : ⟨ α ⟩) → g (f x) ＝ x
    η x = η' x (a₀-dec x)
    ϵ' : (y : 𝟙 + ⟨ α' ⟩) → (d : is-decidable (g y ＝ a₀)) → f' (g y) d ＝ y
    ϵ' (inl ⋆) (inl e) = refl
    ϵ' (inl ⋆) (inr q) = 𝟘-elim (q refl)
    ϵ' (inr (.a₀ , p)) (inl refl) = 𝟘-elim (irrefl α a₀ p)
    ϵ' (inr (x , p)) (inr q) = ap inr (to-subtype-＝ ((λ x → Prop-valuedness α a₀ x)) refl)
    ϵ : (y : 𝟙 + ⟨ α' ⟩) → f (g y) ＝ y
    ϵ y = ϵ' y (a₀-dec (g y))

  eq : α ＝ 𝟙ₒ +ₒ α'
  eq = eqtoidₒ (ua _) fe' α (𝟙ₒ +ₒ α') (f , f-equiv)

\end{code}

Exponentiation whose base is an ordinal with a detachable least element

\begin{code}

exp : (α : Ordinal 𝓤) → has-a-detachable-least-element α → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
exp α d⊥ β = [𝟙+ (α ⁺[ d⊥ ]) ]^ β

exp-dle-0-spec : (α : Ordinal 𝓤) (d⊥ : has-a-detachable-least-element α)
    → exp α _ (𝟘ₒ {𝓥}) ＝ 𝟙ₒ
exp-dle-0-spec α d⊥ = exp-0-spec (α ⁺[ d⊥ ])

exp-dle-succ-spec : (α : Ordinal 𝓤) (d⊥ : has-a-detachable-least-element α)
    → (β : Ordinal 𝓤)
    → exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ α
exp-dle-succ-spec α d⊥ β = goal
 where
  fact : exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ (𝟙ₒ +ₒ (α ⁺[ d⊥ ]))
  fact = exp-succ-spec (α ⁺[ d⊥ ]) β
  eq : α ＝ 𝟙ₒ +ₒ (α ⁺[ d⊥ ])
  eq = has-a-detachable-least-element-lemma α d⊥
  goal : exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ α
  goal = transport (λ x → exp α d⊥ (β +ₒ 𝟙ₒ) ＝ exp α d⊥ β ×ₒ x) (eq ⁻¹) fact

exp-dle-sup-spec : (α : Ordinal 𝓤) (d⊥ : has-a-detachable-least-element α)
    → {I : 𝓤 ̇} → ∥ I ∥ → (β : I → Ordinal 𝓤)
    → sup (λ i → exp α _ (β i)) ＝ exp α _ (sup β)
exp-dle-sup-spec α d⊥ = exp-sup-spec (α ⁺[ d⊥ ])

\end{code}
