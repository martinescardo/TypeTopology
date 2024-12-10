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

open import Ordinals.Exponentiation.TrichotomyAndIsolation ua pt sr

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
  eq : ((x ＝ y) + (x ≺⟨ α ⟩ y)) → ((y ＝ x) + (y ≺⟨ α ⟩ x)) → x ＝ y
  eq (inl e) q' = e
  eq (inr u) (inl e) = e ⁻¹
  eq (inr u) (inr v) = 𝟘-elim (irrefl α x (Transitivity α x y x u v))
  goal : (x , p) ＝ (y , q)
  goal = to-Σ-＝ (eq (p y) (q x) , being-trichotomous-least-is-prop-valued α y _ _)

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
    u z r = cases (λ { refl → q })
                  (λ s → f (z , s) r)
                  (a₀-least z)
    v : (z : ⟨ α ⟩) → z ≺⟨ α ⟩ y → z ≺⟨ α ⟩ x
    v z r = cases (λ { refl → p })
                  (λ s → g (z , s) r)
                  (a₀-least z)

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

The above is a special case of decomposability for locally
trichotomous and least elements. Firstly, being trichotomous least is
equivalent to being trichotomous and least, as expected.

\begin{code}

is-trichotomous-least-implies-is-least : (α : Ordinal 𝓤) → (x : ⟨ α ⟩)
                                       → is-trichotomous-least α x
                                       → is-least α x
is-trichotomous-least-implies-is-least α x tri-least y z l = I (tri-least z)
 where
  I : (x ＝ z) + (x ≺⟨ α ⟩ z) → z ≺⟨ α ⟩ y
  I (inl refl) = 𝟘-elim (irrefl α x l)
  I (inr u) = 𝟘-elim (irrefl α x (Transitivity α x z x u l))

is-trichotomous-least-implies-is-locally-trichotomous
  : (α : Ordinal 𝓤) → (x : ⟨ α ⟩)
  → is-trichotomous-least α x
  → is-locally-trichotomous-at α x
is-trichotomous-least-implies-is-locally-trichotomous α x tri-least y =
 I (tri-least y)
  where
   I : (x ＝ y) + (x ≺⟨ α ⟩ y) → in-trichotomy (underlying-order α) y x
   I (inl e) = inr (inl (e ⁻¹))
   I (inr u) = inr (inr u)

is-trichotomous-and-least-implies-is-trichotomous-least
  : (α : Ordinal 𝓤) → (x : ⟨ α ⟩)
  → is-locally-trichotomous-at α x
  → is-least α x
  → is-trichotomous-least α x
is-trichotomous-and-least-implies-is-trichotomous-least α x tri least y =
 I (tri y)
  where
   I : (y ≺⟨ α ⟩ x) + (y ＝ x) + (x ≺⟨ α ⟩ y) → (x ＝ y) + (x ≺⟨ α ⟩ y)
   I (inl u) = 𝟘-elim (irrefl α y (least y y u))
   I (inr (inl e)) = inl (e ⁻¹)
   I (inr (inr u)) = inr u
\end{code}


\begin{code}
is-least-and-decomposable-implies-nothing-below
 : (α : Ordinal 𝓤) → (x : ⟨ α ⟩)
 → is-least α x
 → (β : Ordinal 𝓤)(γ : Ordinal 𝓤)
 → Σ e ꞉ α ≃ₒ (β +ₒ (𝟙ₒ +ₒ γ)) , ≃ₒ-to-fun _ _ e x ＝ inr (inl ⋆)
 → β ＝ 𝟘ₒ
is-least-and-decomposable-implies-nothing-below α x least β γ (e , p) =
 ⊴-antisym β 𝟘ₒ (≼-gives-⊴ β 𝟘ₒ II) (≼-gives-⊴ 𝟘ₒ β (𝟘ₒ-least β))
  where
   e-sim : is-simulation α (β +ₒ (𝟙ₒ +ₒ γ)) (≃ₒ-to-fun _ _ e)
   e-sim = order-equivs-are-simulations α
                                        (β +ₒ (𝟙ₒ +ₒ γ))
                                        (≃ₒ-to-fun α (β +ₒ (𝟙ₒ +ₒ γ)) e)
                                        (≃ₒ-to-fun-is-order-equiv α (β +ₒ (𝟙ₒ +ₒ γ)) e)

   I : ¬ ⟨ β ⟩
   I b = irrefl (β +ₒ (𝟙ₒ +ₒ γ)) (inl b) u''
    where
     u : x ≼⟨ α ⟩ (≃ₒ-to-fun⁻¹ _ _ e (inl b))
     u = least (≃ₒ-to-fun⁻¹ _ _ e (inl b))

     u' : inr (inl ⋆) ≼⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ (inl b)
     u' = transport₂ (λ - -' → - ≼⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ -')
                     p
                     (inverses-are-sections _ (≃ₒ-to-fun-is-equiv _ _ e) (inl b))
                     (simulations-are-monotone _ _ (≃ₒ-to-fun _ _ e) e-sim _ _ u)

     u'' : inl b ≺⟨ β +ₒ (𝟙ₒ +ₒ γ) ⟩ inl b
     u'' = ≺-≼-gives-≺ (β +ₒ (𝟙ₒ +ₒ γ)) (inl b) (inr (inl ⋆)) (inl b) ⋆ u'

   II : β ≼ 𝟘ₒ
   II = to-≼ (λ b → 𝟘-elim (I b))

trichotomous-least-to-decomposible' : (α : Ordinal 𝓤)
    → has-a-trichotomous-least-element α → Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α'
trichotomous-least-to-decomposible' α (x , tri-least) = (γ , III)
 where
  tri : is-locally-trichotomous-at α x
  tri = is-trichotomous-least-implies-is-locally-trichotomous α x tri-least
  least : is-least α x
  least = is-trichotomous-least-implies-is-least α x tri-least

  I : is-decomposed-at α x
  I = trichotomoy-to-isolation α x tri
  β = pr₁ I
  γ = pr₁ (pr₂ I)
  e = pr₁ (pr₂ (pr₂ I))
  p = pr₂ (pr₂ (pr₂ I))

  II : β ＝ 𝟘ₒ
  II = is-least-and-decomposable-implies-nothing-below α x least β γ (e , p)

  III = α               ＝⟨ eqtoidₒ (ua _) fe' α (β +ₒ (𝟙ₒ +ₒ γ)) e ⟩
        β +ₒ (𝟙ₒ +ₒ γ)  ＝⟨ ap (_+ₒ (𝟙ₒ +ₒ γ)) II ⟩
        𝟘ₒ +ₒ (𝟙ₒ +ₒ γ) ＝⟨ 𝟘ₒ-left-neutral (𝟙ₒ +ₒ γ) ⟩
        𝟙ₒ +ₒ γ         ∎

\end{code}


For any ordinal α that has a trichotomous least element, and for an
arbitrary ordinal β, we can define the exponential α^β. We first use
the trichotomous least element to decompose α.

\begin{code}

_⁺[_] : (α : Ordinal 𝓤) → has-a-trichotomous-least-element α → Ordinal 𝓤
α ⁺[ d⊥ ] = pr₁ (trichotomous-least-to-decomposible α d⊥)

_⁺[_]-part-of-decomposition : (α : Ordinal 𝓤)
                            → (d⊥ : has-a-trichotomous-least-element α)
                            → α ＝ 𝟙ₒ +ₒ α ⁺[ d⊥ ]
α ⁺[ d⊥ ]-part-of-decomposition = pr₂ (trichotomous-least-to-decomposible α d⊥)
\end{code}


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
  eq = α ⁺[ d⊥ ]-part-of-decomposition
  goal : exp α _ (β +ₒ 𝟙ₒ) ＝ exp α _ β ×ₒ α
  goal = transport (λ x → exp α d⊥ (β +ₒ 𝟙ₒ) ＝ exp α d⊥ β ×ₒ x) (eq ⁻¹) fact

exp-dle-sup-spec : (α : Ordinal 𝓤) (d⊥ : has-a-trichotomous-least-element α)
    → {I : 𝓤 ̇} → ∥ I ∥ → (β : I → Ordinal 𝓤)
    → sup (λ i → exp α _ (β i)) ＝ exp α _ (sup β)
exp-dle-sup-spec α d⊥ = exp-sup-spec (α ⁺[ d⊥ ])

\end{code}

