Tom de Jong, 3 - 5 March 2020

As suggested by Martin Escardo.

The (usual) order on the dyadic rationals

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import DyadicsInductive.Dyadics
open import UF.Subsingletons

\end{code}

We inductively define an order ≺ on 𝔻 and prove that it is transitive and
linear.

We also show that is is "dense" and "has no endpoints", but formulated using Σ
rather than ∃. Although the proper formulation would use ∃ (to ensure that being
dense and having no endpoints is property, rather than structure), we still
prove the Σ-versions for two reasons:
- we can easily prove them and derive the ∃-versions from them;
- so that this module does not depend on propositional truncation.

\begin{code}

module DyadicsInductive.DyadicOrder where

\end{code}

We defined ≺ by using the translation (from 𝔻 to (-1,1)) as set out in Dyadic.

\begin{code}

_≺_ : 𝔻 → 𝔻 → 𝓤₀ ̇
middle  ≺ middle  = 𝟘
middle  ≺ left y  = 𝟘
middle  ≺ right y = 𝟙
left x  ≺ middle  = 𝟙
left x  ≺ left y  = x ≺ y
left x  ≺ right y = 𝟙
right x ≺ middle  = 𝟘
right x ≺ left y  = 𝟘
right x ≺ right y = x ≺ y

\end{code}

Monotonicity of left and right holds by definition (so we will never call these
lemmas), but we record them here for clarity.

\begin{code}

left-monotone : {x y : 𝔻} → x ≺ y → left x ≺ left y
left-monotone = id

right-monotone : {x y : 𝔻} → x ≺ y → right x ≺ right y
right-monotone = id

\end{code}

\begin{code}

≺-is-prop-valued : (x y : 𝔻) → is-prop (x ≺ y)
≺-is-prop-valued middle    middle    = 𝟘-is-prop
≺-is-prop-valued middle    (left y)  = 𝟘-is-prop
≺-is-prop-valued middle    (right y) = 𝟙-is-prop
≺-is-prop-valued (left x)  middle    = 𝟙-is-prop
≺-is-prop-valued (left x)  (left y)  = ≺-is-prop-valued x y
≺-is-prop-valued (left x)  (right y) = 𝟙-is-prop
≺-is-prop-valued (right x) middle    = 𝟘-is-prop
≺-is-prop-valued (right x) (left y)  = 𝟘-is-prop
≺-is-prop-valued (right x) (right y) = ≺-is-prop-valued x y

≺-is-transitive : (x y z : 𝔻) → x ≺ y → y ≺ z → x ≺ z
≺-is-transitive middle middle z = 𝟘-induction
≺-is-transitive middle (left y) middle = 𝟘-induction
≺-is-transitive middle (left y) (left z) = 𝟘-induction
≺-is-transitive middle (left y) (right z) = 𝟘-induction
≺-is-transitive middle (right y) middle _ = id
≺-is-transitive middle (right y) (left z) _ = id
≺-is-transitive middle (right y) (right z) _ _ = ⋆
≺-is-transitive (left x) middle middle _ _ = ⋆
≺-is-transitive (left x) middle (left z) _ = 𝟘-induction
≺-is-transitive (left x) middle (right z) _ = id
≺-is-transitive (left x) (left y) middle _ = id
≺-is-transitive (left x) (left y) (left z) = ≺-is-transitive x y z
≺-is-transitive (left x) (left y) (right z) _ = id
≺-is-transitive (left x) (right y) middle _ _ = ⋆
≺-is-transitive (left x) (right y) (left z) _ = 𝟘-induction
≺-is-transitive (left x) (right y) (right z) _ _ = ⋆
≺-is-transitive (right x) middle z = 𝟘-induction
≺-is-transitive (right x) (left y) z = 𝟘-induction
≺-is-transitive (right x) (right y) middle _ = id
≺-is-transitive (right x) (right y) (left z) _ = id
≺-is-transitive (right x) (right y) (right z) = ≺-is-transitive x y z

≺-is-linear : (x y : 𝔻) → x ≠ y → x ≺ y + y ≺ x
≺-is-linear middle middle p = 𝟘-induction (p refl)
≺-is-linear middle (left y) _ = inr ⋆
≺-is-linear middle (right y) _ = inl ⋆
≺-is-linear (left x) middle _ = inl ⋆
≺-is-linear (left x) (left y) lx≠ly = ≺-is-linear x y x≠y
 where
  x≠y : x ≠ y
  x≠y = contrapositive (ap left) lx≠ly
≺-is-linear (left x) (right y) _ = inl ⋆
≺-is-linear (right x) middle _ = inr ⋆
≺-is-linear (right x) (left y) _ = inr ⋆
≺-is-linear (right x) (right y) rx≠ry = ≺-is-linear x y x≠y
 where
  x≠y : x ≠ y
  x≠y = contrapositive (ap right) rx≠ry

\end{code}

Discreteness of 𝔻 and linearity of ≺ imply that ≺ is trichotomous, i.e. for
every x y : 𝔻 , x ≺ y or x ＝ y or y ≺ x holds. The lemmas after
≺-is-trichotomous show that exactly one of these is the case, as witnessed by
trichotomy-is-a-singleton.

\begin{code}

≺-is-trichotomous : (x y : 𝔻) → x ≺ y + (x ＝ y) + (y ≺ x)
≺-is-trichotomous x y = cases a b (𝔻-is-discrete x y)
 where
  a : x ＝ y → (x ≺ y) + (x ＝ y) + (y ≺ x)
  a = inr ∘ inl
  b : (x ≠ y) → (x ≺ y) + (x ＝ y) + (y ≺ x)
  b n = cases c d (≺-is-linear x y n)
   where
    c : x ≺ y → (x ≺ y) + (x ＝ y) + (y ≺ x)
    c = inl
    d : y ≺ x → (x ≺ y) + (x ＝ y) + (y ≺ x)
    d = inr ∘ inr

≺-to-≠ : {x y : 𝔻} → x ≺ y → x ≠ y
≺-to-≠ {middle}  {middle}      = 𝟘-induction
≺-to-≠ {middle}  {left y}      = 𝟘-induction
≺-to-≠ {middle}  {right y} _   = middle-is-not-right
≺-to-≠ {left x}  {middle}  _   = (λ p → middle-is-not-left (p ⁻¹))
≺-to-≠ {left x}  {left y}  x≺y = contrapositive left-lc (≺-to-≠ x≺y)
≺-to-≠ {left x}  {right y} _   = left-is-not-right
≺-to-≠ {right x} {middle}      = 𝟘-induction
≺-to-≠ {right x} {left y}      = 𝟘-induction
≺-to-≠ {right x} {right y} x≺y = contrapositive right-lc (≺-to-≠ x≺y)

≺-to-≠' : {x y : 𝔻} → y ≺ x → x ≠ y
≺-to-≠' l e = ≺-to-≠ l (e ⁻¹)

＝-to-¬≺ : {x y : 𝔻} → x ＝ y → ¬ (x ≺ y)
＝-to-¬≺ e l = ≺-to-≠ l e

＝-to-¬≺' : {x y : 𝔻} → x ＝ y → ¬ (y ≺ x)
＝-to-¬≺' e l = ≺-to-≠ l (e ⁻¹)

≺-to-¬≺ : (x y : 𝔻) → x ≺ y → ¬ (y ≺ x)
≺-to-¬≺ middle    middle      = 𝟘-induction
≺-to-¬≺ middle    (left y)    = 𝟘-induction
≺-to-¬≺ middle    (right y) _ = id
≺-to-¬≺ (left x)  middle    _ = id
≺-to-¬≺ (left x)  (left y)    = ≺-to-¬≺ x y
≺-to-¬≺ (left x)  (right y) _ = id
≺-to-¬≺ (right x) middle      = 𝟘-induction
≺-to-¬≺ (right x) (left y)    = 𝟘-induction
≺-to-¬≺ (right x) (right y)   = ≺-to-¬≺ x y

trichotomy-is-a-singleton : {x y : 𝔻} → is-singleton (x ≺ y + (x ＝ y) + y ≺ x)
trichotomy-is-a-singleton {x} {y} =
 pointed-props-are-singletons (≺-is-trichotomous x y) γ
  where
   γ : is-prop (x ≺ y + (x ＝ y) + y ≺ x)
   γ = +-is-prop (≺-is-prop-valued x y) h g
    where
     h : is-prop ((x ＝ y) + y ≺ x)
     h = +-is-prop 𝔻-is-set (≺-is-prop-valued y x) ＝-to-¬≺'
     g : x ≺ y → ¬ ((x ＝ y) + y ≺ x)
     g l = cases a b
      where
       a : x ≠ y
       a = ≺-to-≠ l
       b : ¬ (y ≺ x)
       b = ≺-to-¬≺ x y l

\end{code}

Next, we prove that ≺ has no endpoints and is dense (although formulated with Σ,
as explained at the top of this file).

\begin{code}

left-≺ : (x : 𝔻) → left x ≺ x
left-≺ middle    = ⋆
left-≺ (left x)  = left-≺ x
left-≺ (right x) = ⋆

≺-right : (x : 𝔻) → x ≺ right x
≺-right middle    = ⋆
≺-right (left x)  = ⋆
≺-right (right x) = ≺-right x

≺-has-no-left-endpoint-Σ : (x : 𝔻) → Σ y ꞉ 𝔻 , y ≺ x
≺-has-no-left-endpoint-Σ x = left x , left-≺ x

≺-has-no-right-endpoint-Σ : (x : 𝔻) → Σ y ꞉ 𝔻 , x ≺ y
≺-has-no-right-endpoint-Σ x = right x , ≺-right x

≺-is-dense-Σ : (x y : 𝔻) → x ≺ y → Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-is-dense-Σ middle middle = 𝟘-induction
≺-is-dense-Σ middle (left y) = 𝟘-induction
≺-is-dense-Σ middle (right y) _ = right (left y) , ⋆ , left-≺ y
≺-is-dense-Σ (left x) middle _ = left (right x) , ≺-right x , ⋆
≺-is-dense-Σ (left x) (left y) x≺y = γ (≺-is-dense-Σ x y x≺y)
 where
  γ : (Σ z ꞉ 𝔻 , x ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ left y
  γ (z , x≺z , z≺y) = left z , x≺z , z≺y
≺-is-dense-Σ (left x) (right y) _ = middle , ⋆ , ⋆
≺-is-dense-Σ (right x) middle = 𝟘-induction
≺-is-dense-Σ (right x) (left y) = 𝟘-induction
≺-is-dense-Σ (right x) (right y) l = γ (≺-is-dense-Σ x y l)
 where
  γ : (Σ z ꞉ 𝔻 , x ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , right x ≺ z × z ≺ right y
  γ (z , m , n) = right z , m , n

\end{code}

Binary interpolation is a generalisation of density, which can, in our case, be
proved from density using trichotomy of ≺.

We will need this property to construct the (rounded) ideal completion of
(𝔻 , ≺).

\begin{code}

≺-interpolation₂-Σ : (x₁ x₂ y : 𝔻) → x₁ ≺ y → x₂ ≺ y
                   → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
≺-interpolation₂-Σ x₁ x₂ y l₁ l₂ = cases₃ a b c (≺-is-trichotomous x₁ x₂)
 where
  a : x₁ ≺ x₂ → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
  a k = γ (≺-is-dense-Σ x₂ y l₂)
   where
    γ : (Σ z ꞉ 𝔻 , x₂ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
    γ (z , m , n) = z , ≺-is-transitive x₁ x₂ z k m , m , n
  b : x₁ ＝ x₂ → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
  b refl = γ (≺-is-dense-Σ x₁ y l₁)
   where
    γ : (Σ z ꞉ 𝔻 , x₁ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
    γ (z , m , n) = z , m , m , n
  c : x₂ ≺ x₁ → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
  c k = γ (≺-is-dense-Σ x₁ y l₁)
   where
    γ : (Σ z ꞉ 𝔻 , x₁ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
    γ (z , m , n) = z , m , ≺-is-transitive x₂ x₁ z k m , n

\end{code}
