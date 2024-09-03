Martin Escardo, 11th December 2023.

We implement the isomorphism described at https://math.stackexchange.com/a/486093 .

Namely that the Cantor space (ℕ → 𝟚) with a removed point is
isomorphic to the product ℕ × (ℕ → 𝟚).

Because the Cantor space is homogeneous, meaning that for every two
points α and β there is an automorphism that maps α to β, it suffices
to consider a particular point of the Cantor space, as in the above
link, which is what we also do here.

To make the proof given in the above link constructive, we remove the
point by considering the subtype of all points *apart* from this
point, rather than all points *different* from this point.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order
open import Notation.Order
open import TypeTopology.Cantor
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons

module TypeTopology.CantorMinusPoint (fe : Fun-Ext) where

\end{code}

The function ϕ is defined so that ϕ n β is the binary sequence of
n-many ones followed by a zero and then β.

\begin{code}

ϕ : ℕ → Cantor → Cantor
ϕ 0        β = ₀ ∷ β
ϕ (succ n) β = ₁ ∷ ϕ n β

\end{code}

We will need the following two properties of the map ϕ.

\begin{code}

ϕ-property-δ : (β : Cantor) (i : ℕ) → ϕ i β i ≠ ₁
ϕ-property-δ β 0        = zero-is-not-one
ϕ-property-δ β (succ i) = ϕ-property-δ β i

ϕ-property-μ : (β : Cantor) (n i : ℕ) → ϕ n β i ≠ ₁ → n ≤ i
ϕ-property-μ β 0        i        ν = zero-least i
ϕ-property-μ β (succ n) 0        ν = ν refl
ϕ-property-μ β (succ n) (succ i) ν = ϕ-property-μ β n i ν

\end{code}

The function ψ is defined so that ψ n α removes n + 1 terms from the
beginning of the sequence α.

\begin{code}

ψ : ℕ → Cantor → Cantor
ψ 0        α = tail α
ψ (succ n) α = ψ n (tail α)

\end{code}

The function ψ n is a left inverse of the function ϕ n.

\begin{code}

ψϕ : (n : ℕ) → ψ n ∘ ϕ n ∼ id
ψϕ n α = dfunext fe (h n α)
 where
  h : (n : ℕ) (α : Cantor) → ψ n (ϕ n α) ∼ α
  h 0        = tail-cons' ₀
  h (succ n) = h n

\end{code}

But it is a right inverse only for sequences α apart 𝟏, in the following
sense, where the apartness relation is defined by

    α ♯ β = Σ n ꞉ ℕ , (α n ≠ β n)
                    × ((i : ℕ) → α i ≠ β i → n ≤ i)

in the module Cantor.

\begin{code}

ϕψ : (α : Cantor)
     ((n , δ , μ) : α ♯ 𝟏)
   → ϕ n (ψ n α) ＝ α
ϕψ α (n , δ , μ) = dfunext fe (h n α δ μ)
 where
  h : (n : ℕ) (α : Cantor)
    → α n ≠ ₁
    → ((i : ℕ) → α i ≠ ₁ → n ≤ i)
    → ϕ n (ψ n α) ∼ α
  h 0 α δ _ =
   ϕ 0 (ψ 0 α)     ∼⟨ ∼-refl ⟩
   ₀ ∷ tail α      ∼⟨ ∼-ap (_∷ tail α) ((different-from-₁-equal-₀ δ)⁻¹) ⟩
   head α ∷ tail α ∼⟨ ∼-sym (cons-head-tail α) ⟩
   α               ∼∎
  h (succ n) α δ μ =
    ϕ (succ n) (ψ (succ n) α) ∼⟨ ∼-refl ⟩
    ₁ ∷ ϕ n (ψ n (tail α))    ∼⟨ cons-∼ (h n (tail α) δ (μ ∘ succ)) ⟩
    ₁ ∷ tail α                ∼⟨ h₁ ⟩
    head α ∷ tail α           ∼⟨ ∼-sym (cons-head-tail α) ⟩
    α                         ∼∎
     where
      h₁ = ∼-cons ((♯-agreement α 𝟏 (succ n , δ , μ) 0 (zero-least n))⁻¹)

\end{code}

With the above we have all ingredients needed to characterize the
Cantor type with the point 𝟏 removed as the type ℕ × Cantor.

\begin{code}

Cantor-minus-𝟏-≃ : (Σ α ꞉ Cantor , α ♯ 𝟏) ≃ (ℕ × Cantor)
Cantor-minus-𝟏-≃ = qinveq f (g , gf , fg)
 where
  Cantor⁻ = Σ α ꞉ Cantor , α ♯ 𝟏

  f : Cantor⁻ → ℕ × Cantor
  f (α , i , δ , m) = i , ψ i α

  g : (ℕ × Cantor) → Cantor⁻
  g (n , β) = ϕ n β , n , ϕ-property-δ β n , ϕ-property-μ β n

  gf : g ∘ f ∼ id
  gf (α , a) = to-subtype-＝ (λ α → ♯-is-prop-valued fe α 𝟏) (ϕψ α a)

  fg : f ∘ g ∼ id
  fg (n , β) = to-Σ-＝ (refl , ψϕ n β)

\end{code}

And this is what we wanted to show. Notice how the prop-valuedness of
the apartness relation is crucial for the proof that this construction
works.

As discussed above, it doesn't matter which point we remove, because
the Cantor space is homogeneous, in the sense that for any two points
α and β there is an automorphism (in fact, an involution) that maps α
to β, as proved in the module Cantor.

TODO. Use this to conclude, as a corollary, that

 (Σ α ꞉ Cantor , α ♯ γ) ≃ (ℕ × Cantor)

for any point γ.
