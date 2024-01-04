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
open import UF.DiscreteAndSeparated hiding (_♯_)
open import UF.Base
open import UF.DiscreteAndSeparated hiding (_♯_)
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

We assume function extensionality in this file:

\begin{code}

module TypeTopology.CantorMinusPoint (fe : Fun-Ext) where

\end{code}

The Cantor type of infinite binary sequences:

\begin{code}

Cantor = ℕ → 𝟚

\end{code}

We let α,β,γ range over the Cantor type.

The constantly ₁ sequence:

\begin{code}

𝟏 : Cantor
𝟏 = (i ↦ ₁)

\end{code}

We now define the canonical apartness relation _♯_ for points of the
Cantor type. Two sequences are apart if they differ at some index.

To make apartness into a proposition, which is crucial for our
purposes, we consider the minimal index at which they differ. This
allows us to avoid the assumption that propositional truncations
exist. But we still need function extensionality, so that the proof is
not in the realm of pure Martin-Löf type theory.

\begin{code}

_♯_ : Cantor → Cantor → 𝓤₀ ̇
α ♯ β = Σ n ꞉ ℕ , (α n ≠ β n)
                × ((i : ℕ) → α i ≠ β i → n ≤ i)

\end{code}

TODO. It is easy to see that this is a tight apartness relation. Maybe
implement this here. But this is not needed for our purposes.

We use δ to range over the type α n ≠ β n, and μ to range over the
minimality condition (i : ℕ) → α i ≠ β i → n ≤ i, for α, β and n
suitably specialized according to the situation we are considering.
We also use the letter "a" to range over the apartness type α ♯ β.

As claimed above, the apartness relation is proposition-valued.

\begin{code}

♯-is-prop-valued : (α β : Cantor) → is-prop (α ♯ β)
♯-is-prop-valued α β (n , δ , μ) (n' , δ' , μ') = III
 where
  I : (n : ℕ) → is-prop ((α n ≠ β n) × ((i : ℕ) → α i ≠ β i → n ≤ i))
  I n = ×-is-prop
         (negations-are-props fe)
         (Π₂-is-prop fe λ i _ → ≤-is-prop-valued n i)

  II : n ＝ n'
  II = ≤-anti n n' (μ n' δ') (μ' n δ)

  III : (n , δ , μ) ＝[ α ♯ β ] (n' , δ' , μ')
  III = to-subtype-＝ I II

\end{code}

If two sequences α and β are apart, they agree before the apartness index n.

\begin{code}

♯-agreement : (α β : Cantor) ((n , δ , μ) : α ♯ β) → (i : ℕ) → i < n → α i ＝ β i
♯-agreement α β (n , _ , μ) i ℓ = IV
 where
  I : α i ≠ β i → n ≤ i
  I = μ i

  II : ¬ (n ≤ i) → ¬ (α i ≠ β i)
  II = contrapositive I

  III : ¬ (n ≤ i)
  III = less-not-bigger-or-equal i n ℓ

  IV : α i ＝ β i
  IV = 𝟚-is-¬¬-separated (α i) (β i) (II III)

\end{code}

Cons, head, tail.

\begin{code}

_∷_ : 𝟚 → Cantor → Cantor
(x ∷ α) 0        = x
(x ∷ α) (succ n) = α n

head : Cantor → 𝟚
head α = α 0

tail : Cantor → Cantor
tail α = α ∘ succ

tail-cons : (x : 𝟚) (α : Cantor) → tail (x ∷ α) ∼ α
tail-cons x α i = refl

cons-head-tail : (α : Cantor) → head α ∷ tail α ∼ α
cons-head-tail α 0        = refl
cons-head-tail α (succ n) = refl

cons-∼ : {x : 𝟚} {α β : Cantor} → α ∼ β → x ∷ α ∼ x ∷ β
cons-∼ h 0        = refl
cons-∼ h (succ i) = h i

∼-cons : {x y : 𝟚} {α : Cantor} → x ＝ y → x ∷ α ∼ y ∷ α
∼-cons refl = ∼-refl

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
  h 0        = tail-cons ₀
  h (succ n) = h n

\end{code}

But it is a right inverse only for sequences α ♯ 𝟏, in the following
sense.

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
   head α ∷ tail α ∼⟨ cons-head-tail α ⟩
   α               ∼∎
  h (succ n) α δ μ =
    ϕ (succ n) (ψ (succ n) α) ∼⟨ ∼-refl ⟩
    ₁ ∷ ϕ n (ψ n (tail α))    ∼⟨ cons-∼ (h n (tail α) δ (μ ∘ succ)) ⟩
    ₁ ∷ tail α                ∼⟨ h₁ ⟩
    head α ∷ tail α           ∼⟨ cons-head-tail α ⟩
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
  gf (α , a) = to-subtype-＝ (λ α → ♯-is-prop-valued α 𝟏) (ϕψ α a)

  fg : f ∘ g ∼ id
  fg (n , β) = to-Σ-＝ (refl , ψϕ n β)

\end{code}

And this is what we wanted to show. Notice how the prop-valuedness of
the apartness relation is crucial for the proof that this construction
works.

As discussed above, it doesn't matter which point we remove, because
the Cantor space is homogeneous, in the sense that for any two points
α and β there is an automorphism (in fact, an involution) that maps α
to β.

\begin{code}

module _ (α β : Cantor) where

 Cantor-swap : Cantor → Cantor
 Cantor-swap γ i = (β i ⊕ α i) ⊕ γ i

 Cantor-swap-involutive : Cantor-swap ∘ Cantor-swap ∼ id
 Cantor-swap-involutive γ = dfunext fe (λ i → ⊕-involutive {β i ⊕ α i} {γ i})

 Cantor-swap-swaps∼ : Cantor-swap α ∼ β
 Cantor-swap-swaps∼ i =
  Cantor-swap α i   ＝⟨ refl ⟩
  (β i ⊕ α i) ⊕ α i ＝⟨ ⊕-assoc {β i} {α i} {α i} ⟩
  β i ⊕ (α i ⊕ α i) ＝⟨ ap (β i ⊕_) (Lemma[b⊕b＝₀] {α i}) ⟩
  β i ⊕ ₀           ＝⟨ ⊕-₀-right-neutral  ⟩
  β i               ∎

 Cantor-swap-swaps : Cantor-swap α ＝ β
 Cantor-swap-swaps = dfunext fe Cantor-swap-swaps∼

 Cantor-swap-swaps' : Cantor-swap β ＝ α
 Cantor-swap-swaps' = involution-swap
                       Cantor-swap
                       Cantor-swap-involutive
                       Cantor-swap-swaps

 Cantor-swap-≃ : Cantor ≃ Cantor
 Cantor-swap-≃ = Cantor-swap ,
                 involutions-are-equivs Cantor-swap Cantor-swap-involutive

Cantor-homogeneous : (α β : Cantor) → Σ f ꞉ Cantor ≃ Cantor , (⌜ f ⌝ α ＝ β)
Cantor-homogeneous α β = Cantor-swap-≃ α β , Cantor-swap-swaps α β

\end{code}

TODO. Use this to conclude, as a corollary, that

 (Σ α ꞉ Cantor , α ♯ γ) ≃ (ℕ × Cantor)

for any point γ.
