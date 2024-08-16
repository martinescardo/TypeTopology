Martin Escardo, 20th June 2019 onwards.

The Cantor type of infinite binary sequences.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.DiscreteAndSeparated hiding (_♯_)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module TypeTopology.Cantor where

Cantor = ℕ → 𝟚

\end{code}

We let  α,β,γ range  over the  Cantor type.

The constant sequences:

\begin{code}

𝟎 : Cantor
𝟎 = (i ↦ ₀)

𝟏 : Cantor
𝟏 = (i ↦ ₁)

\end{code}

Cons, head and tail.

\begin{code}

head : Cantor → 𝟚
head α = α 0

tail : Cantor → Cantor
tail α = α ∘ succ

cons : 𝟚 → Cantor → Cantor
cons n α 0        = n
cons n α (succ i) = α i

_∷_ : 𝟚 → Cantor → Cantor
_∷_ = cons

cons-∼ : {x : 𝟚} {α β : Cantor} → α ∼ β → x ∷ α ∼ x ∷ β
cons-∼ h 0        = refl
cons-∼ h (succ i) = h i

∼-cons : {x y : 𝟚} {α : Cantor} → x ＝ y → x ∷ α ∼ y ∷ α
∼-cons refl = ∼-refl

head-cons : (n : 𝟚) (α : Cantor) → head (cons n α) ＝ n
head-cons n α = refl

tail-cons : (n : 𝟚) (α : Cantor) → tail (cons n α) ＝ α
tail-cons n α = refl

tail-cons' : (n : 𝟚) (α : Cantor) → tail (cons n α) ∼ α
tail-cons' n α i = refl

cons-head-tail : (α : Cantor) → α ∼ cons (head α) (tail α)
cons-head-tail α 0        = refl
cons-head-tail α (succ i) = refl

\end{code}

Agreement of two binary sequences α and β at the first n positions,
written α ＝⟦ n ⟧ β.

\begin{code}

_＝⟦_⟧_ : Cantor → ℕ → Cantor → 𝓤₀ ̇
α ＝⟦ 0      ⟧ β = 𝟙
α ＝⟦ succ n ⟧ β = (head α ＝ head β) × (tail α ＝⟦ n ⟧ tail β)

\end{code}

We have that (α ＝⟦ n ⟧ β) iff α k ＝ β k for all k < n:

\begin{code}

agreement→ : (α β : Cantor)
             (n : ℕ)
           → (α ＝⟦ n ⟧ β)
           → ((k : ℕ) → k < n → α k ＝ β k)
agreement→ α β 0        *       k        l = 𝟘-elim l
agreement→ α β (succ n) (p , e) 0        l = p
agreement→ α β (succ n) (p , e) (succ k) l = IH k l
 where
  IH : (k : ℕ) → k < n → α (succ k) ＝ β (succ k)
  IH = agreement→ (tail α) (tail β) n e

agreement← : (α β : Cantor)
             (n : ℕ)
           → ((k : ℕ) → k < n → α k ＝ β k)
           → (α ＝⟦ n ⟧ β)
agreement← α β 0        ϕ = ⋆
agreement← α β (succ n) ϕ = ϕ 0 ⋆ , agreement← (tail α) (tail β) n (ϕ ∘ succ)

\end{code}

A function Cantor → 𝟚 is uniformly continuous if it has a modulus
of continuity:

\begin{code}

_is-a-modulus-of-uniform-continuity-of_ : ℕ → (Cantor → 𝟚) → 𝓤₀ ̇
m is-a-modulus-of-uniform-continuity-of p = ∀ α β → α ＝⟦ m ⟧ β → p α ＝ p β

uniformly-continuous : (Cantor → 𝟚) → 𝓤₀ ̇
uniformly-continuous p = Σ m ꞉ ℕ , m is-a-modulus-of-uniform-continuity-of p

\end{code}

Uniform continuity as defined above is data rather than property. This
is because any number bigger than a modulus of uniform continuity is
also a modulus.

TODO. Show that

 (Σ p ꞉ (Cantor  → 𝟚) , uniformly-continuous p) ≃ (Σ n ꞉ ℕ , Fin (2 ^ n) → 𝟚)

If we define uniform continuity with ∃ rather than Σ, this is no
longer the case.

\begin{code}

continuous : (Cantor → 𝟚) → 𝓤₀ ̇
continuous p = ∀ α → Σ m ꞉ ℕ , (∀ β → α ＝⟦ m ⟧ β → p α ＝ p β)

\end{code}

\begin{code}

module notions-of-continuity (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-uniformly-continuous : (Cantor → 𝟚) → 𝓤₀ ̇
 is-uniformly-continuous p = ∃ m ꞉ ℕ , m is-a-modulus-of-uniform-continuity-of p

 is-continuous : (Cantor → 𝟚) → 𝓤₀ ̇
 is-continuous p = ∀ α → ∃ m ꞉ ℕ , (∀ β → α ＝⟦ m ⟧ β → p α ＝ p β)

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

♯-is-prop-valued : Fun-Ext → (α β : Cantor) → is-prop (α ♯ β)
♯-is-prop-valued fe α β (n , δ , μ) (n' , δ' , μ') = III
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

♯-agreement : (α β : Cantor)
              ((n , δ , μ) : α ♯ β)
              (i : ℕ)
            → i < n → α i ＝ β i
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

The Cantor type is homogeneous.

\begin{code}

module _ (fe : Fun-Ext) (α β : Cantor) where

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

Cantor-homogeneous : Fun-Ext
                   → (α β : Cantor)
                   → Σ f ꞉ Cantor ≃ Cantor , (⌜ f ⌝ α ＝ β)
Cantor-homogeneous fe α β = Cantor-swap-≃ fe α β , Cantor-swap-swaps fe α β

\end{code}
