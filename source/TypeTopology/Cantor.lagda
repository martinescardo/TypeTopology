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

We use δ to range over the type α n ≠ β n, and μ to range over the
minimality condition (i : ℕ) → α i ≠ β i → n ≤ i, for α, β and n
suitably specialized according to the situation we are considering.
We also use the letter "a" to range over the apartness type α ♯ β.

\begin{code}

apartness-criterion : (α β : Cantor) → (Σ n ꞉ ℕ , α n ≠ β n) → α ♯ β
apartness-criterion α β (n , d) = III II
 where
  open import Naturals.RootsTruncation 𝓤₀ 𝟚 ₁ (λ b → 𝟚-is-discrete b ₁)

  γ : Cantor
  γ n = α n ⊕ β n

  I : γ n ＝ ₁
  I = Lemma[b≠c→b⊕c＝₁] d

  II : Σ m ꞉ ℕ , ((γ m ＝ ₁) × (m ≤ n) × ((i : ℕ) → i < m → γ i ≠ ₁))
  II = minimal-root γ n I

  III : type-of II → α ♯ β
  III (m , e , _ , a) = m , III₀ , III₁
   where
    III₀ : α m ≠ β m
    III₀ = Lemma[b⊕c＝₁→b≠c] e

    III₁ : (i : ℕ) → α i ≠ β i → m ≤ i
    III₁ i d = not-less-bigger-or-equal m i III₃
     where
      III₂ : γ i ＝ ₁
      III₂ = Lemma[b≠c→b⊕c＝₁] d

      III₃ : ¬ (i < m)
      III₃ l = a i l III₂

apartness-criterion-converse : (α β : Cantor) → α ♯ β → (Σ n ꞉ ℕ , α n ≠ β n)
apartness-criterion-converse α β (n , δ , _) = (n , δ)

\end{code}

Hence, in view of the following, the type α ♯ β has the universal
property of the propositional truncation of the type Σ n ꞉ ℕ , α n ≠ β n.

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

The apartness axioms are satisfied, and, moreover, the apartness is tight.

\begin{code}

♯-is-irreflexive : (α : Cantor) → ¬ (α ♯ α)
♯-is-irreflexive α (n , δ , μ) = ≠-is-irrefl (α n) δ

♯-is-symmetric : (α β : Cantor) → α ♯ β → β ♯ α
♯-is-symmetric α β (n , δ , μ) = n , (λ e → δ (e ⁻¹)) , λ i d → μ i (≠-sym d)

♯-is-strongly-cotransitive : ∀ α β γ → α ♯ β → (α ♯ γ) + (β ♯ γ)
♯-is-strongly-cotransitive α β γ (n , δ , μ) = II I
 where
  I : (α n ≠ γ n) + (β n ≠ γ n)
  I = discrete-types-are-cotransitive' 𝟚-is-discrete {α n} {β n} {γ n} δ

  II : type-of I → (α ♯ γ) + (β ♯ γ)
  II (inl d) = inl (apartness-criterion α γ (n , d))
  II (inr d) = inr (apartness-criterion β γ (n , d))

♯-is-tight : Fun-Ext → ∀ α β → ¬ (α ♯ β) → α ＝ β
♯-is-tight fe α β ν = dfunext fe I
 where
  I : (n : ℕ) → α n ＝ β n
  I n = 𝟚-is-¬¬-separated (α n) (β n)
         (λ (d : α n ≠ β n) → ν (apartness-criterion α β (n , d)))

\end{code}

We say "strongly cotransitive", as opposed to simply "cotransitive"
because we have "+" rather than "∨".

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
