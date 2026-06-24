Martin Escardo, 20th June 2019 onwards.

The Cantor type of infinite binary sequences.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Apartness.Definition
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.ExitTruncation
open import Naturals.Order
open import Notation.Order
open import NotionsOfDecidability.Decidable
open import UF.DiscreteAndSeparated hiding (_♯_)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module TypeTopology.Cantor where

\end{code}

The Cantor type 𝟚ᴺ.

\begin{code}

𝟚ᴺ : 𝓤₀ ̇
𝟚ᴺ = ℕ → 𝟚

Cantor-is-set : funext₀ → is-set 𝟚ᴺ
Cantor-is-set fe = Π-is-set fe (λ _ → 𝟚-is-set)

\end{code}

We let  α,β,γ range  over the  Cantor type.

The constant sequences:

\begin{code}

𝟎 : 𝟚ᴺ
𝟎 = (i ↦ ₀)

𝟏 : 𝟚ᴺ
𝟏 = (i ↦ ₁)

\end{code}

Cons, head and tail.

\begin{code}

head : 𝟚ᴺ → 𝟚
head α = α 0

tail : 𝟚ᴺ → 𝟚ᴺ
tail α = α ∘ succ

cons : 𝟚 → 𝟚ᴺ → 𝟚ᴺ
cons n α 0        = n
cons n α (succ i) = α i

_∷_ : 𝟚 → 𝟚ᴺ → 𝟚ᴺ
_∷_ = cons

cons-∼ : {x : 𝟚} {α β : 𝟚ᴺ} → α ∼ β → x ∷ α ∼ x ∷ β
cons-∼ h 0        = refl
cons-∼ h (succ i) = h i

∼-cons : {x y : 𝟚} {α : 𝟚ᴺ} → x ＝ y → x ∷ α ∼ y ∷ α
∼-cons refl = ∼-refl

head-cons : (n : 𝟚) (α : 𝟚ᴺ) → head (cons n α) ＝ n
head-cons n α = refl

tail-cons : (n : 𝟚) (α : 𝟚ᴺ) → tail (cons n α) ＝ α
tail-cons n α = refl

tail-cons' : (n : 𝟚) (α : 𝟚ᴺ) → tail (cons n α) ∼ α
tail-cons' n α i = refl

cons-head-tail : (α : 𝟚ᴺ) → α ∼ cons (head α) (tail α)
cons-head-tail α 0        = refl
cons-head-tail α (succ i) = refl

\end{code}

Agreement of two binary sequences α and β at the first n positions,
written α ＝⟦ n ⟧ β.

\begin{code}

_＝⟦_⟧_ : 𝟚ᴺ → ℕ → 𝟚ᴺ → 𝓤₀ ̇
α ＝⟦ 0      ⟧ β = 𝟙
α ＝⟦ succ n ⟧ β = (head α ＝ head β) × (tail α ＝⟦ n ⟧ tail β)

＝⟦⟧-refl : (α : 𝟚ᴺ) (k : ℕ) → α ＝⟦ k ⟧ α
＝⟦⟧-refl α 0 = ⋆
＝⟦⟧-refl α (succ k) = refl , ＝⟦⟧-refl (tail α) k

＝⟦⟧-trans : (α β γ : 𝟚ᴺ) (k : ℕ) → α ＝⟦ k ⟧ β → β ＝⟦ k ⟧ γ → α ＝⟦ k ⟧ γ
＝⟦⟧-trans α β γ 0 d e = ⋆
＝⟦⟧-trans α β γ (succ k) (h , t) (h' , t') =
 (h ∙ h') ,
 ＝⟦⟧-trans (tail α) (tail β) (tail γ) k t t'

＝⟦⟧-sym : (α β : 𝟚ᴺ) (k : ℕ) → α ＝⟦ k ⟧ β → β ＝⟦ k ⟧ α
＝⟦⟧-sym α β 0        ⋆       = ⋆
＝⟦⟧-sym α β (succ k) (h , t) = (h ⁻¹) , ＝⟦⟧-sym (tail α) (tail β) k t

＝⟦⟧-is-decidable : (α β : 𝟚ᴺ) (k : ℕ) → is-decidable (α ＝⟦ k ⟧ β)
＝⟦⟧-is-decidable α β 0        = inl ⋆
＝⟦⟧-is-decidable α β (succ k) =
 Cases (𝟚-is-discrete (head α) (head β))
  (λ (h : head α ＝ head β)
        → map-decidable
           (λ (t : tail α ＝⟦ k ⟧ tail β) → h , t)
           (λ (_ , t) → t)
           (＝⟦⟧-is-decidable (tail α) (tail β) k))
  (λ (ν : head α ≠ head β) → inr (λ (h , _) → ν h))

\end{code}

We have that (α ＝⟦ n ⟧ β) iff α k ＝ β k for all k < n:

\begin{code}

⟦⟧-agreement→ : (α β : 𝟚ᴺ)
                (n : ℕ)
                → (α ＝⟦ n ⟧ β)
                → ((k : ℕ) → k < n → α k ＝ β k)
⟦⟧-agreement→ α β 0        *       k        l = 𝟘-elim l
⟦⟧-agreement→ α β (succ n) (p , e) 0        l = p
⟦⟧-agreement→ α β (succ n) (p , e) (succ k) l = IH k l
 where
  IH : (k : ℕ) → k < n → α (succ k) ＝ β (succ k)
  IH = ⟦⟧-agreement→ (tail α) (tail β) n e

⟦⟧-agreement← : (α β : 𝟚ᴺ)
                (n : ℕ)
              → ((k : ℕ) → k < n → α k ＝ β k)
              → (α ＝⟦ n ⟧ β)
⟦⟧-agreement← α β 0        ϕ = ⋆
⟦⟧-agreement← α β (succ n) ϕ = ϕ 0 ⋆ , ⟦⟧-agreement← (tail α) (tail β) n (ϕ ∘ succ)

\end{code}

A function 𝟚ᴺ → N, with N a discrete type, is uniformly continuous if
it has a modulus of uniform continuity (uc):

\begin{code}

module notions-of-continuity
         (N : 𝓤 ̇ )
         (N-is-discrete : is-discrete N)
        where

 _is-a-modulus-of-uc-of_ : ℕ → (𝟚ᴺ → N) → 𝓤 ̇
 m is-a-modulus-of-uc-of p = ∀ α β → α ＝⟦ m ⟧ β → p α ＝ p β

 being-a-modulus-of-uc-is-prop
  : Fun-Ext
  → (m : ℕ)
    (p : 𝟚ᴺ → N)
  → is-prop (m is-a-modulus-of-uc-of p)
 being-a-modulus-of-uc-is-prop fe m p
  = Π₃-is-prop fe (λ α β e → discrete-types-are-sets N-is-discrete)

 uniformly-continuous : (𝟚ᴺ → N) → 𝓤 ̇
 uniformly-continuous p = Σ m ꞉ ℕ , m is-a-modulus-of-uc-of p

 uniform-continuity-data = uniformly-continuous

\end{code}

Uniform continuity as defined above is data rather than property. This
is because any number bigger than a modulus of uniform continuity is
also a modulus.

Exercise. Show that

 (Σ p ꞉ (𝟚ᴺ  → N) , uniformly-continuous p) ≃ (Σ n ꞉ ℕ , Fin (2 ^ n) → N)

Added 23 June 2026. Actually, the above is not quite correct!

If we define uniform continuity with ∃ rather than Σ, this is no
longer the case.

\begin{code}

 continuous : (𝟚ᴺ → N) → 𝓤 ̇
 continuous p = ∀ α → Σ m ꞉ ℕ , (∀ β → α ＝⟦ m ⟧ β → p α ＝ p β)

 continuity-data = continuous

\end{code}

Any number bigger than a modulus of uniform continuity is also a modulus.

\begin{code}

 increase-modulus-of-uc : (p : 𝟚ᴺ → N)
                        → (m : ℕ)
                        → m is-a-modulus-of-uc-of p
                        → (succ m) is-a-modulus-of-uc-of p
 increase-modulus-of-uc p 0        0-is-mod      α β _       = 0-is-mod α β ⋆
 increase-modulus-of-uc p (succ m) succ-m-is-mod α β (h , t) = II
  where
   I : ∀ α β m
     → (head (tail α) ＝ head (tail β)) × (tail (tail α) ＝⟦ m ⟧ tail (tail β))
     → tail α ＝⟦ m ⟧ tail β
   I α β 0        (h , t) = ⋆
   I α β (succ m) (h , t) = h , I (tail α) (tail β) m t

   II : p α ＝ p β
   II = succ-m-is-mod α β (h , I α β m t)

\end{code}

We can define uniform continuity as a property by considering a
smallest modulus of continuity.

\begin{code}

 _is-a-smallest-modulus-of-uc-of_ : ℕ → (𝟚ᴺ → N) → 𝓤 ̇
 m is-a-smallest-modulus-of-uc-of p =
    (m is-a-modulus-of-uc-of p)
  × ((n : ℕ) → n is-a-modulus-of-uc-of p → m ≤ n)

 being-a-smallest-modulus-of-uc-is-prop
  : Fun-Ext
  → (m : ℕ)
    (p : 𝟚ᴺ → N)
  → is-prop (m is-a-smallest-modulus-of-uc-of p)
 being-a-smallest-modulus-of-uc-is-prop fe m p
  = ×-is-prop
     (being-a-modulus-of-uc-is-prop fe m p)
     (Π₂-is-prop fe (λ n _ → ≤-is-prop-valued m n))

 is-uniformly-continuous : (𝟚ᴺ → N) → 𝓤 ̇
 is-uniformly-continuous p =
  Σ m ꞉ ℕ , m is-a-smallest-modulus-of-uc-of p

 being-uniformly-continuous-is-prop
  : Fun-Ext
  → (p : 𝟚ᴺ → N) → is-prop (is-uniformly-continuous p)
 being-uniformly-continuous-is-prop
  fe p (m , m-is-mod , m-μ) (m' , m'-is-mod , m'-μ)
  = to-subtype-＝
     (λ n → being-a-smallest-modulus-of-uc-is-prop fe n p)
     (m ＝⟨ ≤-anti m m' (m-μ m' m'-is-mod) (m'-μ m m-is-mod) ⟩
      m' ∎)

\end{code}

The following easy lemma is often useful.

\begin{code}

 cons-decrease-uc-modulus
  : (p : 𝟚ᴺ → N)
  → (m : ℕ)
  → (succ m) is-a-modulus-of-uc-of p
  → (b : 𝟚) → m is-a-modulus-of-uc-of (p ∘ cons b)
 cons-decrease-uc-modulus p m succ-m-is-mod b α β e
  = succ-m-is-mod (cons b α) (cons b β) (refl , e)

\end{code}

In general, it is not decidable whether a given m is a modulus of
uniform continuity. But if m is a modulus, then it is decidable
whether any n < m is a modulus of continuity, so that given any
modulus we can find the smallest one by bounded search.

\begin{code}

 decidable-smaller-modulus-of-uc
  : (p : 𝟚ᴺ → N)
  → (m : ℕ)
  → (succ m) is-a-modulus-of-uc-of p
  → is-decidable (m is-a-modulus-of-uc-of p)
 decidable-smaller-modulus-of-uc p 0 1-is-mod = γ
  where
   have : (α β : 𝟚ᴺ) → (α 0 ＝ β 0) × 𝟙 → p α ＝ p β
   have = 1-is-mod

   γ : is-decidable ((α β : 𝟚ᴺ) → 𝟙 → p α ＝ p β)
   γ = dep-Cases
        (λ _ → is-decidable ((α β : 𝟚ᴺ) → 𝟙 → p α ＝ p β))
        (N-is-discrete (p 𝟎) (p 𝟏))
        (λ (e : p 𝟎 ＝ p 𝟏) → inl (λ α β ⋆
              → 𝟚-equality-cases
                 (λ (a₀ : α 0 ＝ ₀)
                        → 𝟚-equality-cases
                           (λ (b₀ : β 0 ＝ ₀)
                                  → p α ＝⟨ 1-is-mod α 𝟎 (a₀ , ⋆) ⟩
                                    p 𝟎 ＝⟨ 1-is-mod 𝟎 β ((b₀ ⁻¹) , ⋆) ⟩
                                    p β ∎)
                           (λ (b₁ : β 0 ＝ ₁)
                                  → p α ＝⟨ 1-is-mod α 𝟎 (a₀ , ⋆) ⟩
                                    p 𝟎 ＝⟨ e ⟩
                                    p 𝟏 ＝⟨ 1-is-mod 𝟏 β ((b₁ ⁻¹) , ⋆) ⟩
                                    p β ∎))
                 (λ (a₁ : α 0 ＝ ₁)
                        → 𝟚-equality-cases
                           (λ (b₀ : β 0 ＝ ₀)
                                  → p α ＝⟨ 1-is-mod α 𝟏 (a₁ , ⋆) ⟩
                                    p 𝟏 ＝⟨ e ⁻¹ ⟩
                                    p 𝟎 ＝⟨ 1-is-mod 𝟎 β ((b₀ ⁻¹) , ⋆) ⟩
                                    p β ∎)
                           (λ (b₁ : β 0 ＝ ₁)
                                  → p α ＝⟨ 1-is-mod α 𝟏 (a₁ , ⋆) ⟩
                                    p 𝟏 ＝⟨ 1-is-mod 𝟏 β ((b₁ ⁻¹) , ⋆) ⟩
                                    p β ∎))))
        (λ (ν : p 𝟎 ≠ p 𝟏) → inr (λ 0-is-mod → ν (0-is-mod 𝟎 𝟏 ⋆)))

 decidable-smaller-modulus-of-uc p (succ m)is-mod = I (IH ₀) (IH ₁)
  where
   have : succ (succ m) is-a-modulus-of-uc-of p
   have = is-mod

   IH : (b : 𝟚) → is-decidable (m is-a-modulus-of-uc-of (p ∘ cons b))
   IH b = decidable-smaller-modulus-of-uc (p ∘ cons b) m
           (cons-decrease-uc-modulus p (succ m) is-mod b)

   I : is-decidable (m is-a-modulus-of-uc-of (p ∘ cons ₀))
     → is-decidable (m is-a-modulus-of-uc-of (p ∘ cons ₁))
     → is-decidable (succ m is-a-modulus-of-uc-of p)
   I (inl m₀) (inl m₁) = inl II
    where
     II : (α β : 𝟚ᴺ) → (α 0 ＝ β 0) × (tail α ＝⟦ m ⟧ tail β) → p α ＝ p β
     II α β (h , t) =
      𝟚-equality-cases
       (λ (a₀ : α 0 ＝ ₀)
        → p α                     ＝⟨ is-mod _ _ (refl , refl , ＝⟦⟧-refl _ m) ⟩
          p (cons (α 0) (tail α)) ＝⟨ ap (λ - → p (cons - (tail α))) a₀ ⟩
          (p ∘ cons ₀) (tail α)   ＝⟨ m₀ (tail α) (tail β) t ⟩
          (p ∘ cons ₀) (tail β)   ＝⟨ (ap (λ - → p (cons - (tail β))) (h ⁻¹ ∙ a₀))⁻¹ ⟩
          p (cons (β 0) (tail β)) ＝⟨ is-mod _ _ (refl , refl , ＝⟦⟧-refl _ m) ⟩
          p β                     ∎)
       (λ (a₁ : α 0 ＝ ₁)
        → p α                     ＝⟨ is-mod _ _ (refl , refl , ＝⟦⟧-refl _ m) ⟩
          p (cons (α 0) (tail α)) ＝⟨ ap (λ - → p (cons - (tail α))) a₁ ⟩
          (p ∘ cons ₁) (tail α)   ＝⟨ m₁ (tail α) (tail β) t ⟩
          (p ∘ cons ₁) (tail β)   ＝⟨ (ap (λ - → p (cons - (tail β))) (h ⁻¹ ∙ a₁))⁻¹ ⟩
          p (cons (β 0) (tail β)) ＝⟨ is-mod _ _ (refl , refl , ＝⟦⟧-refl _ m) ⟩
          p β                     ∎)
   I (inl _)  (inr ν₁) = inr (contrapositive
                               (λ succ-m-is-mod → cons-decrease-uc-modulus
                                                   p m succ-m-is-mod ₁)
                               ν₁)
   I (inr ν₀) _        = inr (contrapositive
                               (λ succ-m-is-mod → cons-decrease-uc-modulus
                                                   p m succ-m-is-mod ₀)
                               ν₀)

 conditional-decidability-of-being-a-modulus-of-uc
  : (p : 𝟚ᴺ → N)
    (m : ℕ)
  → m is-a-modulus-of-uc-of p
  → (n : ℕ) → n < m → is-decidable (n is-a-modulus-of-uc-of p)
 conditional-decidability-of-being-a-modulus-of-uc p
  = regression-lemma
     (_is-a-modulus-of-uc-of p)
     (decidable-smaller-modulus-of-uc p)
     (increase-modulus-of-uc p)

\end{code}

Hence we can be the uniform continuity property from uniform
continuity data, without propositional truncation.

\begin{code}

 uc-data-gives-uc-property
  : (p : 𝟚ᴺ → N) → uniformly-continuous p → is-uniformly-continuous p
 uc-data-gives-uc-property p
  = minimal-witness⁺
     (_is-a-modulus-of-uc-of p)
     (conditional-decidability-of-being-a-modulus-of-uc p)

\end{code}

The converse is trivial, and amounts to discarding a piece of data.

\begin{code}

 uc-property-gives-uc-data
  : (p : 𝟚ᴺ → N) → is-uniformly-continuous p → uniformly-continuous p
 uc-property-gives-uc-data p (m , m-is-mod , m-μ) = m , m-is-mod

\end{code}

It follows from this that the above notion of uniform continuity is
equivalent to the propositional truncation of uniform continuity data.

\begin{code}

 module alternative-notions-of-continuity
         (pt : propositional-truncations-exist)
        where

  open PropositionalTruncation pt
  open exit-truncations pt

  is-uniformly-continuous' : (𝟚ᴺ → N) → 𝓤 ̇
  is-uniformly-continuous' p = ∃ m ꞉ ℕ , m is-a-modulus-of-uc-of p

  uniform-continuity-prime
   : (p : 𝟚ᴺ → N) → is-uniformly-continuous p → is-uniformly-continuous' p
  uniform-continuity-prime p (m , m-is-mod , m-μ) = ∣ m , m-is-mod ∣

  uniform-continuity-unprime
   : Fun-Ext
   → (p : 𝟚ᴺ → N) → is-uniformly-continuous' p → is-uniformly-continuous p
  uniform-continuity-unprime fe p p-uc'
   = uc-data-gives-uc-property p
      (exit-truncation⁺
        (_is-a-modulus-of-uc-of p)
        (λ m → being-a-modulus-of-uc-is-prop fe m p)
        (conditional-decidability-of-being-a-modulus-of-uc p)
        p-uc')

  is-continuous : (𝟚ᴺ → N) → 𝓤 ̇
  is-continuous p = ∀ α → ∃ m ꞉ ℕ , (∀ β → α ＝⟦ m ⟧ β → p α ＝ p β)

\end{code}

We now define the canonical apartness relation _♯_ for points of the
cantor type 𝟚ᴺ. Two sequences are apart if they differ at some index.

To make apartness into a proposition, which is crucial for our
purposes, we consider the minimal index at which they differ. This
allows us to avoid the assumption that propositional truncations
exist, as above. But we still need function extensionality, so that
the proof is not in the realm of pure Martin-Löf type theory.

\begin{code}

open Apartness

_♯_ : 𝟚ᴺ → 𝟚ᴺ → 𝓤₀ ̇
α ♯ β = Σ n ꞉ ℕ , (α n ≠ β n)
                × ((i : ℕ) → α i ≠ β i → n ≤ i)

\end{code}

We use δ to range over the type α n ≠ β n, and μ to range over the
minimality condition (i : ℕ) → α i ≠ β i → n ≤ i, for α, β and n
suitably specialized according to the situation we are considering.
We also use the letter "a" to range over the apartness type α ♯ β.

\begin{code}

apartness-criterion : (α β : 𝟚ᴺ) → (Σ n ꞉ ℕ , α n ≠ β n) → α ♯ β
apartness-criterion α β = minimal-witness
                           (λ n → α n ≠ β n)
                           (λ n → ¬-preserves-decidability
                                   (𝟚-is-discrete (α n) (β n)))

apartness-criterion-converse : (α β : 𝟚ᴺ) → α ♯ β → (Σ n ꞉ ℕ , α n ≠ β n)
apartness-criterion-converse α β (n , δ , _) = (n , δ)

\end{code}

Hence, in view of the following, the type α ♯ β has the universal
property of the propositional truncation of the type Σ n ꞉ ℕ , α n ≠ β n.

\begin{code}

♯-is-prop-valued : Fun-Ext → is-prop-valued _♯_
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

♯-is-irreflexive : is-irreflexive _♯_
♯-is-irreflexive α (n , δ , μ) = ≠-is-irrefl (α n) δ

♯-is-symmetric : is-symmetric _♯_
♯-is-symmetric α β (n , δ , μ) = n , (λ e → δ (e ⁻¹)) , λ i d → μ i (≠-sym d)

♯-strongly-cotransitive : is-strongly-cotransitive _♯_
♯-strongly-cotransitive α β γ (n , δ , μ) = III
 where
  I : (α n ≠ γ n) + (β n ≠ γ n)
  I = discrete-types-are-cotransitive' 𝟚-is-discrete {α n} {β n} {γ n} δ

  II : type-of I → (α ♯ γ) + (β ♯ γ)
  II (inl d) = inl (apartness-criterion α γ (n , d))
  II (inr d) = inr (apartness-criterion β γ (n , d))

  III : (α ♯ γ) + (β ♯ γ)
  III = II I

♯-is-strong-apartness : Fun-Ext → is-strong-apartness _♯_
♯-is-strong-apartness fe = ♯-is-prop-valued fe ,
                           ♯-is-irreflexive ,
                           ♯-is-symmetric ,
                           ♯-strongly-cotransitive

♯-is-apartness : (fe : Fun-Ext)
               → (pt : propositional-truncations-exist)
               → is-apartness pt _♯_
♯-is-apartness fe pt =
 strong-apartness-is-apartness pt _♯_ (♯-is-strong-apartness fe)

♯-is-tight : Fun-Ext → is-tight _♯_
♯-is-tight fe α β ν = dfunext fe I
 where
  I : (n : ℕ) → α n ＝ β n
  I n = 𝟚-is-¬¬-separated (α n) (β n)
         (λ (d : α n ≠ β n) → ν (apartness-criterion α β (n , d)))

\end{code}

If two sequences α and β are apart, they agree before the apartness index n.

\begin{code}

♯-agreement : (α β : 𝟚ᴺ)
              ((n , _) : α ♯ β)
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

module _ (fe : funext₀) (α β : 𝟚ᴺ) where

 Cantor-swap : 𝟚ᴺ → 𝟚ᴺ
 Cantor-swap γ i = (β i ⊕ α i) ⊕ γ i

 Cantor-swap-involutive : Cantor-swap ∘ Cantor-swap ∼ id
 Cantor-swap-involutive γ = dfunext fe (λ i → ⊕-involutive {β i ⊕ α i} {γ i})

 Cantor-swap-swaps∼ : Cantor-swap α ∼ β
 Cantor-swap-swaps∼ i =
  Cantor-swap α i   ＝⟨refl⟩
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

 Cantor-swap-≃ : 𝟚ᴺ ≃ 𝟚ᴺ
 Cantor-swap-≃ = Cantor-swap ,
                 involutions-are-equivs Cantor-swap Cantor-swap-involutive

Cantor-homogeneous : funext₀
                   → (α β : 𝟚ᴺ)
                   → Σ f ꞉ 𝟚ᴺ ≃ 𝟚ᴺ , (⌜ f ⌝ α ＝ β)
Cantor-homogeneous fe α β = Cantor-swap-≃ fe α β , Cantor-swap-swaps fe α β

\end{code}
