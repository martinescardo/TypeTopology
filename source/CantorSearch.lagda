Martin Escardo, 20th June 2019 and 28th May 2021.

Search over uniformly continuous decidable predicates on the Cantor type.

This is loosely based on my LICS'2007 paper "Infinite sets that admit
fast exhaustive search".

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Two-Properties
open import DiscreteAndSeparated
open import UF-FunExt
open import UF-Base

module CantorSearch (fe : funext 𝓤₀ 𝓤₀) where

\end{code}

We first consider search over the type 𝟚 of binary digits ₀ and ₁.

\begin{code}

private
 motivating-fact𝟚 : (p : 𝟚 → 𝟚) →  p (p ₀) ≡ ₁ → (n : 𝟚) → p n ≡ ₁
 motivating-fact𝟚 p r = f (p ₀) refl r
  where
   f : (n₀ : 𝟚) → p ₀ ≡ n₀ → p n₀ ≡ ₁ → (n : 𝟚) → p n ≡ ₁
   f ₀ s r ₀ = r
   f ₀ s r ₁ = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
   f ₁ s r ₀ = s
   f ₁ s r ₁ = r

ε𝟚 : (𝟚 → 𝟚) → 𝟚
ε𝟚 p = p ₀

A𝟚 : (𝟚 → 𝟚) → 𝟚
A𝟚 p = p (ε𝟚 p)

A𝟚-property : (p : 𝟚 → 𝟚) → A𝟚 p ≡ ₁ → (n : 𝟚) → p n ≡ ₁
A𝟚-property = motivating-fact𝟚

𝟚-searchable : (p : 𝟚 → 𝟚) → Σ n₀ ꞉ 𝟚 , (p n₀ ≡ ₁ → (n : 𝟚) → p n ≡ ₁)
𝟚-searchable p = ε𝟚 p , A𝟚-property p

\end{code}

We use this to search over the Cantor space. We first need some
preliminary definitions and facts.

\begin{code}

Cantor = ℕ → 𝟚

head : Cantor → 𝟚
head α = α 0

tail : Cantor → Cantor
tail α = α ∘ succ

cons : 𝟚 → Cantor → Cantor
cons n α 0        = n
cons n α (succ i) = α i

head-cons : (n : 𝟚) (α : Cantor) → head (cons n α) ≡ n
head-cons n α = refl

tail-cons : (n : 𝟚) (α : Cantor) → tail (cons n α) ≡ α
tail-cons n α = refl

cons-head-tail : (α : Cantor) → cons (head α) (tail α) ≡ α
cons-head-tail α = dfunext fe h
 where
  h : cons (head α) (tail α) ∼ α
  h zero     = refl
  h (succ i) = refl

\end{code}

Uniform continuity as defined below is data rather than property. This
is because any number bigger than a modulus of uniform continuity is
also a modulus.

We first define when two binary sequences α and β agree at the firsy n
positions, written α ≡⟦ n ⟧ β.

\begin{code}

_≡⟦_⟧_ : Cantor → ℕ → Cantor → 𝓤₀ ̇
α ≡⟦ 0      ⟧ β = 𝟙
α ≡⟦ succ n ⟧ β = (head α ≡ head β) × (tail α ≡⟦ n ⟧ tail β)

_is-a-modulus-of-uniform-continuity-of_ : ℕ → (Cantor → 𝟚) → 𝓤₀ ̇
n is-a-modulus-of-uniform-continuity-of p = (α β : Cantor) → α ≡⟦ n ⟧ β → p α ≡ p β

uniformly-continuous : (Cantor → 𝟚) → 𝓤₀ ̇
uniformly-continuous p = Σ n ꞉ ℕ , n is-a-modulus-of-uniform-continuity-of p

\end{code}

The crucial lemma for Cantor search is this:

\begin{code}

cons-decreases-modulus : (p : Cantor → 𝟚)
                         (n : ℕ)
                         (b : 𝟚)
                       → (succ n) is-a-modulus-of-uniform-continuity-of p
                       → n is-a-modulus-of-uniform-continuity-of (p ∘ cons b)
cons-decreases-modulus p n b u α β e = γ
 where
  γ : (p ∘ cons b) α ≡ (p ∘ cons b) β
  γ = u (cons b α) (cons b β) (refl , e)

\end{code}

We now define search over the Cantor space. The functions A and ε are
mutually recursively defined. But of course we can consider only ε
expanding the definition of A in that of ε, because the definition of
A doesn't use induction.

The following point c₀ of the Cantor type is arbitrary, and what we do
works with any choice of c₀. So we make it abstract. (NB. Even if we
postulate it, or we replace the definition by a hole, the definition
of A computes, provided it is used with correct inputs, namely p with
modulus of uniform continuity n. Try the examples module below.)

\begin{code}

abstract
 c₀ : Cantor
 c₀ = λ i → ₀

A : ℕ → (Cantor → 𝟚) → 𝟚
ε : ℕ → (Cantor → 𝟚) → Cantor

A n p = p (ε n p)

ε 0 p        = c₀
ε (succ n) p = cons b₀ α₀
 where
  open import Agda.Builtin.Strict
  b₀ : 𝟚
  b₀ = primForce (λ b → A n (p ∘ cons b)) ε𝟚

  α₀ : Cantor
  α₀ = ε n (p ∘ cons b₀)


epsilon : ℕ → ((ℕ → 𝟚) → 𝟚) → (ℕ → 𝟚)
epsilon 0 p        = λ i → ₀
epsilon (succ n) p = cons b₀ α₀
 where
  b₀ : 𝟚
  b₀ = p (cons ₀ (epsilon n (p ∘ cons ₀)))

  α₀ : ℕ → 𝟚
  α₀ = epsilon n (p ∘ cons b₀)


\end{code}

The function A is designed to satisfy the specification

  A n p ≡ ₁ ⇔ ((α : Cantor) → p α ≡ ₁)

for any decidable predicate p with modulus of continuity n.

So A is the characteristic function of universal quantification over
uniformly continuous decidable predicates.

One direction is trivial and doesn't require uniform continuity, but
we still need to supply a number:

\begin{code}

A-property← : (p : Cantor → 𝟚)
              (n : ℕ)
            → ((α : Cantor) → p α ≡ ₁)
            → A n p ≡ ₁
A-property← p n ϕ = ϕ (ε n p)

\end{code}

The other direction is proved by induction on ℕ.

\begin{code}

A-property→ : (p : Cantor → 𝟚)
              (n : ℕ)
            → n is-a-modulus-of-uniform-continuity-of p
            → A n p ≡ ₁
            → (α : Cantor) → p α ≡ ₁
A-property→ p 0        u r α = p α  ≡⟨ u α c₀ * ⟩
                               p c₀ ≡⟨ r ⟩
                               ₁    ∎
A-property→ p (succ n) u r α = IV
 where
  IH : (b : 𝟚) → A n (p ∘ cons b) ≡ ₁ → (β : Cantor) → p (cons b β) ≡ ₁
  IH b = A-property→ (p ∘ cons b) n (cons-decreases-modulus p n b u)

  b₀ : 𝟚
  b₀ = ε𝟚 (λ b → A n (p ∘ cons b))

  I : A n (p ∘ cons b₀) ≡ ₁ → (b : 𝟚) → A n (p ∘ cons b) ≡ ₁
  I = A𝟚-property (λ b → A n (p ∘ cons b))

  observation₀ : A (succ n) p ≡ ₁
  observation₀ = r

  observation₁ : A (succ n) p ≡ A n (p ∘ cons b₀)
  observation₁ = refl

  II : (b : 𝟚) (β : Cantor) → p (cons b β) ≡ ₁
  II b = IH b (I r b)

  III : p (cons (head α) (tail α)) ≡ ₁
  III = II (head α) (tail α)

  IV : p α ≡ ₁
  IV = transport (λ - → p - ≡ ₁) (cons-head-tail α) III

\end{code}

The desired construction is the following:

\begin{code}

Cantor-uniformly-searchable : (p : Cantor → 𝟚)
                            → uniformly-continuous p
                            → Σ α₀ ꞉ Cantor , (p α₀ ≡ ₁ → (α : Cantor) → p α ≡ ₁)
Cantor-uniformly-searchable p (n , u) = ε n p , A-property→ p n u

Δ : (p : Cantor → 𝟚)
  → uniformly-continuous p
  → decidable (Σ α ꞉ Cantor , p α ≡ ₀)
Δ p (n , u) = γ (p α) refl
 where
  α : Cantor
  α = ε n p

  γ : (k : 𝟚) → p α ≡ k → decidable (Σ α ꞉ Cantor , p α ≡ ₀)
  γ ₀ r = inl (α  , r)
  γ ₁ r = inr (λ (β , s) → zero-is-not-one (s ⁻¹ ∙ A-property→ p n u r β))


Δ' : (p : Cantor → 𝟚)
   → uniformly-continuous p
   → decidable ((α : Cantor) → p α ≡ ₁)
Δ' p u = γ (Δ p u)
 where
  γ : decidable (Σ α ꞉ Cantor , p α ≡ ₀) → decidable ((α : Cantor) → p α ≡ ₁)
  γ (inl (α , r)) = inr (λ ϕ → zero-is-not-one (r ⁻¹ ∙ ϕ α))
  γ (inr ν)       = inl (λ α → different-from-₀-equal-₁ (λ r → ν (α , r)))

\end{code}

Examples, that show that A can be fast (in this case linear time) even
if the supplied modulus of uniform continuity is large:

\begin{code}

module examples where

 prc : ℕ → Cantor → 𝟚
 prc n α = α n

 sprc-lemma : (n : ℕ) → (succ n) is-a-modulus-of-uniform-continuity-of (prc n)
 sprc-lemma 0        α β (r , _) = r
 sprc-lemma (succ n) α β (_ , s) = sprc-lemma n (tail α) (tail β) s

 sprc : (n : ℕ) → uniformly-continuous (prc n)
 sprc n = succ n , sprc-lemma n

 prc-example : ℕ → 𝟚
 prc-example n = A (succ n) (prc n)

 large-prc-example : prc-example 10000 ≡ ₀
 large-prc-example = refl

\end{code}

In the worst case, however, A n p runs in time 2ⁿ. Or is it doubly
exponential in Agda? The following large example doen't work for n>4.

\begin{code}

 xor : ℕ → Cantor → 𝟚
 xor 0        α = ₀
 xor (succ n) α = head α ⊕ xor n (tail α)

 xor-uc : (n : ℕ) → n is-a-modulus-of-uniform-continuity-of (xor n)
 xor-uc 0        α β *       = refl
 xor-uc (succ n) α β (p , q) = γ
  where
   IH : xor n (tail α) ≡ xor n (tail β)
   IH = xor-uc n (tail α) (tail β) q

   γ : α 0 ⊕ xor n (tail α) ≡ β 0 ⊕ xor n (tail β)
   γ = ap₂ _⊕_ p IH

 xor-example : ℕ → 𝟚
 xor-example n = A n (xor n)

 large-xor-example : xor-example 4 ≡ ₀
 large-xor-example = refl

\end{code}

Another fast example:

\begin{code}

 κ₁ : ℕ → Cantor → 𝟚
 κ₁ n α = complement (α n ⊕ α n)

 sκ₁-lemma : (n : ℕ) → (succ n) is-a-modulus-of-uniform-continuity-of (κ₁ n)
 sκ₁-lemma 0        α β (r , _) = ap (λ - → complement (- ⊕ -)) r
 sκ₁-lemma (succ n) α β (_ , s) = sκ₁-lemma n (tail α) (tail β) s

 sκ₁ : (n : ℕ) → uniformly-continuous (κ₁ n)
 sκ₁ n = succ n , sκ₁-lemma n

 κ₁-example : ℕ → 𝟚
 κ₁-example n = A (succ n) (κ₁ n)

 large-κ₁-example : κ₁-example 100000 ≡ ₁
 large-κ₁-example = refl

\end{code}
