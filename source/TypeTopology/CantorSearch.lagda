Martin Escardo, 20th June 2019 and 28th May 2021.

Search over uniformly continuous decidable predicates on the Cantor type.

This is loosely based on my LICS'2007 paper "Infinite sets that admit
fast exhaustive search", https://doi.org/10.1109/LICS.2007.25, and my
LMCS'2008 paper "Exhaustible sets in higher-type computation",
https://doi.org/10.2168/LMCS-4(3:3)2008.

Removed assumption of function extensionality 11th July 2024 by using
the observation that 𝟚-valued uniformly continuous functions on the
Cantor type are extensional in the sense that they map pointwise equal
sequences to equal booleans.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.Cantor
open import UF.Base
open import UF.DiscreteAndSeparated hiding (_♯_)

module TypeTopology.CantorSearch where

\end{code}

We first consider search over the type 𝟚 of binary digits ₀ and ₁.

To check that for all n : 𝟚 we have p n ＝ ₁, it is enough to check
that p (p ₀) ＝ ₁.

\begin{code}

private
 motivating-fact : (p : 𝟚 → 𝟚) →  p (p ₀) ＝ ₁ → (n : 𝟚) → p n ＝ ₁
 motivating-fact p r = f (p ₀) refl r
  where
   f : (n₀ : 𝟚) → p ₀ ＝ n₀ → p n₀ ＝ ₁ → (n : 𝟚) → p n ＝ ₁
   f ₀ s r ₀ = r
   f ₀ s r ₁ = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
   f ₁ s r ₀ = s
   f ₁ s r ₁ = r

ε𝟚 : (𝟚 → 𝟚) → 𝟚
ε𝟚 p = p ₀

A𝟚 : (𝟚 → 𝟚) → 𝟚
A𝟚 p = p (ε𝟚 p)

\end{code}

The function A𝟚 is the characteristic function of universal
quantification:

\begin{code}

A𝟚-property→ : (p : 𝟚 → 𝟚) → A𝟚 p ＝ ₁ → (n : 𝟚) → p n ＝ ₁
A𝟚-property→ = motivating-fact

A𝟚-property← : (p : 𝟚 → 𝟚) → ((n : 𝟚) → p n ＝ ₁) → A𝟚 p ＝ ₁
A𝟚-property← p ϕ = ϕ (ε𝟚 p)

𝟚-searchable : (p : 𝟚 → 𝟚) → Σ n₀ ꞉ 𝟚 , (p n₀ ＝ ₁ → (n : 𝟚) → p n ＝ ₁)
𝟚-searchable p = ε𝟚 p , A𝟚-property→ p

\end{code}

The function p has a root (that is, there is n with p n ＝ ₀) if and
only if ε𝟚 p is a root. This follows from A𝟚-property→. So ε𝟚 chooses
a root if there is some root, and we can check whether there is a root
by checking whether or not p (ε𝟚 p) ＝ ₀. This is what A𝟚 does.

\begin{code}

ε𝟚-property→ : (p : 𝟚 → 𝟚) → (Σ n ꞉ 𝟚 , p n ＝ ₀) → p (ε𝟚 p) ＝ ₀
ε𝟚-property→ p = IV
 where
  I : (Σ n ꞉ 𝟚 , p n ＝ ₀) → ¬ ((n : 𝟚) → p n ＝ ₁)
  I (n , e) ϕ = equal-₀-different-from-₁ e (ϕ n)

  II : ¬ ((n : 𝟚) → p n ＝ ₁) → ¬ (A𝟚 p ＝ ₁)
  II = contrapositive (A𝟚-property→ p)

  III : ¬ (A𝟚 p ＝ ₁) → p (ε𝟚 p) ＝ ₀
  III = different-from-₁-equal-₀

  IV : (Σ n ꞉ 𝟚 , p n ＝ ₀) → p (ε𝟚 p) ＝ ₀
  IV = III ∘ II ∘ I

ε𝟚-property← : (p : 𝟚 → 𝟚) → p (ε𝟚 p) ＝ ₀ → (Σ n ꞉ 𝟚 , p n ＝ ₀)
ε𝟚-property← p e = ε𝟚 p , e

\end{code}

We use this to search over the Cantor type.

Notice that a function has modulus of continuity zero if and only if
it is constant, and that if a function has modulus of continuity n
then it has modulus of continuity k for any k > n.

\begin{code}

open notions-of-continuity 𝟚 𝟚-is-discrete

modulus-zero-iff-constant  : (p : 𝟚ᴺ → 𝟚)
                           → 0 is-a-modulus-of-uc-of p
                           ↔ ((α β : 𝟚ᴺ) → p α ＝ p β)
modulus-zero-iff-constant p = I , II
 where
  I :  0 is-a-modulus-of-uc-of p → ((α β : 𝟚ᴺ) → p α ＝ p β)
  I u α β = u α β ⋆

  II :  ((α β : 𝟚ᴺ) → p α ＝ p β) → 0 is-a-modulus-of-uc-of p
  II κ α β ⋆ = κ α β

\end{code}

The crucial lemma for Cantor search is this:

\begin{code}

cons-decreases-modulus : (p : 𝟚ᴺ → 𝟚)
                         (n : ℕ)
                         (b : 𝟚)
                       → (succ n) is-a-modulus-of-uc-of p
                       → n is-a-modulus-of-uc-of (p ∘ cons b)
cons-decreases-modulus p n b u α β = III
 where
  I : α ＝⟦ n ⟧ β → cons b α ＝⟦ succ n ⟧ cons b β
  I e = refl , e

  II : cons b α ＝⟦ succ n ⟧ cons b β → p (cons b α) ＝ p (cons b β)
  II = u (cons b α) (cons b β)

  III : α ＝⟦ n ⟧ β → p (cons b α) ＝ p (cons b β)
  III = II ∘ I

\end{code}

Added 11th July 2024. Uniformly continuous functions are extensional
in the following sense. This allows us to remove the assumption of
function extensionality from previous versions of this file.

\begin{code}

uniform-continuity-gives-extensionality : (p : 𝟚ᴺ → 𝟚)
                                        → uniformly-continuous p
                                        → (α β : 𝟚ᴺ) → α ∼ β → p α ＝ p β
uniform-continuity-gives-extensionality p (n , u) = II
 where
  I : (n : ℕ) (α β : 𝟚ᴺ) → α ∼ β → α ＝⟦ n ⟧ β
  I 0        α β h = ⋆
  I (succ n) α β h = h 0 , I n (α ∘ succ) (β ∘ succ) (h ∘ succ)

  II : (α β : 𝟚ᴺ) → α ∼ β → p α ＝ p β
  II α β h = u α β (I n α β h)

\end{code}

We now define search over the Cantor space. The functions A and ε are
mutually recursively defined. But of course we can consider only ε
expanding the definition of A in that of ε, because the definition of
A doesn't use induction.

The following point c₀ of the Cantor type is arbitrary, and what we do
works with any choice of c₀. So we make it abstract.

\begin{code}

abstract
 c₀ : 𝟚ᴺ
 c₀ = λ i → ₀

A  : ℕ → (𝟚ᴺ → 𝟚) → 𝟚
ε  : ℕ → (𝟚ᴺ → 𝟚) → 𝟚ᴺ

A n p = p (ε n p)

ε 0 p        = c₀
ε (succ n) p = case ε𝟚 (λ b → A n (p ∘ cons b)) of
                (λ (b₀ : 𝟚) → cons b₀ (ε n (p ∘ cons b₀)))
\end{code}

The function A is designed to satisfy the specification

  A n p ＝ ₁ ↔ ((α : 𝟚ᴺ) → p α ＝ ₁)

for any decidable predicate p with modulus of uniform continuity n.

So A is the characteristic function of universal quantification over
uniformly continuous decidable predicates.

One direction is direct and doesn't require uniform continuity, but we
still need to supply a number:

\begin{code}

A-property← : (p : 𝟚ᴺ → 𝟚)
              (n : ℕ)
            → ((α : 𝟚ᴺ) → p α ＝ ₁)
            → A n p ＝ ₁
A-property← p n ϕ = ϕ (ε n p)

\end{code}

The other direction is proved by induction on ℕ.

\begin{code}

A-property→ : (p : 𝟚ᴺ → 𝟚)
              (n : ℕ)
            → n is-a-modulus-of-uc-of p
            → A n p ＝ ₁
            → (α : 𝟚ᴺ) → p α ＝ ₁
A-property→ p 0        u r α = p α  ＝⟨ u α c₀ ⋆ ⟩
                               p c₀ ＝⟨ r ⟩
                               ₁    ∎
A-property→ p (succ n) u r α = V
 where
  IH : (b : 𝟚) → A n (p ∘ cons b) ＝ ₁ → (β : 𝟚ᴺ) → p (cons b β) ＝ ₁
  IH b = A-property→ (p ∘ cons b) n (cons-decreases-modulus p n b u)

  b₀ : 𝟚
  b₀ = ε𝟚 (λ b → A n (p ∘ cons b))

  I : A n (p ∘ cons b₀) ＝ ₁ → (b : 𝟚) → A n (p ∘ cons b) ＝ ₁
  I = A𝟚-property→ (λ b → A n (p ∘ cons b))

  observation₀ : A (succ n) p ＝ ₁
  observation₀ = r

  observation₁ : A (succ n) p ＝ A n (p ∘ cons b₀)
  observation₁ = refl

  II : (b : 𝟚) (β : 𝟚ᴺ) → p (cons b β) ＝ ₁
  II b = IH b (I r b)

  III : p (cons (head α) (tail α)) ＝ ₁
  III = II (head α) (tail α)

  IV : p α ＝ p (cons (head α) (tail α))
  IV = uniform-continuity-gives-extensionality
        p
        (succ n , u)
        α
        (cons (head α) (tail α))
        (cons-head-tail α)

  V : p α ＝ ₁
  V =  p α                        ＝⟨ IV ⟩
       p (cons (head α) (tail α)) ＝⟨ III ⟩
       ₁                          ∎

\end{code}

The desired construction is the following:

\begin{code}

Cantor-uniformly-searchable : (p : 𝟚ᴺ → 𝟚)
                            → uniformly-continuous p
                            → Σ α₀ ꞉ 𝟚ᴺ , (p α₀ ＝ ₁ → (α : 𝟚ᴺ) → p α ＝ ₁)
Cantor-uniformly-searchable p (n , u) = ε n p , A-property→ p n u

having-root-is-decidable : (p : 𝟚ᴺ → 𝟚)
                         → uniformly-continuous p
                         → is-decidable (Σ α ꞉ 𝟚ᴺ , p α ＝ ₀)
having-root-is-decidable p (n , u) = γ (p α) refl
 where
  α : 𝟚ᴺ
  α = ε n p

  γ : (k : 𝟚) → p α ＝ k → is-decidable (Σ α ꞉ 𝟚ᴺ , p α ＝ ₀)
  γ ₀ r = inl (α  , r)
  γ ₁ r = inr (λ (β , s) → zero-is-not-one
                            (₀   ＝⟨ s ⁻¹ ⟩
                             p β ＝⟨ A-property→ p n u r β ⟩
                             ₁   ∎))

being-constantly-₁-is-decidable : (p : 𝟚ᴺ → 𝟚)
                                → uniformly-continuous p
                                → is-decidable ((α : 𝟚ᴺ) → p α ＝ ₁)
being-constantly-₁-is-decidable p u = γ (having-root-is-decidable p u)
 where
  γ : is-decidable (Σ α ꞉ 𝟚ᴺ , p α ＝ ₀) → is-decidable ((α : 𝟚ᴺ) → p α ＝ ₁)
  γ (inl (α , r)) = inr (λ ϕ → zero-is-not-one (r ⁻¹ ∙ ϕ α))
  γ (inr ν)       = inl (λ α → different-from-₀-equal-₁ (λ r → ν (α , r)))

\end{code}

Examples that show that A can be fast (in this case linear time) even
if the supplied modulus of uniform continuity is large.

\begin{code}

module examples where

 prc : ℕ → 𝟚ᴺ → 𝟚
 prc n α = α n

 sprc-lemma : (n : ℕ) → (succ n) is-a-modulus-of-uc-of (prc n)
 sprc-lemma 0        α β (r , _) = r
 sprc-lemma (succ n) α β (_ , s) = sprc-lemma n (tail α) (tail β) s

 sprc : (n : ℕ) → uniformly-continuous (prc n)
 sprc n = succ n , sprc-lemma n

 prc-example : ℕ → 𝟚
 prc-example n = A (succ n) (prc n)

 large-prc-example : prc-example 10000 ＝ ₀
 large-prc-example = refl

\end{code}

In the worst case, however, A n p runs in time 2ⁿ.

\begin{code}

 xor : ℕ → 𝟚ᴺ → 𝟚
 xor 0        α = ₀
 xor (succ n) α = head α ⊕ xor n (tail α)

 xor-uc : (n : ℕ) → n is-a-modulus-of-uc-of (xor n)
 xor-uc 0        α β ⋆       = refl
 xor-uc (succ n) α β (p , q) = γ
  where
   IH : xor n (tail α) ＝ xor n (tail β)
   IH = xor-uc n (tail α) (tail β) q

   γ : head α ⊕ xor n (tail α) ＝ head β ⊕ xor n (tail β)
   γ = ap₂ _⊕_ p IH

 xor-example : ℕ → 𝟚
 xor-example n = A n (xor n)

\end{code}

If we set the following to `true` then the type checking of this
module increases by 17s in a MacBook Air M1, where the total time to
check this file with `false` is less than 2s.

\begin{code}

 open import MLTT.Bool

 check-large-example : Bool
 check-large-example = false

 large-xor-example : if check-large-example then (xor-example 17 ＝ ₀) else (₀ ＝ ₀)
 large-xor-example = refl

\end{code}

The time is 2^n for this example.

Another fast example (linear):

\begin{code}

 κ₁ : ℕ → 𝟚ᴺ → 𝟚
 κ₁ n α = complement (α n ⊕ α n)

 sκ₁-lemma : (n : ℕ) → (succ n) is-a-modulus-of-uc-of (κ₁ n)
 sκ₁-lemma 0        α β (r , _) = ap (λ - → complement (- ⊕ -)) r
 sκ₁-lemma (succ n) α β (_ , s) = sκ₁-lemma n (tail α) (tail β) s

 sκ₁ : (n : ℕ) → uniformly-continuous (κ₁ n)
 sκ₁ n = succ n , sκ₁-lemma n

 κ₁-example : ℕ → 𝟚
 κ₁-example n = A (succ n) (κ₁ n)

 large-κ₁-example : κ₁-example 100000 ＝ ₁
 large-κ₁-example = refl

\end{code}
