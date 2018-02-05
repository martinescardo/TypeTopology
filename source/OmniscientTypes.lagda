Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OmniscientTypes where

open import SpartanMLTT
open import Two

omniscient : ∀ {U} → U ̇ → U ̇
omniscient X = (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + (Π \(x : X) → p x ≡ ₁)

\end{code}

Notice that Bishop's limited principle of omniscience LPO, which is a
taboo, in Aczel's terminology, is the omniscience of ℕ. LPO is
independent. In classical mathematics it is uncomfortable to have
independent propositions, but of course unavoidable. Independence
occurs often in constructive mathematics, particular in classically
compatible constructive mathematics, like Bishop's methamatics and
Martin-Löf type theory (in its various flavours); even the principle
of excluded middle is independent.

We'll see that the infinite set ℕ∞ defined in the module
ConvergentSequence is omniscient.


If a set X is omniscient and a set Y has is has decidable
equality, then the function space (X → Y) has decidable
equality, if we assume extensionality. In our topological
correspondence, decidable equality is called discreteness.
More generally we have:

\begin{code}

open import DiscreteAndSeparated
open import DecidableAndDetachable
open import UF

apart-or-equal : ∀ {U V} {X : U ̇} → FunExt U V → {Y : X → V ̇}
              → omniscient X → ((x : X) → discrete(Y x)) 
              → (f g : (x : X) → Y x) → (f ♯ g) + (f ≡ g)
apart-or-equal {U} {V} {X} fe {Y} φ d f g = lemma₂ lemma₁
 where
  claim : (x : X) → f x ≢ g x  +  f x ≡ g x
  claim x = +-commutative(d x (f x) (g x))

  lemma₀ : Σ \(p : X → 𝟚) → (x : X) → (p x ≡ ₀ → f x ≢ g x) × (p x ≡ ₁ → f x ≡ g x)
  lemma₀ = indicator claim

  p : X → 𝟚
  p = pr₁ lemma₀

  lemma₁ : (Σ \x → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  lemma₁ = φ p

  lemma₂ : (Σ \x → p x ≡ ₀) + ((x : X) → p x ≡ ₁) → f ♯ g  +  f ≡ g
  lemma₂(inl(x , r)) = inl(x , (pr₁(pr₂ lemma₀ x) r)) 
  lemma₂(inr h) = inr (funext fe (λ x → pr₂(pr₂ lemma₀ x) (h x)))


omniscient-discrete-discrete : ∀ {U V} {X : U ̇} → FunExt U V → {Y : X → V ̇} → 

   omniscient X → ((x : X) → discrete(Y x)) → discrete((x : X) → Y x)

omniscient-discrete-discrete fe φ d f g = h(apart-or-equal fe φ d f g)
 where
  h : f ♯ g + f ≡ g → f ≡ g + f ≢ g
  h(inl a) = inr(apart-is-different a)
  h(inr r) = inl r


omniscient-discrete-discrete' : ∀ {U V} {X : U ̇} {Y : V ̇} → FunExt U V
                             → omniscient X → discrete Y → discrete(X → Y)
omniscient-discrete-discrete' fe φ d = omniscient-discrete-discrete fe φ (λ x → d)

𝟘-omniscient : omniscient 𝟘
𝟘-omniscient p = inr (λ x → 𝟘-elim x)

omniscient-decidable : ∀ {U} (X : U ̇) → omniscient X → decidable X
omniscient-decidable X φ = f a
 where
  a : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁)
  a = φ (λ x → ₀)
  
  f : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁) → decidable X
  f (inl (x , _)) = inl x
  f (inr u)       = inr (λ x → zero-is-not-one (u x))

decidable-prop-omniscient : ∀ {U} (X : U ̇) → isProp X → decidable X → omniscient X
decidable-prop-omniscient X isp δ p = g δ
 where
  g : decidable X → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
  g (inl x) = two-equality-cases b c
   where
    b : p x ≡ ₀ → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
    b r = inl (x , r)

    c : p x ≡ ₁ → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
    c r = inr (λ y → transport (λ x → p x ≡ ₁) (isp x y) r)
  g (inr u) = inr (λ x → 𝟘-elim (u x))
   

\end{code}
