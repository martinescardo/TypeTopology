Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ExhaustibleTypes where

open import SpartanMLTT
open import Two

\end{code}

Definition:

\begin{code}

exhaustible : ∀ {U} → U ̇ → U ̇
exhaustible X = (p : X → 𝟚) → Σ \(y : 𝟚) → y ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Closer to the original definition of exhaustibility in LICS'2007 amd LMCS'2008:

\begin{code}

exhaustible' : ∀ {U} → U ̇ → U ̇
exhaustible' X = 
 Σ \(A : (X → 𝟚) → 𝟚) → (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Because the axiom of choice holds in MLTT:

\begin{code}

exhaustible-implies-exhaustible' : ∀ {U} {X : U ̇} →

 exhaustible X → exhaustible' X

exhaustible-implies-exhaustible' {U} {X} φ = A , lemma
 where A : (X → 𝟚) → 𝟚
       A p = pr₁(φ p)

       lemma : (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)
       lemma p = pr₂(φ p)

open import SearchableTypes

searchable-implies-exhaustible : ∀ {U} {X : U ̇} →

 searchable X → exhaustible X

searchable-implies-exhaustible {U} {X} ε p = y , (lemma₀ , lemma₁)
 where 
  x₀ : X
  x₀ = pr₁(ε p)

  y : 𝟚 
  y = p x₀

  lemma₀ :  y ≡ ₁ → (x : X) → p x ≡ ₁
  lemma₀ = pr₂(ε p)

  lemma₁ : ((x : X) → p x ≡ ₁) → y ≡ ₁
  lemma₁ h = h x₀

\end{code}
