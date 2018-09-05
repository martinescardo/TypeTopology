Martin Escardo, September 2018.

on Lawvere's FPT.
http://tac.mta.ca/tac/reprints/articles/15/tr15abs.html

We begin with retracts and then move to surjections.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LawvereFPT where

open import SpartanMLTT
open import UF-Retracts

lfpt : ∀ {U V} {A : U ̇} {X : V ̇} (φ : A → (A → X))
     → has-section φ
     → (f : X → X) → Σ \(x : X) → x ≡ f x
lfpt {U} {V} {A} {X} φ (s , φs) f = x , p
 where
  g : A → X
  g a = f (φ a a)
  a : A
  a = s g
  x : X
  x = φ a a
  p : x ≡ f x
  p = x         ≡⟨ refl ⟩
      φ (s g) a ≡⟨ ap (λ - → - a) (φs g) ⟩
      g a       ≡⟨ refl ⟩
      f x       ∎

\end{code}

The original LFPT has surjection, rather than retraction, as an
assumption. The retraction version can be formulated and proved in
pure MLTT. To formulate the original version we consider MLTT extended
with propositional truncation, or rather just MLTT with propositional
truncation as an assumption, given as a parameter for the following
anonymous module.

\begin{code}

open import UF-PropTrunc
open import UF-ImageAndSurjection

module _ (pt : PropTrunc) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

 lfpto : ∀ {U V} {A : U ̇} {X : V ̇} (φ : A → (A → X))
      → is-surjection φ
      → (f : X → X) → ∃ \(x : X) → x ≡ f x
 lfpto {U} {V} {A} {X} φ s f = ptfunct γ e
  where
   g : A → X
   g a = f (φ a a)
   e : ∃ \(a : A) → φ a ≡ g
   e = s g
   γ : (Σ \(a : A) → φ a ≡ g) → (Σ \(x : X) → x ≡ f x)
   γ (a , q) = x , p
    where
     x : X
     x = φ a a
     p : x ≡ f x
     p = x         ≡⟨ refl ⟩
         φ a a     ≡⟨ ap (λ - → - a) q ⟩
         g a       ≡⟨ refl ⟩
         f x       ∎

\end{code}

So in lfpto we have a weaker hypothesis for the theorem, but we need a
stronger language for formulate and prove it.

To be continued.
