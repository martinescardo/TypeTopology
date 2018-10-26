Martin Escardo, 15 August 2014.

Higgs' Involution Theorem. In any topos, if f : Ω → Ω is a
monomorphism, then it is an involution.

We adapt and prove the result in univalent mathematics, using the
propositional axiom of univalence. (We don't rely on propositional
resizing (or impredicativity).)

There is a proof by diagram chasing with iterated pullbacks, in page
65 of Johnstone's Sketches of an Elephant, volume 1.

The proof given here is based on an exercise in page 160 of Lambek and
Scott's Introduction to Higher-Order Categorical Logic, attributed to
Scedrov. Thanks to Phil Scott for bringing my attention to this proof.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt

module HiggsInvolutionTheorem
        (fe : funext U₀ U₀)
        (pe : propext U₀)
       where

\end{code}

TODO. Generalize from propositions in the universe U₀ to any universe U.

\begin{code}

Ω₀ : U₁ ̇
Ω₀ = Ω U₀

involutive : ∀ {U} {X : U ̇} → (f : X → X) → U ̇
involutive f = ∀{x} → f (f x) ≡ x

higgs : (f : Ω₀ → Ω₀) → left-cancellable f → involutive f
higgs f cancelf {p} = cancelf (VII p)
  where
   I : (p : Ω₀) → f p ≡ ⊤ → p ≡ ⊤ → f ⊤ ≡ ⊤
   I p r s = transport (λ - → f - ≡ ⊤) s r

   II : (p : Ω₀) → f p ≡ ⊤ → f ⊤ ≡ ⊤ → p ≡ ⊤
   II p r s = cancelf (r ∙ s ⁻¹)

   III : (p : Ω₀) → f p ≡ ⊤ → p ≡ f ⊤
   III p r = Ω-ext pe fe (I p r) (II p r)

   IV : (p : Ω₀) → f (f p) ≡ ⊤ → p ≡ ⊤
   IV p r = cancelf (III (f p) r)

   V' : (p : Ω₀) → f (f (f p)) ≡ ⊤ → f p ≡ ⊤
   V' p r = IV (f p) r

   VI : (p : Ω₀) → f p ≡ ⊤ → f (f (f p)) ≡ ⊤
   VI p r = d ∙ r
    where
     a : f (f p) ≡ f ⊤
     a = ap f r

     b : f ⊤ ≡ p
     b = (III p r)⁻¹

     c : f (f p) ≡ p
     c = a ∙ b

     d : f (f (f p)) ≡ f p
     d = ap f c

   VII : (p : Ω₀) → f (f (f p)) ≡ f p
   VII p = Ω-ext pe fe (V' p) (VI p)

\end{code}
