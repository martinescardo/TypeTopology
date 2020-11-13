Martin Escardo, 15 August 2014.

Higgs' Involution Theorem. In any topos, if f : Ω → Ω is a
monomorphism, then it is an involution.

We adapt and prove the result in univalent mathematics, using
propositional and functional extensionality. (We don't rely on
propositional resizing (or impredicativity).)

There is a proof by diagram chasing with iterated pullbacks, in page
65 of Johnstone's Sketches of an Elephant, volume 1.

The proof given here is based on an exercise in page 160 of Lambek and
Scott's Introduction to Higher-Order Categorical Logic, attributed to
Scedrov. Thanks to Phil Scott for bringing my attention to this proof.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-FunExt
open import UF-Subsingletons-FunExt

module HiggsInvolutionTheorem
        (fe : funext 𝓤 𝓤)
        (pe : propext 𝓤)
       where

involutive : {X : 𝓥 ̇ } → (f : X → X) → 𝓥 ̇
involutive f = ∀ x → f (f x) ≡ x

higgs : (f : Ω 𝓤 → Ω 𝓤) → left-cancellable f → involutive f
higgs f c = VIII
  where
   I : (p : Ω 𝓤) → f p ≡ ⊤ → p ≡ ⊤ → f ⊤ ≡ ⊤
   I p r s = transport (λ - → f - ≡ ⊤) s r

   II : (p : Ω 𝓤) → f p ≡ ⊤ → f ⊤ ≡ ⊤ → p ≡ ⊤
   II p r s = c (r ∙ s ⁻¹)

   III : (p : Ω 𝓤) → f p ≡ ⊤ → p ≡ f ⊤
   III p r = Ω-ext' pe fe (I p r) (II p r)

   IV : (p : Ω 𝓤) → f (f p) ≡ ⊤ → p ≡ ⊤
   IV p r = c (III (f p) r)

   V : (p : Ω 𝓤) → f (f (f p)) ≡ ⊤ → f p ≡ ⊤
   V p = IV (f p)

   VI : (p : Ω 𝓤) → f p ≡ ⊤ → f (f (f p)) ≡ ⊤
   VI p r = iv ∙ r
    where
     i : f (f p) ≡ f ⊤
     i = ap f r

     ii : f ⊤ ≡ p
     ii = (III p r)⁻¹

     iii : f (f p) ≡ p
     iii = i ∙ ii

     iv : f (f (f p)) ≡ f p
     iv = ap f iii

   VII : (p : Ω 𝓤) → f (f (f p)) ≡ f p
   VII p = Ω-ext' pe fe (V p) (VI p)

   VIII : (p : Ω 𝓤) → f (f p) ≡ p
   VIII p = c (VII p)

\end{code}
