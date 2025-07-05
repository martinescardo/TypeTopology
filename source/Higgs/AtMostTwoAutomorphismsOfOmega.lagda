Martin Escardo, 10th June 2025.

We prove that Ω has at most two automorphisms, which seems to be due
to Freyd [1]. Our proof is not based on [1], though.

[1] Peter Freyd. Choice and well-ordering.  Annals of Pure and Applied
    Logic 35 (1987) 149-166.
    https://doi.org/10.1016/0168-0072(87)90060-1
    https://core.ac.uk/download/pdf/81927529.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import UF.Equiv hiding (_≅_)
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier hiding (Ω)

module Higgs.AtMostTwoAutomorphismsOfOmega
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

open import Higgs.InvolutionTheorem fe pe
open import Higgs.AutomorphismsOfOmega fe pe

open Conjunction
open Implication fe
open Universal fe

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open Disjunction pt
 open PropositionalTruncation pt hiding (_∨_ ; ∨-elim)

 ℍ-has-at-most-two-elements-lemma
  : (x y : ℍ)
  → ∥ (𝕥 ＝ x) + (x ＝ y) + (y ＝ 𝕥) ∥
 ℍ-has-at-most-two-elements-lemma
  x@(p@(P , i) , p-is-ws)
  y@(q@(Q , j) , q-is-ws)
  = II
  where
   QP : ∥ Q + (Q → P) ∥
   QP = widespread-gives-widespread' pt p p-is-ws q

   PQ : ∥ P + (P → Q) ∥
   PQ = widespread-gives-widespread' pt q q-is-ws p

   I : (Q + (Q → P))
     → (P + (P → Q))
     → (𝕥 ＝ x) + (x ＝ y) + (y ＝ 𝕥)
   I (inl q)  _        = inr (inr (to-ℍ-＝' y 𝕥 ((λ _ → ⋆) , (λ _ → q))))
   I (inr _)  (inl p)  = inl (to-ℍ-＝' 𝕥 x ((λ _ → p) , (λ _ → ⋆)))
   I (inr qp) (inr pq) = inr (inl (to-ℍ-＝' x y (pq , qp)))

   II : ∥ (𝕥 ＝ x) + (x ＝ y) + (y ＝ 𝕥) ∥
   II = ∥∥-functor₂ I QP PQ

\end{code}

And so ℍ has at most two elements, in the sense that among any three
elements of ℍ, two of them are equal.

\begin{code}

 ℍ-has-at-most-two-elements
  : (x y z : ℍ)
  → ∥ (z ＝ x) + (x ＝ y) + (y ＝ z) ∥
 ℍ-has-at-most-two-elements x y z
  = V
  where
   I : ∥ (𝕥 ＝ x) + (x ＝ y) + (y ＝ 𝕥) ∥
   I = ℍ-has-at-most-two-elements-lemma x y

   II : ∥ (𝕥 ＝ y) + (y ＝ z) + (z ＝ 𝕥) ∥
   II = ℍ-has-at-most-two-elements-lemma y z

   III : ∥ (𝕥 ＝ z) + (z ＝ x) + (x ＝ 𝕥) ∥
   III = ℍ-has-at-most-two-elements-lemma z x

   IV : (𝕥 ＝ x) + (x ＝ y) + (y ＝ 𝕥)
      → (𝕥 ＝ y) + (y ＝ z) + (z ＝ 𝕥)
      → (𝕥 ＝ z) + (z ＝ x) + (x ＝ 𝕥)
      → (z ＝ x) + (x ＝ y) + (y ＝ z)
   IV (inl a)       (inl b)       _             = inr (inl (a ⁻¹ ∙ b))
   IV (inl _)       (inr (inl b)) _             = inr (inr b)
   IV (inl a)       (inr (inr b)) _             = inl (b ∙ a)
   IV (inr (inl a)) (inl _)       _             = inr (inl a)
   IV (inr (inr _)) (inl b)       (inl c)       = inr (inr (b ⁻¹ ∙ c))
   IV (inr (inr _)) (inl _)       (inr (inl c)) = inl c
   IV (inr (inr _)) (inl b)       (inr (inr c)) = inr (inl (c ∙ b))
   IV (inr (inl a)) (inr _)       _             = inr (inl a)
   IV (inr (inr _)) (inr (inl b)) _             = inr (inr b)
   IV (inr (inr a)) (inr (inr b)) _             = inr (inr (a ∙ b ⁻¹))

   V : ∥ (z ＝ x) + (x ＝ y) + (y ＝ z) ∥
   V = ∥∥-functor₃ IV I II III

\end{code}

We have the following corollary.

\begin{code}

 Aut-Ω-has-at-most-two-elements
  : (f g h : Aut Ω)
  → ∥ (h ＝ f) + (f ＝ g) + (g ＝ h) ∥
 Aut-Ω-has-at-most-two-elements f g h
  = II
  where
   ϕ = ⌜ ℍ-to-Aut-Ω-equivalence ⌝⁻¹
   ϕ-lc = equivs-are-lc ϕ ⌜ ℍ-to-Aut-Ω-equivalence ⌝⁻¹-is-equiv

   I : ∥ (ϕ h ＝ ϕ f) + (ϕ f ＝ ϕ g) + (ϕ g ＝ ϕ h) ∥
   I = ℍ-has-at-most-two-elements (ϕ f) (ϕ g) (ϕ h)

   II : ∥ (h ＝ f) + (f ＝ g) + (g ＝ h) ∥
   II = ∥∥-functor (+functor₂ ϕ-lc ϕ-lc ϕ-lc) I

\end{code}

By the above development, the assertion that Aut Ω is a singleton (or
equivalently a proposition, because it is pointed) is a stronger
principle than the negation of the law of excluded middle.
