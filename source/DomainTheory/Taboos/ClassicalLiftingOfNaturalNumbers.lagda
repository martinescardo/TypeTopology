Tom de Jong, 22 & 23 June 2024

We formalize what we've known for a long time: if the poset pictured below

   0   1   2   3   ...
     \ \   / /
      \ \ / /
         ⊥

is ω-complete/directed complete, then Bishop's LPO holds.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Taboos.ClassicalLiftingOfNaturalNumbers
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀

open import CoNaturals.Type renaming (ℕ∞-to-ℕ→𝟚 to ε)
open import MLTT.Two-Properties
open import MLTT.Plus-Properties
open import Notation.CanonicalMap
open import Taboos.LPO (λ 𝓤 𝓥 → fe)

\end{code}

The poset is defined as follows. Notice that the set of natural numbers is
ordered discretely.

NB: In this file, and this file only, we denote this poset by ℕ⊥. In
CoNaturals/Sharp this notation is reserved for the lifting of the natural
numbers which constructively *does* yield a directed complete
poset. Classically, the constructions are equivalent, as formalized in
Lifting.Miscelanea-PropExt-FunExt. Indeed, this is the case *only* classically,
as this file shows by deriving a constructive taboo from the assumption that ℕ⊥
is directed complete.

\begin{code}

ℕ⊥ : 𝓤₀ ̇
ℕ⊥ = 𝟙{𝓤₀} + ℕ

_⊑_ : ℕ⊥ → ℕ⊥ → 𝓤₀ ̇
inl ⋆ ⊑ x = 𝟙
inr n ⊑ x = inr n ＝ x

\end{code}

We now state the main results, postponing the proof.

In fact, we show that just having upper bounds of ω-chains (so not necessarily
least ones) gives LPO.

\begin{code}

ℕ⊥-is-ω-complete-gives-LPO : is-ω-complete _⊑_ → LPO

ℕ⊥-is-directed-complete-gives-LPO : is-directed-complete _⊑_ → LPO

ℕ⊥-has-upperbounds-for-ω-chains-gives-LPO :
   ((α : ℕ → ℕ⊥)
       → is-ω-chain _⊑_ α
       → (Σ x ꞉ ℕ⊥ , is-upperbound _⊑_ x α))
 → LPO

\end{code}

We need a few preliminaries before giving the proof.

\begin{code}

inr-not-⊑-inl : {n : ℕ} → ¬ (inr n ⊑ inl ⋆)
inr-not-⊑-inl p = +disjoint (p ⁻¹)

⊑-refl : (x : ℕ⊥) → x ⊑ x
⊑-refl (inl ⋆) = ⋆
⊑-refl (inr n) = refl

⊑-refl-＝ : {x y : ℕ⊥} → x ＝ y → x ⊑ y
⊑-refl-＝ refl = ⊑-refl _

⊑-trans : (x y z : ℕ⊥) → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans (inl ⋆) y z p q = ⋆
⊑-trans (inr n) y z refl q = q

\end{code}

We now prove the main result.

In TypeTopology, LPO states that is decidable whether a decreasing binary sequence
u : ℕ∞ is finite or not. The equivalence with the traditional formulation is
formalized in Taboos.LPO.

We write ε u n for evaluating the binary sequence u at index n.

Given such u, we construct χ : ℕ → ℕ⊥ such that

   • χ n = ⊥ = inl ⋆ ⇔ ε u n = ₁;
   • χ n = inr m     ⇔ m is the least integer ≤ n such that ε u m = ₀.

We then show that χ is an ω-chain and that from an upper bound we can decide,
via some case splitting, whether u is finite or not, i.e., whether u is always ₁
or attains ₀ somewhere.

\begin{code}

private
 module construction (u : ℕ∞) where

  χ : ℕ → ℕ⊥
  χ n = 𝟚-equality-cases I II
   where
    I : ε u n ＝ ₀ → ℕ⊥
    I p = inr (size (bounded-is-finite fe n u p))
    II : ε u n ＝ ₁ → ℕ⊥
    II _ = inl ⋆

  module _
          {n : ℕ}
          (p : ε u n ＝ ₀)
         where

   χ-numeral : ℕ
   χ-numeral = size (bounded-is-finite fe n u p)

   χ-eq : χ n ＝ inr χ-numeral
   χ-eq = 𝟚-equality-cases₀ p

   χ-numeral-eq : ℕ-to-ℕ∞ χ-numeral ＝ u
   χ-numeral-eq = size-property (bounded-is-finite fe n u p)

  χ-otherwise : {n : ℕ} → ε u n ＝ ₁ → χ n ＝ inl ⋆
  χ-otherwise p = 𝟚-equality-cases₁ p

  χ-is-ω-chain : (n : ℕ) → χ n ⊑ χ (succ n)
  χ-is-ω-chain n = 𝟚-equality-cases I II
   where
    II : ε u n ＝ ₁ → χ n ⊑ χ (succ n)
    II p = transport⁻¹ (_⊑ χ (succ n)) (χ-otherwise p) ⋆
    I : ε u n ＝ ₀ → χ n ⊑ χ (succ n)
    I p = ⊑-refl-＝ I₁
     where
      q : ε u (succ n) ＝ ₀
      q = stays-zero u p
      I₁ = χ n               ＝⟨ χ-eq p ⟩
           inr (χ-numeral p) ＝⟨ I₂ ⟩
           inr (χ-numeral q) ＝⟨ (χ-eq q) ⁻¹ ⟩
           χ (succ n)        ∎
       where
        I₂ = ap inr (ℕ-to-ℕ∞-lc (χ-numeral-eq p ∙ (χ-numeral-eq q) ⁻¹))

  inl-case : is-upperbound _⊑_ (inl ⋆) χ
           → is-decidable (is-finite' u)
  inl-case ub = inr I
   where
    I : ¬ (is-finite' u)
    I (n , refl) = inr-not-⊑-inl II
     where
      p : ε u n ＝ ₀
      p = ℕ-to-ℕ∞-diagonal₀ n
      II : inr (χ-numeral p) ⊑ inl ⋆
      II = transport (_⊑ inl ⋆) (χ-eq p) (ub n)

  inr-case : {m : ℕ} → is-upperbound _⊑_ (inr m) χ
           → is-decidable (is-finite' u)
  inr-case {m} ub = 𝟚-equality-cases I II
   where
    I : ε u m ＝ ₀ → is-decidable (is-finite' u)
    I p = inl (χ-numeral p , ((χ-numeral-eq p) ⁻¹))
    II : ε u m ＝ ₁ → is-decidable (is-finite' u)
    II p = inr III
     where
      III : ¬ is-finite' u
      III (n , refl) = diff (inr-lc eq)
       where
        q : ε u n ＝ ₀
        q = ℕ-to-ℕ∞-diagonal₀ n

        eq = inr n             ＝⟨ (ap inr (ℕ-to-ℕ∞-lc (χ-numeral-eq q)))⁻¹ ⟩
             inr (χ-numeral q) ＝⟨ transport (_⊑ inr m) (χ-eq q) (ub n) ⟩
             inr m             ∎

        diff : n ≠ m
        diff e = zero-is-not-one (₀     ＝⟨ (ℕ-to-ℕ∞-diagonal₀ n) ⁻¹ ⟩
                                  ε u n ＝⟨ ap (ε u) e ⟩
                                  ε u m ＝⟨ p ⟩
                                  ₁     ∎)

\end{code}

This completes the technical details and we are ready to give the proofs.

\begin{code}

ℕ⊥-has-upperbounds-for-ω-chains-gives-LPO ν seq =
 equality-cases s (I s s-is-ub) (II s s-is-ub)
  where
   open construction seq
   module _
           (s : ℕ⊥)
           (s-is-ub : is-upperbound _⊑_ s χ)
          where
    I : (u : 𝟙) → s ＝ inl u → is-decidable (is-finite' seq)
    I ⋆ refl = inl-case s-is-ub
    II : (m : ℕ) → s ＝ inr m → is-decidable (is-finite' seq)
    II m refl = inr-case s-is-ub

   s : ℕ⊥
   s = pr₁ (ν χ χ-is-ω-chain)
   s-is-ub : is-upperbound _⊑_ s χ
   s-is-ub = pr₂ (ν χ χ-is-ω-chain)

ℕ⊥-is-ω-complete-gives-LPO comp =
 ℕ⊥-has-upperbounds-for-ω-chains-gives-LPO
  (λ α c → the-sup _⊑_ (comp α c) ,
           sup-is-upperbound _⊑_ (sup-property _⊑_ (comp α c)))

ℕ⊥-is-directed-complete-gives-LPO comp =
 ℕ⊥-is-ω-complete-gives-LPO
  (λ α c → comp ℕ α (ω-chains-are-directed _⊑_ ⊑-refl ⊑-trans α c))

\end{code}
