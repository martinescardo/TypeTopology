Martin Escardo, 17th August 2024 and 18th September 2024.

We develop and generalize a result from 2013/03/13 first advertised in
the IAS Univalent Foundations mailing list in response to a question
by Andrej Bauer [1]:

If A : ℕ → 𝓤 is a family of decidable types,
then

   ∥ Σ n ꞉ ℕ , A n ∥ → Σ n ꞉ ℕ , A n.

This may seem surprising at first sight. The original proof in [1]
uses function extensionality and the assumption that A is
proposition-valued to show that the type

  A m × ((k : ℕ) → A k → m ≤ k)

is a proposition for any m. But, using the results of [2] (or its
extended version [3]), we can remove both assumptions.

Moreover, in [4] we show that, more generally, if A : ℕ → 𝓤 is a
family of propositions such that A (n + 1) implies that A n is
decidable, then

   ∥ Σ n ꞉ ℕ , A n ∥ → Σ n ꞉ ℕ , A n,

again with a proof that assumes function extensionality. Here, using
[2], we are able to remove the assumption of function extensionality,
but not the assumption that A is proposition-valued.

Moreover, we can construct the propositional truncation of the type
Σ n ꞉ ℕ , A n in pure Spartan MLTT without assuming that propositional
truncations exist in general, by considering the type of fixed points
of a minimization endomap of Σ n ꞉ ℕ , A n. See the module UF.ExitPropTrunc.

[1] Martin Escardo. 2013/03/13 message to the IAS Univalent Foundations
    mailing list.
    https://groups.google.com/g/univalent-foundations/c/SA0dzenV1G4/m/d5iIGdKKNxMJ

[2] Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
    Generalizations of Hedberg’s Theorem.
    TLCA 2013
    https://doi.org/10.1007/978-3-642-38946-7_14

[3] Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
    Notions of Anonymous Existence in Martin-Löf Type Theory.
    Logical Methods in Computer Science, March 24, 2017, Volume 13, Issue 1.
    https://doi.org/10.23638/LMCS-13(1:15)2017

[4] Martín H. Escardó and Chuangjie Xu. The inconsistency of a
    Brouwerian continuity principle with the Curry-Howard
    interpretation. 13th International Conference on Typed Lambda
    Calculi and Applications (TLCA 2015).

    https://drops.dagstuhl.de/opus/portals/lipics/index.php?semnr=15006
    https://doi.org/10.4230/LIPIcs.TLCA.2015.153

    Although it was presented with a different proof that assumes function
    extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.ExitTruncation where

open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import NotionsOfDecidability.Decidable
open import UF.Hedberg
open import UF.ExitPropTrunc
open import UF.PropTrunc
open import UF.Subsingletons

module _ (A : ℕ → 𝓤 ̇ )
         (δ : (n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
       where

 minimal-witness⁺ : (Σ n ꞉ ℕ , A n)
                  → Σ k ꞉ ℕ , (A k × ((i : ℕ) → A i → k ≤ i))
 minimal-witness⁺ = uncurry (μ A δ)
  where
   μ : (A : ℕ → 𝓤 ̇ )
     → ((n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
     → (n : ℕ)
     → A n
     → Σ k ꞉ ℕ , (A k × ((i : ℕ) → A i → k ≤ i))
   μ A δ 0        a₀   = 0 , a₀ , (λ i aᵢ → zero-least i)
   μ A δ (succ n) aₙ₊₁ = II
    where
     IH : Σ j ꞉ ℕ , ((A (succ j) × ((i : ℕ) → A (succ i) → j ≤ i)))
     IH = μ (A ∘ succ) (λ n aₙ₊₁ j → δ (succ n) aₙ₊₁ (succ j)) n aₙ₊₁

     I : type-of IH
       → Σ k ꞉ ℕ , A k × ((i : ℕ) → A i → k ≤ i)
     I (j , aⱼ₊₁ , b) =
      Cases (δ (succ n) aₙ₊₁ 0 (zero-least j))
       (λ (a₀ :    A 0) → (0      , a₀   , (λ i aᵢ → zero-least i)))
       (λ (ν₀  : ¬ A 0) → (succ j , aⱼ₊₁ , I₀ ν₀))
        where
         I₀ : ¬ A 0 → (i : ℕ) (aᵢ : A i) → j < i
         I₀ ν₀ 0        a₀   = 𝟘-elim (ν₀ a₀)
         I₀ ν₀ (succ i) aᵢ₊₁ = b i aᵢ₊₁

     II : Σ k ꞉ ℕ , (A k ×  ((i : ℕ) → A i → k ≤ i))
     II = I IH

\end{code}

We name the projections for convenience.

\begin{code}

 minimal-number : Σ A → ℕ
 minimal-number σ = pr₁ (minimal-witness⁺ σ)

 minimal-number-requirement : (σ : Σ A) → A (minimal-number σ)
 minimal-number-requirement σ = pr₁ (pr₂ (minimal-witness⁺ σ))

 minimality : (σ : Σ A) → (i : ℕ) → A i → minimal-number σ ≤ i
 minimality σ = pr₂ (pr₂ (minimal-witness⁺ σ))

 minimal-pair : Σ A → Σ A
 minimal-pair σ = minimal-number σ , minimal-number-requirement σ

 minimal-pair-wconstant : is-prop-valued-family A → wconstant minimal-pair
 minimal-pair-wconstant A-prop-valued σ σ' =
  to-subtype-＝ A-prop-valued
   (need
     minimal-number σ ＝ minimal-number σ'
    which-is-given-by
     ≤-anti _ _
      (minimality σ  (minimal-number σ') (minimal-number-requirement σ'))
      (minimality σ' (minimal-number σ)  (minimal-number-requirement σ)))

\end{code}

A particular case.

\begin{code}

minimal-witness : (A : ℕ → 𝓤 ̇ )
                → ((n : ℕ) → is-decidable (A n))
                → (Σ n ꞉ ℕ , A n)
                → Σ m ꞉ ℕ , (A m × ((k : ℕ) → A k → m ≤ k))
minimal-witness A δ = minimal-witness⁺ A (λ n aₙ k l → δ k)

\end{code}

We apply the above to exit truncations.

\begin{code}

module exit-truncations (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open split-support-and-collapsibility pt

 module _ (A : ℕ → 𝓤 ̇ )
          (A-is-prop-valued : is-prop-valued-family A)
          (δ : (n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
        where

  exit-truncation⁺ : ∥ Σ A ∥ → Σ A
  exit-truncation⁺ = collapsible-gives-split-support
                      (minimal-pair A δ ,
                       minimal-pair-wconstant A δ A-is-prop-valued)
\end{code}

Not only can we exit the truncation, but also we can say that the
result is minimal.

\begin{code}

  exit-truncation⁺-minimality
   : (s : ∥ Σ A ∥) (i : ℕ) → A i → pr₁ (exit-truncation⁺ s) ≤ i
  exit-truncation⁺-minimality s = IV
   where
    I : minimal-pair A δ (exit-truncation⁺ s) ＝ exit-truncation⁺ s
    I = exit-prop-trunc-is-fixed
         (minimal-pair A δ)
         (minimal-pair-wconstant A δ A-is-prop-valued)
         s

    II : minimal-number A δ (exit-truncation⁺ s) ＝ pr₁ (exit-truncation⁺ s)
    II = ap pr₁ I

    III : (i : ℕ) → A i → minimal-number A δ (exit-truncation⁺ s) ≤ i
    III = minimality A δ (exit-truncation⁺ s)

    IV : (i : ℕ) → A i → pr₁ (exit-truncation⁺ s) ≤ i
    IV = transport (λ - → (i : ℕ) → A i → - ≤ i) II III

\end{code}

In the following particular case of interest, the prop-valuedness
assumption can be removed.

\begin{code}

 module _ (A : ℕ → 𝓤 ̇ )
          (d : (n : ℕ) → is-decidable (A n))
        where

  private
    B : ℕ → 𝓤₀ ̇
    B n = ∥ A n ∥⟨ d n ⟩

    B-is-prop-valued : is-prop-valued-family B
    B-is-prop-valued n = ∥∥⟨ d n ⟩-is-prop

    δ : (n : ℕ) → B n → (k : ℕ) → k < n → is-decidable (B k)
    δ n bₙ k l = ∥∥⟨ d k ⟩-is-decidable

    f : Σ A → Σ B
    f (n , aₙ) = n , ∣ aₙ ∣⟨ d n ⟩

    g : Σ B → Σ A
    g (n , bₙ) = (n , ∣∣⟨ d n ⟩-exit bₙ)

  exit-truncation : ∥ Σ A ∥ → Σ A
  exit-truncation t = g (exit-truncation⁺ B B-is-prop-valued δ (∥∥-functor f t))

  exit-truncation-minimality
   : (t : ∥ Σ A ∥) (i : ℕ) → A i → pr₁ (exit-truncation t) ≤ i
  exit-truncation-minimality t i a =
   exit-truncation⁺-minimality
    B
    B-is-prop-valued
    δ
    (∥∥-functor f t)
    i
    ∣ a ∣⟨ d i ⟩

\end{code}

TODO. Can we remove the prop-valuedness assumption in general?

Added 19th September 2024.

The following is useful in practice to fulfill a hypothesis of
exit-truncation⁺.

\begin{code}

regression-lemma₀
 : (A : ℕ → 𝓤 ̇ )
 → ((n : ℕ) → A (succ n) → is-decidable (A n))
 → ((n : ℕ) → A n → A (succ n))
 → (n : ℕ) → A (succ n) → is-decidable (A 0)
regression-lemma₀ A f g 0        = f 0
regression-lemma₀ A f g (succ n) = I
 where
  IH : A (succ (succ n)) → is-decidable (A 1)
  IH = regression-lemma₀ (A ∘ succ) (f ∘ succ) (g ∘ succ) n

  I : A (succ (succ n)) → is-decidable (A 0)
  I a = Cases (IH a)
         (λ (a₁ :   A 1) → f 0 a₁)
         (λ (ν  : ¬ A 1) → inr (contrapositive (g 0) ν))

regression-lemma
 : (A : ℕ → 𝓤 ̇ )
 → ((n : ℕ) → A (succ n) → is-decidable (A n))
 → ((n : ℕ) → A n → A (succ n))
 → (n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k)
regression-lemma A f g 0        a k        l = 𝟘-elim l
regression-lemma A f g (succ n) a 0        l = regression-lemma₀ A f g n a
regression-lemma A f g (succ n) a (succ k) l = regression-lemma
                                                (A ∘ succ)
                                                (f ∘ succ)
                                                (g ∘ succ)
                                                n a k l
\end{code}

Notice that these functions don't actually use the full force of the
assumption

 (n : ℕ) → A n → A (succ n)

but only its contrapositive. So there is a more general result that
assumes

 (n : ℕ) → ¬ A (succ n) → ¬ A n

instead, although I don't think this will ever be needed. If it is, we
can come back here and do a little bit of refactoring.
