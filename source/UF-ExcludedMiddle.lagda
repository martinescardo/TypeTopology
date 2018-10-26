Martin Escardo.

Excluded middle related things.

In the Curry-Howard interpretation, excluded middle say that every
type has an inhabitant or os empty. In univalent foundations, where
one works with propositions as subsimgletons, excluded middle is the
principle that every subsingleton type is inhabited or empty.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-ExcludedMiddle where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Embedding
open import UF-PropTrunc

\end{code}

Excluded middle (EM) is not provable or disprovable. However, we do
have that there is no truth value other than false (⊥) or true (⊤),
which we refer to as the density of the decidable truth values.

\begin{code}

EM : ∀ U → U ′ ̇
EM U = (P : U ̇) → is-prop P → P + ¬ P

WEM : ∀ U → U ′ ̇
WEM U = (P : U ̇) → is-prop P → ¬ P + ¬¬ P

DNE : ∀ U → U ′ ̇
DNE U = (P : U ̇) → is-prop P → ¬¬ P → P

EM-gives-DNE : EM U → DNE U
EM-gives-DNE em P isp φ = cases (λ p → p) (λ u → 𝟘-elim (φ u)) (em P isp)

DNE-gives-EM : funext U U₀ → DNE U → EM U
DNE-gives-EM fe dne P isp = dne (P + ¬ P)
                             (decidable-is-prop fe isp)
                             (λ u → u (inr (λ p → u (inl p))))

fem-proptrunc : funext U U₀ → EM U → propositional-truncations-exist U U
fem-proptrunc fe em X = ¬¬ X ,
                        (Π-is-prop fe (λ _ → 𝟘-is-prop) ,
                         (λ x u → u x) ,
                         λ P isp u φ → EM-gives-DNE em P isp (¬¬-functor u φ))

module _ (pt : PropTrunc) where

 open PropositionalTruncation pt

 double-negation-is-truncation-gives-DNE :((X : U ̇) → ¬¬ X → ∥ X ∥) → DNE U
 double-negation-is-truncation-gives-DNE {U} f P isp u = ptrec isp id (f P u)

\end{code}
