Martin Escardo and Paulo Oliva, November 2026.

Decidable strict weak orders.

A strict weak order on a type V is a relation _<_ that is
irreflexive, transitive and cotransitive, where cotransitivity says
that a < b implies a < c or c < b, for every c. We consider strict
weak orders that are moreover decidable.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module OrderedTypes.DecidableStrictWeakOrder where

open import MLTT.Spartan

record Decidable-Strict-Weak-Order {𝓥 : Universe} (V : 𝓥 ̇ ) (𝓣 : Universe)
       : 𝓥 ⊔ 𝓣 ⁺ ̇ where
 field
  _<_            : V → V → 𝓣 ̇
  <-decidable    : (a b : V) → is-decidable (a < b)
  <-irreflexive  : (a : V) → ¬ (a < a)
  <-transitive   : (a b c : V) → a < b → b < c → a < c
  <-cotransitive : (a b c : V) → a < b → (a < c) + (c < b)

\end{code}

We write a ≤ b for the negation of b < a, which is a total preorder.
Conversely, for a decidable total preorder ≤, the negation of b ≤ a is
a decidable strict weak order, and so the two notions are
interdefinable in the presence of decidability. We take the strict
order as primitive, and name the record after it. The word weak says
that distinct elements may be incomparable, and we then say that they
are tied. In constructive mathematics, a linear order is a strict
order that is moreover tight, with incomparable elements equal, and so
a decidable linear order is a decidable strict weak order without
ties.

\begin{code}

 _≤_ : V → V → 𝓣 ̇
 a ≤ b = ¬ (b < a)

 ≤-decidable : (a b : V) → is-decidable (a ≤ b)
 ≤-decidable a b = Cases (<-decidable b a) (λ l → inr (λ h → h l)) inl

 ≤-refl : (a : V) → a ≤ a
 ≤-refl = <-irreflexive

 <-gives-≤ : {a b : V} → a < b → a ≤ b
 <-gives-≤ {a} {b} l m = <-irreflexive a (<-transitive a b a l m)

 ≤-trans : {a b c : V} → a ≤ b → b ≤ c → a ≤ c
 ≤-trans {a} {b} {c} l m n = Cases (<-cotransitive c a b n) m l

 <-≤-trans : {a b c : V} → a < b → b ≤ c → a < c
 <-≤-trans {a} {b} {c} l m =
  Cases (<-cotransitive a b c l) id (λ n → 𝟘-elim (m n))

 ≤-<-trans : {a b c : V} → a ≤ b → b < c → a < c
 ≤-<-trans {a} {b} {c} l m =
  Cases (<-cotransitive b c a m) (λ n → 𝟘-elim (l n)) id

\end{code}

The binary maximum, which keeps the left argument in case of a tie.

\begin{code}

 maxδ : (a b : V) → is-decidable (a < b) → V
 maxδ a b (inl _) = b
 maxδ a b (inr _) = a

 max : V → V → V
 max a b = maxδ a b (<-decidable a b)

 max-＝-right : {a b : V} → a < b → max a b ＝ b
 max-＝-right {a} {b} l = I (<-decidable a b)
  where
   I : (d : is-decidable (a < b)) → maxδ a b d ＝ b
   I (inl _) = refl
   I (inr n) = 𝟘-elim (n l)

 max-＝-left : {a b : V} → b ≤ a → max a b ＝ a
 max-＝-left {a} {b} l = I (<-decidable a b)
  where
   I : (d : is-decidable (a < b)) → maxδ a b d ＝ a
   I (inl m) = 𝟘-elim (l m)
   I (inr _) = refl

\end{code}

The opposite of a decidable strict weak order is again a decidable
strict weak order.

\begin{code}

opposite : {𝓥 𝓣 : Universe} {V : 𝓥 ̇ }
         → Decidable-Strict-Weak-Order V 𝓣
         → Decidable-Strict-Weak-Order V 𝓣
opposite O = record
 { _<_            = λ a b → b < a
 ; <-decidable    = λ a b → <-decidable b a
 ; <-irreflexive  = <-irreflexive
 ; <-transitive   = λ a b c l m → <-transitive c b a m l
 ; <-cotransitive = λ a b c l → Cases (<-cotransitive b a c l) inr inl
 }
 where
  open Decidable-Strict-Weak-Order O

\end{code}
