Evan Cavallo, 2nd July 2025, updated 3rd July 2025.

A proof that the natural numbers form a set that does not use a universe, in
response to a question asked by Naïm Favier on Mastodon:

 https://types.pl/@ncf/114779291760324789
 https://mathstodon.xyz/@ecavallo/114780841234656632

In Martin-Löf type theory without a universe or large elimination from ℕ, it is
impossible to prove that 0 ≠ 1:

 Jan M. Smith. The independence of Peano's fourth axiom from Martin-Löf's type
 theory without universes. The Journal of Symbolic Logic, Volume 53, Issue 3,
 September 1988, pp. 840–845. doi:10.2307/2274575.
 https://www.cse.chalmers.se/~smith/JSLPeano.pdf

Thus, we cannot take the usual route of showing that ℕ has decidable equality
and then applying Hedberg's theorem.

There are multiple proofs of the same result in this file: the first one is the
original, and the others are subsequent simplifications. At the end, there is
also a proof that if A is a set then List A is a set.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Id
open import MLTT.NaturalNumbers
open import MLTT.Pi
open import MLTT.Plus
open import MLTT.Sigma
open import MLTT.List
open import UF.Base using (ap₂)
open import UF.Hedberg
open import UF.Sets using (is-set)
open import UF.Subsingletons using (is-prop)
open import UF.Subsingletons-Properties using (props-are-sets)
open import Naturals.Properties using (pred)

module Various.NatIsSetWithoutUniverse where

\end{code}

First we show that if 0 ＝ succ n for some n : ℕ, then ℕ is an h-proposition.
This will be used in all the proofs.

\begin{code}

[0＝succ]-implies-ℕ-is-prop : {n : ℕ} → 0 ＝ succ n → is-prop ℕ
[0＝succ]-implies-ℕ-is-prop eq m k = ap distinguish eq
 where
  distinguish : ℕ → ℕ
  distinguish 0 = m
  distinguish (succ _) = k

\end{code}

For the first proof we follow the standard proof that ℕ is a set from Hedberg's
theorem, but we use is-prop ℕ as a substitute for the empty type. This proof
strategy is inspired by Friedman's A-translation (or "Friedman's trick") from

 Harvey Friedman. Classically and intuitionistically provably recursive functions.
 In: Higher Set Theory. Lecture Notes in Mathematics, Volume 669, 1978, pp 21–27,
 doi:10.1007/BFb0103100.

Another option would be to use 0 ＝ 1 instead of is-prop ℕ.

We can't show that ℕ has decidable equality, but we can show that any m,n : ℕ
are either equal or their equality would imply that ℕ is a proposition (thus
contractible):

\begin{code}

ℕ-＝-holds-or-makes-ℕ-prop
 : (m n : ℕ) → (m ＝ n) + ((m ＝ n) → is-prop ℕ)
ℕ-＝-holds-or-makes-ℕ-prop zero zero =
 inl refl
ℕ-＝-holds-or-makes-ℕ-prop zero (succ n) =
 inr [0＝succ]-implies-ℕ-is-prop
ℕ-＝-holds-or-makes-ℕ-prop (succ m) zero =
 inr ([0＝succ]-implies-ℕ-is-prop ∘ _⁻¹)
ℕ-＝-holds-or-makes-ℕ-prop (succ m) (succ n) =
 bump (ℕ-＝-holds-or-makes-ℕ-prop m n)
 where
  bump : ((m ＝ n) + ((m ＝ n) → is-prop ℕ))
       → (succ m ＝ succ n) + ((succ m ＝ succ n) → is-prop ℕ)
  bump (inl eq) = inl (ap succ eq)
  bump (inr neq) = inr (neq ∘ ap pred)

\end{code}

From this decision procedure we derive double "negation" elimination for
equality in ℕ in the usual way. Here, we need that our "empty type" is-prop ℕ
implies whatever equality in ℕ we need.

\begin{code}

ℕ-＝-double-[to-is-prop]-elim-helper
 : (m n : ℕ)
 → ((m ＝ n) + ((m ＝ n) → is-prop ℕ))
 → (((m ＝ n) → is-prop ℕ) → is-prop ℕ) → m ＝ n
ℕ-＝-double-[to-is-prop]-elim-helper m n (inl eq) _ = eq
ℕ-＝-double-[to-is-prop]-elim-helper m n (inr neq) nneq = nneq neq m n

ℕ-＝-double-[to-is-prop]-elim
 : (m n : ℕ) → (((m ＝ n) → is-prop ℕ) → is-prop ℕ) → m ＝ n
ℕ-＝-double-[to-is-prop]-elim m n =
 ℕ-＝-double-[to-is-prop]-elim-helper m n (ℕ-＝-holds-or-makes-ℕ-prop m n)

\end{code}

To apply a Hedberg-like argument, we will also need to know that double
"negation" elimination is weakly constant. Here, we need that our "empty type"
is-prop ℕ implies that all elements of identity types in ℕ are equal (i.e., ℕ is
a set).

If we assumed function extensionality, ((m ＝ n) → is-prop ℕ) → is-prop ℕ) would
be a proposition and this would be immediate.

\begin{code}

ℕ-＝-double-[to-is-prop]-elim-is-wconstant
 : (m n : ℕ) → wconstant (ℕ-＝-double-[to-is-prop]-elim m n)
ℕ-＝-double-[to-is-prop]-elim-is-wconstant m n =
 ℕ-＝-double-[to-is-prop]-elim-helper-is-wconstant
  (ℕ-＝-holds-or-makes-ℕ-prop m n)
 where
  ℕ-＝-double-[to-is-prop]-elim-helper-is-wconstant
   : (dec : (m ＝ n) + ((m ＝ n) → is-prop ℕ))
   → wconstant (ℕ-＝-double-[to-is-prop]-elim-helper m n dec)
  ℕ-＝-double-[to-is-prop]-elim-helper-is-wconstant (inl eq) _ _ =
   refl
  ℕ-＝-double-[to-is-prop]-elim-helper-is-wconstant (inr neq) nneq _ =
   props-are-sets (nneq neq) _ _

\end{code}

We can use the following variation on Hedberg's theorem to prove the main
result. (Although the type signature involves two universes, we use these
hypotheses only as types / type families.)

\begin{code}

reflexive-relation-that-wconstantly-implies-equality-gives-set
 : {X : 𝓤 ̇ }
 → (_R_ : X → X → 𝓥 ̇ )
 → ((x : X) → x R x)
 → (e : (x y : X) → x R y → x ＝ y)
 → ((x y : X) → wconstant (e x y))
 → is-set X
reflexive-relation-that-wconstantly-implies-equality-gives-set
 {𝓤} {𝓥} {X} _R_ r e ec = γ
 where
  f : {x y :  X} → x ＝ y → x ＝ y
  f {x} {y} p = e x y (transport (x R_) p (r x))

  κ : {x y : X} → wconstant (f {x} {y})
  κ p q = ec _ _ _ _

  γ : is-set X
  γ = Id-collapsibles-are-sets (f , κ)

ℕ-is-set-without-universe : is-set ℕ
ℕ-is-set-without-universe =
 reflexive-relation-that-wconstantly-implies-equality-gives-set
  (λ m n → ((m ＝ n) → is-prop ℕ) → is-prop ℕ)
  (λ n neq → neq refl)
  ℕ-＝-double-[to-is-prop]-elim
  ℕ-＝-double-[to-is-prop]-elim-is-wconstant

\end{code}

The above proof can be shortened if we inline the Hedberg lemma. Upon inlining,
we see that "f" in the lemma above uses the transport in the family

  n : ℕ ⊢ ((m ＝ n) → is-prop ℕ) → is-prop ℕ

of

  (λ neq → neq refl) : ((m ＝ m) → is-prop ℕ) → is-prop ℕ

along some p : m ＝ n. Using the usual simplifications of transport in function
and identity types, the result is equal to (λ neq → neq p). Making that
substitution, we have:

\begin{code}

ℕ-is-set-without-universe' : is-set ℕ
ℕ-is-set-without-universe' =
  Id-collapsibles-are-sets
   ( (λ p → ℕ-＝-double-[to-is-prop]-elim _ _ (λ neq → neq p))
   , (λ p q → ℕ-＝-double-[to-is-prop]-elim-is-wconstant _ _ _ _)
   )

\end{code}

Added by Evan Cavallo, 3rd July 2025.

We can give a significantly simpler proof that ℕ is a set by proving that ℕ's
identity types are collapsible directly by induction, rather going through a
"decision" procedure first.

Beware that Agda's coverage checker would let us leave out the "impossible"
cases of these inductions, but those omissions are not justified in MLTT without
a universe!

\begin{code}

ℕ-＝-collapse : (m n : ℕ) → m ＝ n → m ＝ n
ℕ-＝-collapse zero zero _ = refl
ℕ-＝-collapse zero (succ n) p = [0＝succ]-implies-ℕ-is-prop p _ _
ℕ-＝-collapse (succ m) zero p = [0＝succ]-implies-ℕ-is-prop (p ⁻¹) _ _
ℕ-＝-collapse (succ m) (succ n) p = ap succ (ℕ-＝-collapse m n (ap pred p))

ℕ-＝-collapse-is-wconstant : (m n : ℕ) → wconstant (ℕ-＝-collapse m n)
ℕ-＝-collapse-is-wconstant zero zero _ _ = refl
ℕ-＝-collapse-is-wconstant zero (succ n) p _  =
 props-are-sets ([0＝succ]-implies-ℕ-is-prop p) _ _
ℕ-＝-collapse-is-wconstant (succ m) zero p _ =
 props-are-sets ([0＝succ]-implies-ℕ-is-prop (p ⁻¹)) _ _
ℕ-＝-collapse-is-wconstant (succ m) (succ n) p q =
 ap (ap succ) (ℕ-＝-collapse-is-wconstant m n (ap pred p) (ap pred q))

ℕ-is-Id-collapsible : Id-collapsible ℕ
ℕ-is-Id-collapsible = (ℕ-＝-collapse _ _ , ℕ-＝-collapse-is-wconstant _ _)

ℕ-is-set-without-universe'' : is-set ℕ
ℕ-is-set-without-universe'' = Id-collapsibles-are-sets ℕ-is-Id-collapsible

\end{code}

An advantage of the preceding proof is that we can apply the same argument to
types that we don't expect to have decidable equality (even with a universe).
For example, we can show that if A is a set then List A is a set:

\begin{code}

module _ {A : 𝓤 ̇ } (setA : is-set A) where

 [nil＝cons]-implies-List-is-prop
  : {x : A} {xs : List A} → [] ＝ x ∷ xs → is-prop (List A)
 [nil＝cons]-implies-List-is-prop p ys zs = ap distinguish p
  where
   distinguish : List A → List A
   distinguish [] = ys
   distinguish (_ ∷ _) = zs

 safe-head : A → List A → A
 safe-head a [] = a
 safe-head a (x ∷ xs) = x

 tail : List A → List A
 tail [] = []
 tail (x ∷ xs) = xs

 List-＝-collapse : (xs ys : List A) → xs ＝ ys → xs ＝ ys
 List-＝-collapse [] [] p = refl
 List-＝-collapse [] (y ∷ ys) p = [nil＝cons]-implies-List-is-prop p _ _
 List-＝-collapse (x ∷ xs) [] p = [nil＝cons]-implies-List-is-prop (p ⁻¹) _ _
 List-＝-collapse (x ∷ xs) (y ∷ ys) p =
  ap₂ _∷_ (ap (safe-head x) p) (List-＝-collapse xs ys (ap tail p))

 List-＝-collapse-is-wconstant
  : (xs ys : List A) → wconstant (List-＝-collapse xs ys)
 List-＝-collapse-is-wconstant [] [] p q = refl
 List-＝-collapse-is-wconstant [] (y ∷ ys) p q =
  props-are-sets ([nil＝cons]-implies-List-is-prop p) _ _
 List-＝-collapse-is-wconstant (x ∷ xs) [] p q =
  props-are-sets ([nil＝cons]-implies-List-is-prop (p ⁻¹)) _ _
 List-＝-collapse-is-wconstant (x ∷ xs) (y ∷ ys) p q =
   ap₂
    (ap₂ _∷_)
    (setA _ _)
    (List-＝-collapse-is-wconstant xs ys (ap tail p) (ap tail q))

 List-is-Id-collapsible : Id-collapsible (List A)
 List-is-Id-collapsible = (List-＝-collapse _ _ , List-＝-collapse-is-wconstant _ _)

 List-is-set-without-universe : is-set (List A)
 List-is-set-without-universe =
  Id-collapsibles-are-sets List-is-Id-collapsible

\end{code}
