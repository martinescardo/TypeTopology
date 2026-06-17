Fredrik Bakke, 16–17 June 2026.

We demonstrate that any type A that has a commutative and idempotent binary
action _*_ with eventually idempotent right action at every element is a set.

 Theorem.
 Given a type A with a binary operation _*_ which satisfies the equations

  x * x = x                              (idempotence)
  x * y = y * x                          (commutativity)

 for all x and y, and such that for each y there is a natural number n such that
 the following equation holds

  rⁿ⁺¹(x) = rⁿ(x), where r(x) := x * y

 then A is a set.

This theorem provides a generalisation of David Wärn's proof [1] that types
equipped with the algebraic structure of a semilattice forms a set. We elaborate
on the properness of this generalisation in the final section of this file. Our
work builds on the adaptated formalisation of this result by Tom de Jong [2].
See also Martín Escardó's adaptation [3] of this result.


[1] David Wärn. https://dwarn.se/agda/Idem.html, 17 February 2026.
    (See also https://mathstodon.xyz/deck/@dwarn/116091515645003634.)

[2] Tom de Jong. AlgebraicStructuresForcingSethood.Semilattices-streamlined.lagda,
    25—27 February 2026

[3] Martín Escardó. AlgebraicStructuresForcingSethood.Semilattices.lagda,
    23 February 2026.

TODO: elaborate on proof

\begin{code}

{-# OPTIONS --safe --without-K #-}

module AlgebraicStructuresForcingSethood.CommutativeIdempotent where

open import MLTT.Universes
open import MLTT.Id
open import MLTT.NaturalNumbers
open import UF.Base
open import UF.Sets using
 (is-set ; refl-is-set)
open import AlgebraicStructuresForcingSethood.Semilattices-streamlined using
 (module idempotent)
open import AlgebraicStructuresForcingSethood.CommutativeLoopSpaces using
 (module idempotent-commutative-operation)

\end{code}

Loop space criterion
────────────────────────────────────────────────────────────────────────────────

\begin{code}

ΩA : {A  : 𝓤 ̇} → A → 𝓤 ̇
ΩA x₀ = (x₀ ＝ x₀)

module _ (A  : 𝓤 ̇) (x₀ : A) where

 iterate-is-refl-reflects
  : (f g : ΩA x₀ → ΩA x₀)
  → ((p : ΩA x₀) → g (f p) ＝ p)
  → g refl ＝ refl
  → (n : ℕ)
  → (p : ΩA x₀)
  → (f ^ n) p ＝ refl
  → p ＝ refl
 iterate-is-refl-reflects f g gf g-refl 0 p e
  = e
 iterate-is-refl-reflects f g gf g-refl (succ n) p e
  = p       ＝⟨ gf p ⁻¹ ⟩
    g (f p) ＝⟨ ap g fp-trivial ⟩
    g refl  ＝⟨ g-refl ⟩
    refl    ∎
    where
     fp-trivial : f p ＝ refl
     fp-trivial
       = iterate-is-refl-reflects f g gf g-refl n
          (f p)
          (^-succ f n p ∙ e)

 trivial-Ω-eventually-idempotent-endomap-criterion
  : (f : ΩA x₀ → ΩA x₀)
    (n : ℕ)
  → ((p : ΩA x₀) → (f ^ n) p ＝ (f ^ succ n) p)
  → ((p : ΩA x₀) → f p ∙ f p ＝ p)
  → (p : ΩA x₀) → p ＝ refl
 trivial-Ω-eventually-idempotent-endomap-criterion
  f n r f-self-concat p =
  iterate-is-refl-reflects f (λ p → p ∙ p) f-self-concat refl n p (cancel-left I)
   where
   I : (f ^ n) p ∙ (f ^ n) p ＝ (f ^ n) p ∙ refl
   I = (f ^ n) p ∙ (f ^ n) p           ＝⟨ ap (λ q → q ∙ q) (r p) ⟩
       (f ^ succ n) p ∙ (f ^ succ n) p ＝⟨ f-self-concat ((f ^ n) p) ⟩
       (f ^ n) p                       ＝⟨ refl-right-neutral ((f ^ n) p) ⟩
       (f ^ n) p ∙ refl                ∎

\end{code}

Iterating the induced map on the loop space of a pointed endomap
────────────────────────────────────────────────────────────────────────────────

\begin{code}

module pointed-endomap-iterates
 {A  : 𝓤 ̇}
 (x₀ : A)
 (f  : A → A)
 (η  : f x₀ ＝ x₀)
 where

 Ω-map : ΩA x₀ → ΩA x₀
 Ω-map p = conjugate-loop η (ap f p)

 fixed^ : (n : ℕ) → (f ^ n) x₀ ＝ x₀
 fixed^ 0 = refl
 fixed^ (succ n) = ap f (fixed^ n) ∙ η

 Ω-map^ : (n : ℕ) → ΩA x₀ → ΩA x₀
 Ω-map^ n p = conjugate-loop (fixed^ n) (ap (f ^ n) p)

 ap-iterate-succ
  : {x y : A} (n : ℕ) (p : x ＝ y)
  → ap (f ^ succ n) p ＝ ap f (ap (f ^ n) p)
 ap-iterate-succ n refl = refl

 Ω-map-iterates : (n : ℕ) (p : ΩA x₀)
                → (Ω-map ^ n) p ＝ Ω-map^ n p
 Ω-map-iterates 0 p = ap-id-is-id p ⁻¹
 Ω-map-iterates (succ n) p =
  let
   β = fixed^ n
   r = ap (f ^ n) p
  in
  Ω-map ((Ω-map ^ n) p)                               ＝⟨ ap Ω-map (Ω-map-iterates n p) ⟩
  Ω-map (Ω-map^ n p)                                  ＝⟨ ap (conjugate-loop η) (ap-conjugate-loop f β r) ⟩
  conjugate-loop η (conjugate-loop (ap f β) (ap f r)) ＝⟨ ＝-congr-∙' (ap f β) η (ap f β) η (ap f r) ⁻¹ ⟩
  conjugate-loop (ap f β ∙ η) (ap f r)                ＝⟨ ap (conjugate-loop (fixed^ (succ n))) (ap-iterate-succ n p ⁻¹) ⟩
  Ω-map^ (succ n) p                                   ∎

\end{code}

\begin{code}

 conjugate-loop-is-id
  : ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → (β p : ΩA x₀)
  → conjugate-loop β p ＝ p
 conjugate-loop-is-id loop-comm β p =
  cancel-left (＝-congr-sq p β β ∙ loop-comm p β)

 homotopic-conjugations
  : {y z : A}
    (h : y ＝ z) (β : y ＝ x₀) (γ : z ＝ x₀)
    {r : y ＝ y} {s : z ＝ z}
  → h ∙ s ∙ h ⁻¹ ＝ r
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → conjugate-loop β r ＝ conjugate-loop γ s
 homotopic-conjugations refl β refl {r} e loop-comm =
  conjugate-loop-is-id loop-comm β r ∙ e ⁻¹ ∙ refl-left-neutral

 homotopic-Ω-map^
  : (m n : ℕ)
  → ((x : A) → (f ^ m) x ＝ (f ^ n) x)
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → (p : ΩA x₀)
  → Ω-map^ m p ＝ Ω-map^ n p
 homotopic-Ω-map^ m n H loop-comm p =
  homotopic-conjugations
   (H x₀)
   (fixed^ m)
   (fixed^ n)
   (homotopies-are-natural' (f ^ m) (f ^ n) H {p = p})
   (loop-comm)

 Ω-map-eventually-idempotent
  : (n : ℕ)
  → ((x : A) → (f ^ n) x ＝ (f ^ succ n) x)
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → (p : ΩA x₀)
  → (Ω-map ^ n) p ＝ (Ω-map ^ succ n) p
 Ω-map-eventually-idempotent n r loop-comm p =
  (Ω-map ^ n) p      ＝⟨ Ω-map-iterates n p ⟩
  Ω-map^ n p         ＝⟨ homotopic-Ω-map^ n (succ n) r loop-comm p ⟩
  Ω-map^ (succ n) p  ＝⟨ Ω-map-iterates (succ n) p ⁻¹ ⟩
  (Ω-map ^ succ n) p ∎

\end{code}

Commutative idempotent binary operations with eventually idempotent right action
────────────────────────────────────────────────────────────────────────────────

We now return to a commutative idempotent binary operation on A.

TODO: text

\begin{code}

module comm-idem
 (A    : 𝓤 ̇)
 (_*_  : A → A → A)
 (comm : (x y : A) → x * y ＝ y * x)
 (idem : (x : A) → x * x ＝ x)
 where

\end{code}

TODO: text

\begin{code}
 module pointed (x₀ : A) where

  open idempotent-commutative-operation A x₀ _*_ idem comm
  open pointed-endomap-iterates x₀ (_* x₀) (idem x₀)
  open idempotent.pointed A _*_ idem x₀

  Ω-map-is-＊Ω-refl : (p : ΩA x₀) → Ω-map p ＝ p ＊Ω refl
  Ω-map-is-＊Ω-refl p =
   ap (conjugate-loop (idem x₀)) ((ap₂-refl-right (_*_) {y = x₀} p) ⁻¹)

  Ω-map-self-concat : (p : ΩA x₀) → Ω-map p ∙ Ω-map p ＝ p
  Ω-map-self-concat p =
   Ω-map p ∙ Ω-map p           ＝⟨ ap₂ (_∙_) (Ω-map-is-＊Ω-refl p) (Ω-map-is-＊Ω-refl p) ⟩
   (p ＊Ω refl) ∙ (p ＊Ω refl) ＝⟨ ap ((p ＊Ω refl) ∙_) (＊Ω-commutative comm p refl) ⟩
   (p ＊Ω refl) ∙ (refl ＊Ω p) ＝⟨ ＊Ω-interchange-∙ p refl refl p ⟩
   (p ∙ refl) ＊Ω (refl ∙ p)   ＝⟨ ap₂ _＊Ω_ (refl-right-neutral p) refl-left-neutral ⟩
   p ＊Ω p                     ＝⟨ ＊Ω-idempotent p ⟩
   p                           ∎

  ΩA-is-trivial
   : (n₀ : ℕ) (r : (x : A) → ((_* x₀) ^ n₀) x ＝ ((_* x₀) ^ succ n₀) x)
   → (p : ΩA x₀) → p ＝ refl
  ΩA-is-trivial n₀ r₀ =
   trivial-Ω-eventually-idempotent-endomap-criterion A x₀
    Ω-map n₀ (Ω-map-eventually-idempotent n₀ r₀ ∙-is-commutative) Ω-map-self-concat

\end{code}

Now, assuming that the right action at every element is eventually idempotent
we obtain that A is a set.

\begin{code}

 A-is-set
  : (n : A → ℕ)
    (r : (y x : A) → ((_* y) ^ n y) x ＝ ((_* y) ^ succ (n y)) x)
  → is-set A
 A-is-set n r = refl-is-set A (λ x → pointed.ΩA-is-trivial x (n x) (r x))

\end{code}

Properness of the generalisation
────────────────────────────────────────────────────────────────────────────────

This theorem gives a proper generalisation of David Wärn's result [1] that types
equipped with the algebraic structure of a semilattice are sets. Recall that
algebraic structure of a semilattice is that of an associative, commutative, and
idempotent binary operation. Associative idempotent binary operations have
idempotent right action:

 (x * y) * y = x * (y * y) = x * y,

but commutative idempotent binary operations with idempotent right action need
not be associative.

 Counterexample.
 The following 3-element table defines a commutative and idempotent binary
 operation with an idempotent right action that is not associative:

  * │ 0 1 2
  ──┼──────
  0 │ 0 0 2
  1 │ 0 1 1
  2 │ 2 1 2

 Indeed, we may evaluate

  (0 * 1) * 2 = 0 * 2 = 2   and   0 * (1 * 2) = 0 * 1 = 0,

 so associativity would entail 2 = 0. This operation is commutative since the
 table is symmetric across the diagonal, and idempotent since the diagonal
 matches the row and column labels. We may validate it has an idempotent right
 action by brute computation:

  (0 * 0) * 0 = 0 * 0
  (1 * 0) * 0 = 0 * 0 = 0 = 1 * 0
  (2 * 0) * 0 = 2 * 0

  (0 * 1) * 1 = 0 * 1
  (1 * 1) * 1 = 1 * 1
  (2 * 1) * 1 = 1 * 1

  (0 * 2) * 2 = 2 * 2 = 2 = 0 * 2
  (1 * 2) * 2 = 1 * 2
  (2 * 2) * 2 = 2 * 2.


Eventual idempotence of the right action is also a proper generalisation of
idempotence of the right action for commutative idempotent binary operations.

 Counterexample.
 The following 4-element table defines a binary operation that is commutative
 and idempotent, whose right action is not idempotent at any element,
 but which satisfies (((x * y) * y) * y) = ((x * y) * y) for all x and y:

  * │ 0 1 2 3
  ──┼────────
  0 │ 0 0 0 1
  1 │ 0 1 3 1
  2 │ 0 3 2 0
  3 │ 1 1 0 3
