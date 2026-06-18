Fredrik Bakke, 16–17 June 2026.

We demonstrate that any type A that has a commutative and idempotent binary
action _*_ with eventually idempotent right action is a set.

 Theorem.
 Given a type A with a binary operation _*_ which satisfies the equations

  x * y = y * x                          (commutativity)
  x * x = x                              (idempotence)

 for all x and y, and eventual idempotence of the right action, meaning that for
 each y there is a natural number n such that the following equation holds

  rⁿ⁺¹(x) = rⁿ(x), where r(x) := x * y   (eventual idempotence of right action)

 then A is a set.

This theorem provides a generalisation of David Wärn's result [1] that types
equipped with the algebraic structure of a semilattice forms a set. We elaborate
on the properness of this generalisation in the final section of this file. Our
work builds on the adaptated formalisation of this result by Tom de Jong [2].
See also Martín Escardó's adaptation [3].

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
open import MLTT.Id using
 (_＝_ ; refl ; _∙_ ; _⁻¹ ; ap ; _＝⟨_⟩_ ; _∎)
open import MLTT.NaturalNumbers using
 (ℕ ; zero ; succ ; _^_ ; ^-succ ; ap-iterate-succ)
open import UF.Base using
 ( conjugate-loop
 ; cancel-left
 ; refl-right-neutral
 ; ap-id-is-id'
 ; ap-conjugate-loop
 ; conjugate-loop-refl
 ; conjugate-loop-conjugates
 ; homotopies-are-natural''
 ; ap₂
 ; refl-left-neutral
 ; ap₂-refl-right'
 ; ＝-congr-∙'
 ; ＝-congr-sq)
open import UF.Sets using
 (is-set ; refl-is-set')
open import AlgebraicStructuresForcingSethood.Semilattices-streamlined using
 (module idempotent)
open import AlgebraicStructuresForcingSethood.CommutativeLoopSpaces using
 (module idempotent-commutative-operation)

\end{code}

Loop space criterion
────────────────────────────────────────────────────────────────────────────────

TODO: explain criterion

\begin{code}

ΩA : {A  : 𝓤 ̇} → A → 𝓤 ̇
ΩA x₀ = (x₀ ＝ x₀)

module _ (A  : 𝓤 ̇) (x₀ : A) where

 iterate-reflects-is-refl
  : (f g : ΩA x₀ → ΩA x₀)
  → ((p : ΩA x₀) → g (f p) ＝ p)
  → refl ＝ g refl
  → (n : ℕ)
  → (p : ΩA x₀)
  → refl ＝ (f ^ n) p
  → refl ＝ p
 iterate-reflects-is-refl f g gf g-refl 0 p e = e
 iterate-reflects-is-refl f g gf g-refl (succ n) p e
  = refl       ＝⟨ g-refl ⟩
    g refl     ＝⟨ ap g refl-is-fp ⟩
    g (f p)    ＝⟨ gf p ⟩
    p          ∎
    where
     refl-is-fp : refl ＝ f p
     refl-is-fp
      = iterate-reflects-is-refl f g gf g-refl n (f p) (e ∙ ^-succ f n p)

 trivial-Ω-eventually-idempotent-endomap-criterion
  : (f : ΩA x₀ → ΩA x₀)
    (n : ℕ)
  → ((p : ΩA x₀) → (f ^ n) p ＝ (f ^ succ n) p)
  → ((p : ΩA x₀) → f p ∙ f p ＝ p)
  → (p : ΩA x₀) → refl ＝ p
 trivial-Ω-eventually-idempotent-endomap-criterion
  f n r f-self-concat p =
  iterate-reflects-is-refl f (λ p → p ∙ p) f-self-concat refl n p (II ⁻¹)
   where
    I : (f ^ n) p ∙ (f ^ n) p ＝ (f ^ n) p
    I = (f ^ n) p ∙ (f ^ n) p           ＝⟨ ap (λ q → q ∙ q) (r p) ⟩
        (f ^ succ n) p ∙ (f ^ succ n) p ＝⟨ f-self-concat ((f ^ n) p) ⟩
        (f ^ n) p                       ∎

    II : (f ^ n) p ＝ refl
    II = cancel-left (I ∙ refl-right-neutral ((f ^ n) p))

\end{code}

Iteration of the induced map on the loop space of a pointed endomap
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

 preserves-point^ : (n : ℕ) → (f ^ n) x₀ ＝ x₀
 preserves-point^ 0 = refl
 preserves-point^ (succ n) = ap f (preserves-point^ n) ∙ η

 Ω-map^-conj : (n : ℕ) → ΩA x₀ → ΩA x₀
 Ω-map^-conj n p = conjugate-loop (preserves-point^ n) (ap (f ^ n) p)

 Ω-map-iterates : (n : ℕ) (p : ΩA x₀)
                → (Ω-map ^ n) p ＝ Ω-map^-conj n p
 Ω-map-iterates 0 p = ap-id-is-id' p
 Ω-map-iterates (succ n) p =
  let
   β = preserves-point^ n
   r = ap (f ^ n) p
  in
  Ω-map ((Ω-map ^ n) p)                               ＝⟨ ap Ω-map (Ω-map-iterates n p) ⟩
  Ω-map (Ω-map^-conj n p)                             ＝⟨ ap (conjugate-loop η) (ap-conjugate-loop f β r) ⟩
  conjugate-loop η (conjugate-loop (ap f β) (ap f r)) ＝⟨ ＝-congr-∙' (ap f β) η (ap f β) η (ap f r) ⁻¹ ⟩
  conjugate-loop (ap f β ∙ η) (ap f r)                ＝⟨ ap (conjugate-loop (preserves-point^ (succ n))) (ap-iterate-succ n p) ⟩
  Ω-map^-conj (succ n) p                              ∎

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
  → conjugate-loop h r ＝ s
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → conjugate-loop β r ＝ conjugate-loop γ s
 homotopic-conjugations refl β refl {r} {s} e loop-comm
  = conjugate-loop β r    ＝⟨ conjugate-loop-is-id loop-comm β r ⟩
    r                     ＝⟨ conjugate-loop-refl r ⟩
    conjugate-loop refl r ＝⟨ e ⟩
    s                     ＝⟨ conjugate-loop-refl s ⟩
    conjugate-loop refl s ∎

 homotopic-Ω-map^-conj
  : (m n : ℕ)
  → ((x : A) → (f ^ m) x ＝ (f ^ n) x)
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → (p : ΩA x₀)
  → Ω-map^-conj m p ＝ Ω-map^-conj n p
 homotopic-Ω-map^-conj m n H loop-comm p =
  homotopic-conjugations
   (H x₀)
   (preserves-point^ m)
   (preserves-point^ n)
   ( conjugate-loop-conjugates (H x₀) (ap (f ^ m) p)
   ∙ homotopies-are-natural'' (f ^ m) (f ^ n) H {p = p})
   (loop-comm)

 Ω-map-eventually-idempotent
  : (n : ℕ)
  → ((x : A) → (f ^ n) x ＝ (f ^ succ n) x)
  → ((p q : ΩA x₀) → p ∙ q ＝ q ∙ p)
  → (p : ΩA x₀)
  → (Ω-map ^ n) p ＝ (Ω-map ^ succ n) p
 Ω-map-eventually-idempotent n r loop-comm p =
  (Ω-map ^ n) p          ＝⟨ Ω-map-iterates n p ⟩
  Ω-map^-conj n p        ＝⟨ homotopic-Ω-map^-conj n (succ n) r loop-comm p ⟩
  Ω-map^-conj (succ n) p ＝⟨ Ω-map-iterates (succ n) p ⁻¹ ⟩
  (Ω-map ^ succ n) p     ∎

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
   ap (conjugate-loop (idem x₀)) (ap₂-refl-right' (_*_) p)

  Ω-map-self-concat : (p : ΩA x₀) → Ω-map p ∙ Ω-map p ＝ p
  Ω-map-self-concat p =
   Ω-map p ∙ Ω-map p          ＝⟨ ap₂ (_∙_) (Ω-map-is-＊Ω-refl p) (Ω-map-is-＊Ω-refl p) ⟩
   (p ＊Ω refl) ∙ (p ＊Ω refl) ＝⟨ ap ((p ＊Ω refl) ∙_) (＊Ω-commutative comm p refl) ⟩
   (p ＊Ω refl) ∙ (refl ＊Ω p) ＝⟨ ＊Ω-interchange-∙ p refl refl p ⟩
   (p ∙ refl) ＊Ω (refl ∙ p)  ＝⟨ ap₂ (_＊Ω_) (refl-right-neutral p) (refl-left-neutral) ⟩
   p ＊Ω p                    ＝⟨ ＊Ω-idempotent p ⟩
   p                          ∎

  ΩA-is-trivial
   : (n₀ : ℕ) (r : (x : A) → ((_* x₀) ^ n₀) x ＝ ((_* x₀) ^ succ n₀) x)
   → (p : ΩA x₀) → refl ＝ p
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
 A-is-set n r = refl-is-set' A (λ x → pointed.ΩA-is-trivial x (n x) (r x))

\end{code}

Properness of the generalisation
────────────────────────────────────────────────────────────────────────────────

This theorem gives a proper generalisation of Wärn's result [1] that types
equipped with the algebraic structure of a semilattice are sets. Recall that the
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
 and idempotent, whose right action is not idempotent at any element, but which
 satisfies (((x * y) * y) * y) = ((x * y) * y) for all x and y:

  * │ 0 1 2 3
  ──┼────────
  0 │ 0 0 0 1
  1 │ 0 1 3 1
  2 │ 0 3 2 0
  3 │ 1 1 0 3

 We leave verifying these laws as an exercise to the reader.

 You can also see the laws it satisfies and refutes here:
 https://teorth.github.io/equational_theories/fme/?magma=0%200%200%201%0A0%201%203%201%0A0%203%202%200%0A1%201%200%203
 where the relevant laws correspond to the following numbers:
  #     3 is the idempotence law
  #    43 is the commutative law
  #   378 is the idempotence law for the right action
  #  4512 is the associative law
  # 62068 is the second order idempotence law for the right action


I originally wanted see if some of the results from the Equational Theories
Project [4] could aid in generalising Wärn's result, but unfortunately their
project is too limited in scope for this problem. This is because they only
consider equational theories with a single equation. They also do not consider
parametric laws such as eventual idempotence.

 [4] Bolan, M., Breitner, J., Brox, J., Carlini, N., Carneiro, M.,
     van Doorn, F., Dvorak, M., Goens, A., Hill, A., Husum, H.,
     Ibarra Mejia, H., Kocsis, Z. A., Le Floch, B., Livne Bar-on, A.,
     Luccioli, L., McNeil, D., Meiburg, A., Monticone, P., Nielsen, P.,
     Osazuwa, E. O., Paolini, G., Petracci, M., Reinke, B., Renshaw, D.,
     Rossel, M., Roux, C., Scanvic, J., Srinivas, S., Tadipatri, A. R., Tao, T.,
     Tsyrklevich, V., Vaquerizo-Villar, F., Weber, D., & Zheng, F. (2025).
     The Equational Theories Project (Version 0.2.0) [Computer software].
     https://teorth.github.io/equational_theories/
