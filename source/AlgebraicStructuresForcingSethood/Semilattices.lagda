Martin Escardo 23rd Feb 2026. A result by David Wärn [1].

Moved from `gist` to this place 17th April 2026.

Merged basic library into UF.Base on 3—4 June 2026 by Tom de Jong.

Any type equipped with a binary operation _*_ that is associative,
commutative and idempotent is a set (homotopy 0-type). That is, there
are no higher semilattices! This file is my attempt to understand
David's Agda file [1].

[1] David Wärn. https://dwarn.se/agda/Idem.html , 17 February 2026.
    (See also https://mathstodon.xyz/deck/@dwarn/116091515645003634)

I add, in the discussion of the formal definitions and proofs, some
diagrams and some explanations, and rename some things, which I hope
are correct and what David intended. You may wish to also have a look
at yet another version [2].

[2] Tom de Jong. AlgebraicStructuresForcingSethood.Semilattices-streamlined.lagda,
    25-27 February 2026.
    (See also https://mathstodon.xyz/deck/@de_Jong_Tom/116141966476412629)

Proof sketch (formalized in the anonymous module at the very end of
this file). Fix a type A and an x₀ : A, and write ΩA = (x₀ ＝ x₀). An
operation _*_ on A induces an operation _⋆_ on ΩA.  The main steps
are, for suitably defined act-l and act-r,

  (i)   p ⋆ p ＝ p                             (⋆-idemp)
  (ii)  p ⋆ q ＝ act-l p ∙ act-r q             (⋆-in-terms-of-∙)
  (iii) p ⋆ q ＝ q ⋆ p                         (comm-loop)
  (iv)  act-l p ＝ act-r p                     (only-one-act)
  (v)   act-l p ∙ act-l p ＝ p                 (act-l-idemp)
  (vi)  act-l p ∙ act-l q ＝ act-l q ∙ act-l p (comm-l)

An Eckmann–Hilton argument using (v) and (vi) gives the following:

  (vii) p ∙ q ＝ q ∙ p                         (loop-comm)

Finally, using the associativity of *, we get that

  (viii) act-l (act-l p) ＝ act-l p            (act-l-idem)
  (ix)   act-l p ＝ refl                       (act-l-trivial)
  (x)    p ＝ refl                             (Ω-null)

In the spirit of the original file [1], we only use minimal imports
from TypeTopology, to show that a relatively short argument in a
rather Spartan MLTT is possible - we only need Π-types and identity
types. (We also don't make real use of universe polymorphism.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module AlgebraicStructuresForcingSethood.Semilattices where

open import MLTT.Universes
open import MLTT.Id
open import UF.Base using
  ( ap₂
  ; refl-left-neutral
  ; refl-right-neutral
  ; cancel-left
  ; ＝-congr
  ; ＝-congr-refl
  ; ＝-congr-∙
  ; ＝-congr-∙'
  ; ＝-congr-nat
  ; ＝-congr-⁻¹
  ; ＝-congr-sq
  ; comm₂
  )

\end{code}

We fix a type A with an associative, commutative, idempotent
operation, and a base-point x₀.

\begin{code}

module _
         (A     : 𝓤 ̇ )
         (_*_   : A → A → A)
         (idem  : (a : A) → a * a ＝ a)
         (comm  : (a b : A) → a * b ＝ b * a)
         (assoc : (a b c : A) → (a * b) * c ＝ a * (b * c))
         (x₀    : A)
       where

  ΩA : 𝓤 ̇
  ΩA = x₀ ＝ x₀

\end{code}

The operation * acts on paths componentwise:

    a₁ ══ p ══ a₂       b₁ ══ q ══ b₂

                                         ↝   a₁*b₁ ══ p ★ q ══ a₂*b₂.

It also splits into a left part followed by a right part:

    a₁*b₁ ══ ap (-*b₁) p ══ a₂*b₁ ══ ap (a₂*-) q ══ a₂*b₂.

\begin{code}

  _★_ : {a₁ a₂ b₁ b₂ : A} → a₁ ＝ a₂ → b₁ ＝ b₂ → a₁ * b₁ ＝ a₂ * b₂
  _★_ = ap₂ _*_

  ★-in-terms-of-∙ : {a₁ a₂ b₁ b₂ : A} (p : a₁ ＝ a₂) (q : b₁ ＝ b₂)
                  → p ★ q ＝ ap (_* b₁) p ∙ ap (a₂ *_) q
  ★-in-terms-of-∙ refl refl = refl

\end{code}

The function `reduce` uses idempotence to turn a loop at x₀ * x₀ into
a loop at x₀:

       idem x₀
   x₀ ════════ x₀*x₀
   ║             ║
   ║             ║
   ║             ║
   x₀ ════════ x₀*x₀
       idem x₀

\begin{code}

  reduce : x₀ * x₀ ＝ x₀ * x₀ → ΩA
  reduce = ＝-congr (idem x₀) (idem x₀)

\end{code}

Given loops p, q : x₀ ＝ x₀, we form the loop at x₀*x₀ via _★_, then
reduce it:

    x₀*x₀ ══════ p ★ q ══════ x₀*x₀
      ║                         ║
    idem x₀                   idem x₀
      ║                         ║
     x₀ ═══════════════════════ x₀
                 p ⋆ q

It splits as act-l p ∙ act-r q:

    x₀*x₀ ═ ap(-*x₀) p ═ x₀*x₀ ═ ap(x₀*-) q ═══ x₀*x₀
      ║                    ║                      ║
    idem x₀              idem x₀                idem x₀
      ║                    ║                      ║
     x₀ ═════ act-l p ════ x₀ ═════ act-r q ═════ x₀

With this we have that _★_ induces an operation _⋆_ on loops.

\begin{code}

  _⋆_ : ΩA → ΩA → ΩA
  p ⋆ q = reduce (p ★ q)

  act-l : ΩA → ΩA
  act-l p = reduce (ap (_* x₀) p)

  act-r : ΩA → ΩA
  act-r q = reduce (ap (x₀ *_) q)

  ⋆-in-terms-of-∙ : (p q : ΩA) → p ⋆ q ＝ act-l p ∙ act-r q
  ⋆-in-terms-of-∙ p q =
   ap reduce (★-in-terms-of-∙ _ _)
   ∙ ＝-congr-∙ (idem x₀) (idem x₀) (idem x₀) (ap (_* x₀) p) (ap (x₀ *_) q)

\end{code}

We now show that _⋆_ is idempotent.

When both arguments are equal, p ★ p reduces to p via the idempotence
of *, for any p : a ＝ b:

    a*a ══════ p ★ p ═════ b*b
     ║                      ║
   idem a                 idem b
     ║                      ║
     a ═════════ p ════════ b

\begin{code}

  ★-idemp : {a b : A} (p : a ＝ b)
          → ＝-congr (idem a) (idem b) (p ★ p) ＝ p
  ★-idemp refl = ＝-congr-refl (idem _)

  ⋆-idemp : (p : ΩA) → p ⋆ p ＝ p
  ⋆-idemp = ★-idemp

\end{code}

Next, we show that _⋆_ is commutative.

We use the commutativity of * as a base-point-preserving loop
comm-self : x₀ ＝ x₀, and show that equality congruence by it swaps _⋆_.

comm-loop-raw builds the following stacked rectangle:

    x₀*x₀ ═══ p ★ q ════ x₀*x₀       (top, before reduce)
      ║                    ║
    comm x₀ x₀           comm x₀ x₀  (side paths via commutativity)
      ║                    ║
    x₀*x₀ ═══ q ★ p ════ x₀*x₀       (comm-paths flips the args)
      ║                    ║
    idem x₀              idem x₀
      ║                    ║
     x₀ ═════ q ⋆ p ══════ x₀

Stacking the rectangles gives

  eq-congr comm-self comm-self (p ⋆ q) ＝ q ⋆ p.

The function comm-self-center then shows that comm-self is central
(equality congruence with it is the identity), by specializing to p = q
and using ⋆-idemp.

\begin{code}

  comm-paths : {a b x y : A} (p : a ＝ x) (q : b ＝ y)
             → ＝-congr (comm a b) (comm x y) (p ★ q) ＝ q ★ p
  comm-paths refl refl = ＝-congr-refl (comm _ _)

  comm-self : ΩA
  comm-self = reduce (comm x₀ x₀)

  comm-loop-raw : (p q : ΩA)
                → ＝-congr comm-self comm-self (p ⋆ q) ＝ q ⋆ p
  comm-loop-raw p q =
    ＝-congr
     (＝-congr-nat (comm x₀ x₀) (comm x₀ x₀) (idem x₀) (idem x₀) (p ★ q))
     refl
     (ap reduce (comm-paths p q))

  comm-self-center : (p : ΩA) → ＝-congr comm-self comm-self p ＝ p
  comm-self-center p =
   ＝-congr
    (ap (＝-congr comm-self comm-self) (⋆-idemp p))
    (⋆-idemp p)
    (comm-loop-raw p p)

  comm-loop : (p q : ΩA) → p ⋆ q ＝ q ⋆ p
  comm-loop p q = ＝-congr (comm-self-center _) refl (comm-loop-raw p q)

\end{code}

The function `act-swap` defined below follows from comm-loop via the
splitting ⋆-in-terms-of-∙:

  act-l p ∙ act-r q
    ＝ p ⋆ q              (by ⋆-in-terms-of-∙)
    ＝ q ⋆ p              (by comm-loop)
    ＝ act-l q ∙ act-r p

To deduce act-l ＝ act-r, we specialize to q = refl:

  act-l p ∙ act-r refl ＝ act-l refl ∙ act-r p
      act-l p ∙ refl  ＝ refl ∙ act-r p
            act-l p  ＝ act-r p

\begin{code}

  act-swap : (p q : ΩA) → act-l p ∙ act-r q ＝ act-l q ∙ act-r p
  act-swap p q = ＝-congr
                  (⋆-in-terms-of-∙ p q)
                  (⋆-in-terms-of-∙ q p)
                  (comm-loop p q)

  act-l-refl : act-l refl ＝ refl
  act-l-refl = ＝-congr-refl (idem x₀)

  act-r-refl : act-r refl ＝ refl
  act-r-refl = ＝-congr-refl (idem x₀)

  only-one-act : (p : ΩA) → act-l p ＝ act-r p
  only-one-act p = ＝-congr
                    (ap (act-l p ∙_) act-r-refl ∙ refl-right-neutral _)
                    (ap (_∙ act-r p) act-l-refl ∙ refl-left-neutral)
                    (act-swap p refl)

\end{code}

Using an Eckmann–Hilton argument, we show that loop concatenation is
commutative.

We now know

  (v)  act-l p ∙ act-l p ＝ p                  (using act-l ＝ act-r)
  (vi) act-l p ∙ act-l q ＝ act-l q ∙ act-l p  (comm-l, using act-swap)

Then

  p ∙ q
   ＝ (act-l p ∙ act-l p) ∙ (act-l q ∙ act-l q) (by act-l-idemp twice)
   ＝ (act-l q ∙ act-l q) ∙ (act-l p ∙ act-l p) (by comm₂, using comm-l)
   ＝ q ∙ p

\begin{code}

  act-l-idemp : (p : ΩA) → act-l p ∙ act-l p ＝ p
  act-l-idemp p =
   ap (act-l p ∙_) (only-one-act p)
   ∙ ＝-congr (⋆-in-terms-of-∙ p p) refl (⋆-idemp p)

  comm-l : (p q : ΩA) → act-l p ∙ act-l q ＝ act-l q ∙ act-l p
  comm-l p q =
   ＝-congr
    (ap (act-l p ∙_) ((only-one-act q) ⁻¹))
    (ap (act-l q ∙_) ((only-one-act p) ⁻¹))
    (act-swap p q)

  loop-comm : (p q : ΩA) → p ∙ q ＝ q ∙ p
  loop-comm p q =
   ＝-congr
    (ap₂ _∙_ (act-l-idemp p) (act-l-idemp q))
    (ap₂ _∙_ (act-l-idemp q) (act-l-idemp p))
    (comm₂ {p = act-l p} {q = act-l q} (comm-l p q))

\end{code}

We now show that _⋆_ is associative.

The function assoc-paths defined below says that * acts functorially
on 2×1 grids of paths:

    (a*b)*c ══ (p ★ q) ★ r ══ (x*y)*z
        ║                         ║
   assoc a b c               assoc x y z
        ║                         ║
    a*(b*c) ══ p ★ (q ★ r) ══ x*(y*z)

We compare two reductions of the triple self-product x₀*x₀*x₀, one
for each parenthesization:

    (x₀*x₀)*x₀ ══ idem-triple-l ══ x₀
    x₀*(x₀*x₀) ══ idem-triple-r ══ x₀

The function path assoc-self is the loop

    x₀         ═ (by sym idem-triple-l)
    (x₀*x₀)*x₀ ═ (by assoc)
    x₀*(x₀*x₀) ═ (by idem-triple-r)
    x₀

that witnesses the path between the two constructions.  Equality
congruence with assoc-self gives ⋆-assoc-raw.  Since ΩA is commutative
(loop-comm) and the equality congruence witness satisfies the square
identity (＝-congr-sq), we can use ∙-cancel to strip assoc-self and
obtain ⋆-assoc.

\begin{code}

  assoc-paths : {a b c x y z : A} (p : a ＝ x) (q : b ＝ y) (r : c ＝ z)
              → ＝-congr (assoc a b c) (assoc x y z) ((p ★ q) ★ r)
              ＝ p ★ (q ★ r)
  assoc-paths refl refl refl = ＝-congr-refl (assoc _ _ _)

  idem-triple-l : (x₀ * x₀) * x₀ ＝ x₀
  idem-triple-l = (idem x₀ ★  refl) ∙ idem x₀

  idem-triple-r : x₀ * (x₀ * x₀) ＝ x₀
  idem-triple-r = (refl ★ idem x₀) ∙ idem x₀

\end{code}

We now have, recorded as triple-fold-l,

  (a*b)*d ════════════ (p ★ q) ★ r ══════════════════════ (a*b)*d
     ║                                                       ║
(hab ★refl) ∙ hcd                                       (hab ★ refl) ∙ hcd
     ║                                                       ║
     e ══ ＝-congr hcd hcd (＝-congr hab hab (p ★ q) ★ r) ══ e

And we have that triple-fold-r does the same for the right-associated
parenthesization.

\begin{code}

  triple-fold-l : {a b c d e : A} (hab : a * b ＝ c) (hcd : c * d ＝ e)
                  (p : a ＝ a) (q : b ＝ b) (r : d ＝ d)
                → ＝-congr
                   ((hab ★ refl) ∙ hcd)
                   ((hab ★ refl) ∙ hcd)
                   ((p ★ q) ★ r)
                ＝ ＝-congr
                    hcd
                    hcd
                    (＝-congr hab hab (p ★ q) ★ r)
  triple-fold-l refl refl p q r = refl

  triple-fold-r : {a b c d e : A} (hab : a * b ＝ c) (hcd : d * c ＝ e)
                  (p : a ＝ a) (q : b ＝ b) (r : d ＝ d)
                → ＝-congr
                   ((refl ★ hab) ∙ hcd)
                   ((refl ★ hab) ∙ hcd)
                   (r ★ (p ★ q))
                ＝ ＝-congr
                    hcd
                    hcd
                    (r ★ ＝-congr hab hab (p ★ q))
  triple-fold-r refl refl p q r = refl

  loop-triple-l : (p q r : ΩA)
                → ＝-congr idem-triple-l idem-triple-l ((p ★ q) ★ r)
                ＝ (p ⋆ q) ⋆ r
  loop-triple-l p q r = triple-fold-l (idem x₀) (idem x₀) p q r

  loop-triple-r : (p q r : ΩA)
                → ＝-congr idem-triple-r idem-triple-r (p ★ (q ★ r))
                ＝ p ⋆ (q ⋆ r)
  loop-triple-r p q r = triple-fold-r (idem x₀) (idem x₀) q r p

  assoc-self : ΩA
  assoc-self = idem-triple-l ⁻¹ ∙ (assoc x₀ x₀ x₀ ∙ idem-triple-r)

  ⋆-assoc-raw : (p q r : ΩA)
              → ＝-congr assoc-self assoc-self ((p ⋆ q) ⋆ r)
              ＝ p ⋆ (q ⋆ r)
  ⋆-assoc-raw p q r =
   ＝-congr
    ((＝-congr-∙' (assoc x₀ x₀ x₀) idem-triple-r _ idem-triple-r _) ⁻¹
      ∙ (＝-congr-∙' _ (assoc x₀ x₀ x₀ ∙ idem-triple-r) _ _ _) ⁻¹)
    (loop-triple-r p q r)
    (ap (＝-congr idem-triple-r idem-triple-r)
      (ap (＝-congr (assoc x₀ x₀ x₀) _)
          ((＝-congr-⁻¹ {hax = idem-triple-l} {hby = idem-triple-l}
                       (loop-triple-l p q r)) ⁻¹)
        ∙ assoc-paths p q r))

  ⋆-refl : (p : ΩA) → p ⋆ refl ＝ act-l p
  ⋆-refl p =
   ⋆-in-terms-of-∙ p refl
   ∙ ap (act-l p ∙_) act-r-refl
   ∙ refl-right-neutral (act-l p)

\end{code}

We strip assoc-self using the commutativity of ΩA and the square
identity:

  assoc-self ∙ ⋆-assoc-raw  ＝  (p ⋆ q) ⋆ r ∙ assoc-self

(by ＝-congr-sq once we know loop-comm).

\begin{code}

  ⋆-assoc : (p q r : ΩA) → (p ⋆ q) ⋆ r ＝ p ⋆ (q ⋆ r)
  ⋆-assoc p q r =
   cancel-left (loop-comm assoc-self _ ∙ ＝-congr-sq _ assoc-self _ ⁻¹)
   ∙ ⋆-assoc-raw p q r

\end{code}

We now conclude that every loop is trivial.

act-l is idempotent:

  act-l (act-l p)
   ＝ act-l (p ⋆ refl)    (by ⋆-refl)
   ＝ p ⋆ (refl ⋆ refl)   (by ⋆-assoc)
   ＝ p ⋆ (act-l refl)    (by ⋆-refl)
   ＝ p ⋆ refl            (by act-l-refl)
   ＝ act-l p             (by ⋆-refl)

\begin{code}

  act-l-idem : (p : ΩA) → act-l (act-l p) ＝ act-l p
  act-l-idem p =
   ＝-congr
    (⋆-refl _ ∙ ap act-l (⋆-refl p))
    (ap (p ⋆_) (⋆-refl refl ∙ act-l-refl) ∙ ⋆-refl p)
    (⋆-assoc p refl refl)

\end{code}

act-l p ＝ refl.

  act-l p ∙ act-l p
   ＝ act-l (act-l p) ∙ act-l (act-l p)   (act-l-idem twice)
   ＝ act-l p                             (act-l-idemp)

So act-l p acts as a right-identity on itself, and we can left-cancel
to get refl.

\begin{code}

  act-l-trivial : (p : ΩA) → act-l p ＝ refl
  act-l-trivial p =
   cancel-left
    ((ap₂ _∙_
          ((act-l-idem p) ⁻¹)
          ((act-l-idem p) ⁻¹)
      ∙ act-l-idemp (act-l p))
      ∙ refl-right-neutral (act-l p))

\end{code}

Every loop is trivial:

  p  ＝  act-l p ∙ act-l p  ＝  refl ∙ refl  ＝  refl.

The first step is act-l-idemp backwards, and the second is
act-l-trivial. This shows that the type A is a set, as we wished to
know.

\begin{code}

  Ω-null : (p : x₀ ＝ x₀) → p ＝ refl
  Ω-null p =
   (act-l-idemp p) ⁻¹
   ∙ ap₂ _∙_ (act-l-trivial p) (act-l-trivial p)
   ∙ refl-left-neutral

\end{code}
