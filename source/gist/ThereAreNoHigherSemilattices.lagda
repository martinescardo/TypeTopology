Martin Escardo 23rd Feb 2026. A result by David Wärn [1].

Any type equipped with a binary operation _*_ that is associative,
commutative and idempotent is a set (homotopy 0-type). That is, there
are no higher semilattices! This file is my attempt to understand
David's Agda file [1].

[1] David Wärn. https://dwarn.se/agda/Idem.html , 17 February 2026.
    (See also https://mathstodon.xyz/deck/@dwarn/116091515645003634)

I add some diagrams and some explanation, and rename some things,
which I hope are correct and what David intended.

Proof sketch (formalized in the anonymous module at the very end of
this file). Fix a type A and an x₀ : A, and write ΩA = (x₀ ＝ x₀). An
operation _*_ on A induces an operation _⋆_ on ΩA.  The main steps
are, for suitably defined act-l and act-r,

  (i)   p ⋆ p ＝ p                             (⋆-idemp)
  (ii)  p ⋆ q ＝ act-l p ∙ act-r q             (⋆-in-terms-of-∙)
  (iii) p ⋆ q ＝ q ⋆ p                         (comm-loop)
  (iv)  act-l p ＝ act-r p                     (only-one-act)
  (v)   act-l p ∙ act-l p ＝ p                 (⋆-idemp-lr)
  (vi)  act-l p ∙ act-l q ＝ act-l q ∙ act-l p (comm-lr)

An Eckmann–Hilton argument using (v) and (vi) gives:

  (vii) p ∙ q ＝ q ∙ p                         (loop-comm)

Finally, using the associativity of *:

  (viii) act-l (act-l p) ＝ act-l p            (act-l-idem)
  (ix)   act-l p ＝ refl                       (act-l-trivial)
  (x)    p ＝ refl                             (Ω-null)

In the spirit of the original file [1], we make this file
self-contained, without importing any TypeTopology file, to show that
a relatively short argument in a Spartan MLTT is possible. (We also
don't use universe polymorphism.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.ThereAreNoHigherSemilattices where

\end{code}

What Agda calls sets is what we call types.

\begin{code}

open import Agda.Primitive renaming (Set to Type)

\end{code}

Basic path combinators
──────────────────────

\begin{code}

infix 15 _＝_

data _＝_ {A : Type} (a : A) : A → Type where
 refl : a ＝ a

ap : {A B : Type} {a b : A} (f : A → B) → a ＝ b → f a ＝ f b
ap f refl = refl

infixr 20 _∙_

_∙_ : {A : Type} {a b c : A} → a ＝ b → b ＝ c → a ＝ c
refl ∙ refl = refl

sym : {A : Type} {a b : A} → a ＝ b → b ＝ a
sym refl = refl

ap₂ : {A B C : Type} (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → f a₁ b₁ ＝ f a₂ b₂
ap₂ f refl refl = refl

∙refl : {A : Type} {a b : A} (p : a ＝ b) → p ∙ refl ＝ p
∙refl refl = refl

refl∙ : {A : Type} {a b : A} (p : a ＝ b) → refl ∙ p ＝ p
refl∙ refl = refl

\end{code}

Equality (or path) congruence
─────────────────────────────

`eq-congr h₁ h₂ p` transports a path p : a ＝ b across a commutative
square to obtain a path x ＝ y:

    a ════ p ═════ b
    ║              ║
   h₁             h₂
    ║              ║
    x ════════════ y
           ?

The resulting path is sym h₁ ∙ p ∙ h₂.  Definitionally, when
h₁ = h₂ = refl, the square degenerates and we recover p.

\begin{code}

eq-congr : {A : Type} {a b x y : A} → a ＝ x → b ＝ y → a ＝ b → x ＝ y
eq-congr refl refl p = p

\end{code}

When h = refl the square collapses to a point and the loop is unchanged:

    a ══ p ══ a
    ║          ║
    h          h    ↝   a ══ refl ══ a
    ║          ║
    a ════════ a

\begin{code}

eq-congr-refl : {A : Type} {a x : A} (h : a ＝ x) → eq-congr h h refl ＝ refl
eq-congr-refl refl = refl

\end{code}

Equality Congruence distributes over path concatenation:

    a ══ p ══ b ══ q ═══ c
    ║         ║          ║
   h₁        h₂         h3
    ║         ║          ║
    x ═══════ y ════════ z

\begin{code}

eq-congr-∙ : {A : Type} {a b c x y z : A}
             {h₁ : a ＝ x} {h₂ : b ＝ y} {h3 : c ＝ z}
             (p : a ＝ b) (q : b ＝ c)
           → eq-congr h₁ h3 (p ∙ q) ＝ eq-congr h₁ h₂ p ∙ eq-congr h₂ h3 q
eq-congr-∙ {h₁ = refl} {h₂ = refl} {h3 = refl} p q = refl

\end{code}

Inverting an equality congruence
────────────────────────────────

\begin{code}

eq-congr-sym : {A : Type} {a b x y : A} {hax : a ＝ x} {hby : b ＝ y}
               {p : a ＝ b} {q : x ＝ y}
             → eq-congr hax hby p ＝ q
             → p ＝ eq-congr (sym hax) (sym hby) q
eq-congr-sym {hax = refl} {hby = refl} refl = refl

\end{code}

The square identity
───────────────────

Going right-then-down equals going down-then-right:

    a ══ p ══  b
    ║          ║
    q          r
    ║          ║
    x ════════ y

\begin{code}

eq-congr-sq : {A : Type} {a b x y : A} (p : a ＝ b) (q : a ＝ x) (r : b ＝ y)
            → q ∙ eq-congr q r p ＝ p ∙ r
eq-congr-sq refl refl refl = refl

\end{code}

Naturality of equality congruence
─────────────────────────────────

The cleanest expression is a commutative square whose nodes are
path spaces and whose edges are "apply congruence with":

  (a ＝ b) ══════ congruence with (ha, hb) ══════ (a ＝ b)
     ║                                              ║
congruence with (hax, hby)                  congruence with (hax, hby)
     ║                                              ║
  (x ＝ y) ════ congruence with (ha', hb') ══════ (x ＝ y)

  where  ha' = eq-congr hax hax ha
         hb' = eq-congr hby hby hb.

The geometric intuition is a cube in A, where the top and bottom faces
record the ha/hb loops and their conjugates ha'/hb', and the vertical
edges are hax and hby:

        a ══ ha ══ a
       ╱║           ║╲
    hax ║           ║  hax
     ╱  p           p'  ╲
    x   ║           ║    x
    ║   b ══ hb ══ b     ║
    ║  ╱           ╲     ║
    ║ hby          hby   ║
    ╲╱               ╲  ╱
     y ═════ hb' ═════ y

  where  p  = eq-congr hax hby p      (front face)
         p' = eq-congr hax hby        (back face)
              (eq-congr ha hb p).

Naturality says that the front face and back face of the cube give the
same path x ＝ y, that is, it doesn't matter whether we apply
congruence first by (ha, hb) and then by (hax, hby), or first to (hax, hby)
and then to the induced (ha', hb').

\begin{code}

eq-congr-nat : {A : Type} {a b x y : A}
               (ha : a ＝ a) (hb : b ＝ b) (hax : a ＝ x) (hby : b ＝ y)
               (p : a ＝ b)
              → eq-congr hax hby (eq-congr ha hb p)
              ＝ eq-congr
                  (eq-congr hax hax ha) (eq-congr hby hby hb)
                  (eq-congr hax hby p)
eq-congr-nat ha hb refl refl p = refl

\end{code}

Equality congruence by a composite path equals iterated congruence.

\begin{code}

congr-∙ : {A : Type} {a b u v x y : A}
          (l₁ : a ＝ u) (l₂ : u ＝ x) (r₁ : b ＝ v) (r₂ : v ＝ y) (p : a ＝ b)
        → eq-congr (l₁ ∙ l₂) (r₁ ∙ r₂) p ＝ eq-congr l₂ r₂ (eq-congr l₁ r₁ p)
congr-∙ refl refl refl refl p = refl

\end{code}

Left-cancellation of path concatenation.

\begin{code}

∙-cancel : {A : Type} {a b c : A} (p : a ＝ b) (q₁ q₂ : b ＝ c)
         → p ∙ q₁ ＝ p ∙ q₂ → q₁ ＝ q₂
∙-cancel refl q₁ q₂ h = eq-congr (refl∙ q₁) (refl∙ q₂) h

\end{code}

Eckmann–Hilton
──────────────

The standard Eckmann–Hilton argument shows that two binary operations
on a set that share a unit and interchange with each other must
coincide and be commutative. Here we only need one piece of that
argument: if loops p and q commute, then p ∙ p and q ∙ q also commute.

The key calculation rearranges a 2×2 grid of tiles:

  ┌──────┬──────┐     ┌──────┬──────┐
  │  p   │  p   │     │  q   │  q   │
  ├──────┼──────┤  ↝  ├──────┼──────┤
  │  q   │  q   │     │  p   │  p   │
  └──────┴──────┘     └──────┴──────┘

Concretely,

  p∙p∙q∙q = p∙(p∙q)∙q ＝ p∙(q∙p)∙q = (p∙q)∙(p∙q)
          ＝ (q∙p)∙(q∙p) = q∙(p∙q)∙p ＝ q∙(q∙p)∙p = q∙q∙p∙p.

The function assoc₄ handles the repeated reassociation steps.

\begin{code}

assoc₄ : {A : Type} {a b c d e : A}
         {p : a ＝ b} {q : b ＝ c} {r : c ＝ d} {s : d ＝ e}
       → (p ∙ q) ∙ (r ∙ s) ＝ p ∙ (q ∙ r) ∙ s
assoc₄ {p = refl} {q = refl} {r = refl} {s = refl} = refl

comm₂ : {A : Type} {a : A} {p q : a ＝ a} (h : p ∙ q ＝ q ∙ p)
      → (p ∙ p) ∙ (q ∙ q) ＝ (q ∙ q) ∙ (p ∙ p)
comm₂ {p = p} {q = q} h =
 eq-congr (sym assoc₄) (sym assoc₄)
  (eq-congr
    (ap (λ x → p ∙ x ∙ q) (sym h))
    (ap (λ x → q ∙ x ∙ p) h)
    (eq-congr assoc₄ assoc₄ (ap (λ x → x ∙ x) h)))

\end{code}

Main theorem
────────────

We fix a type A with an associative, commutative, idempotent operation,
and a base-point x₀.

\begin{code}

module _
         (A     : Type)
         (_*_   : A → A → A)
         (idem  : (a : A) → a * a ＝ a)
         (comm  : (a b : A) → a * b ＝ b * a)
         (assoc : (a b c : A) → (a * b) * c ＝ a * (b * c))
         (x₀   : A)
       where

  ΩA : Type
  ΩA = x₀ ＝ x₀

\end{code}

*-paths and _⋆_
───────────────

The operation * acts on paths componentwise:

    a₁ ══ p ══ a₂       b₁ ══ q ══ b₂

                                         ↝   a₁*b₁ ══ *-paths p q ══ a₂*b₂.

It also splits into a left part followed by a right part:

    a₁*b₁ ══ ap (-*b₁) p ══ a₂*b₁ ══ ap (a₂*-) q ══ a₂*b₂.

\begin{code}

  *-paths : {a₁ a₂ b₁ b₂ : A} → a₁ ＝ a₂ → b₁ ＝ b₂ → a₁ * b₁ ＝ a₂ * b₂
  *-paths = ap₂ _*_

  *-paths＝∙ : {a₁ a₂ b₁ b₂ : A} (p : a₁ ＝ a₂) (q : b₁ ＝ b₂)
             → *-paths p q ＝ ap (_* b₁) p ∙ ap (a₂ *_) q
  *-paths＝∙ refl refl = refl

\end{code}

The function `reduce` uses idempotence to turn a loop at x₀ * x₀ into
a loop at x₀:

        idem x₀                              idem x₀
   x₀ ════════ x₀*x₀                  x₀*x₀ ══════════ x₀
   ║               ║                    ↑               ↑
   ?       p       ?     (sym)          ║               ║  (sym)
   ║               ║                    ║               ║
   x₀ ════════ x₀*x₀                   x₀ ═══════════ x₀*x₀
        idem x₀                             idem x₀

\begin{code}

  reduce : x₀ * x₀ ＝ x₀ * x₀ → ΩA
  reduce = eq-congr (idem x₀) (idem x₀)

\end{code}

Given loops p, q : x₀ ＝ x₀, form the loop at x₀*x₀ via *-paths, then
reduce it:

    x₀*x₀ ═══ *-paths p q ═══ x₀*x₀
      ║                         ║
   idem x₀                    idem x₀
      ║                         ║
     x₀ ═══════════════════════ x₀
               p ⋆ q

It splits as act-l p ∙ act-r q:

    x₀*x₀ ═ ap(-*x₀) p ═ x₀*x₀ ═ ap(x₀*-) q ═══ x₀*x₀
      ║                    ║                      ║
    idem                 idem                   idem
      ║                    ║                      ║
     x₀ ═════ act-l p ════ x₀ ═════ act-r q ═════ x₀

\begin{code}

  _⋆_ : ΩA → ΩA → ΩA
  p ⋆ q = reduce (*-paths p q)

  act-l : ΩA → ΩA
  act-l p = reduce (ap (_* x₀) p)

  act-r : ΩA → ΩA
  act-r q = reduce (ap (x₀ *_) q)

  ⋆-in-terms-of-∙ : (p q : ΩA) → p ⋆ q ＝ act-l p ∙ act-r q
  ⋆-in-terms-of-∙ p q =
   ap reduce (*-paths＝∙ _ _)
   ∙ eq-congr-∙ (ap (_* x₀) p) (ap (x₀ *_) q)

\end{code}

Idempotence of _⋆_
──────────────────

When both arguments are equal, *-paths p p reduces to p via the
pointwise idempotence of *.  For any p : a ＝ b:

    a*a ══ *-paths p p ══ b*b
     ║                     ║
   idem a                idem b
     ║                     ║
     a ══════════ p ══════ b

\begin{code}#

  idem-paths : {a b : A} (p : a ＝ b)
             → eq-congr (idem a) (idem b) (*-paths p p) ＝ p
  idem-paths refl = eq-congr-refl (idem _)

  ⋆-idemp : (p : ΩA) → p ⋆ p ＝ p
  ⋆-idemp = idem-paths

\end{code}

Commutativity of _⋆_
────────────────────

We use the commutativity of * as a base-point-preserving loop
comm-self : x₀ ＝ x₀, and show that equality congruence by it swaps
_⋆_.

comm-loop-raw builds the following stacked rectangle:

    x₀*x₀ ═══ *-paths p q ════ x₀*x₀   (top, before reduce)
      ║                          ║
   comm x₀ x₀              comm x₀ x₀  (side paths via commutativity)
      ║                          ║
    x₀*x₀ ════ *-paths q p ═══ x₀*x₀   (comm-paths flips the args)
      ║                          ║
   idem x₀                  idem x₀
      ║                          ║
     x₀ ══════ q ⋆ p ═══════════ x₀

Stacking the rectangles gives:

  eq-congr comm-self comm-self (p ⋆ q) ＝ q ⋆ p.

The function comm-self-center then shows that comm-self is central
(equality congruence with it is the identity), by specializing to p = q
and using ⋆-idemp.

\begin{code}

  comm-paths : {a b x y : A} (p : a ＝ x) (q : b ＝ y)
             → eq-congr (comm a b) (comm x y) (*-paths p q) ＝ *-paths q p
  comm-paths refl refl = eq-congr-refl _

  comm-self : ΩA
  comm-self = reduce (comm x₀ x₀)

  comm-loop-raw : (p q : ΩA)
                → eq-congr comm-self comm-self (p ⋆ q) ＝ q ⋆ p
  comm-loop-raw p q =
    eq-congr
     (eq-congr-nat (comm x₀ x₀) (comm x₀ x₀) (idem x₀) (idem x₀) (*-paths p q))
     refl
     (ap reduce (comm-paths p q))

  comm-self-center : (p : ΩA) → eq-congr comm-self comm-self p ＝ p
  comm-self-center p =
   eq-congr
    (ap (eq-congr comm-self comm-self) (⋆-idemp p))
    (⋆-idemp p)
    (comm-loop-raw p p)

  comm-loop : (p q : ΩA) → p ⋆ q ＝ q ⋆ p
  comm-loop p q = eq-congr (comm-self-center _) refl (comm-loop-raw p q)

\end{code}

Swapping act-l and act-r; deducing act-l ＝ act-r
─────────────────────────────────────────────────

act-swap follows from comm-loop via the splitting ⋆-in-terms-of-∙:

  act-l p ∙ act-r q
    ＝ p ⋆ q              (by ⋆-in-terms-of-∙)
    ＝ q ⋆ p              (by comm-loop)
    ＝ act-l q ∙ act-r p

To deduce act-l ＝ act-r, specialize to q = refl:

  act-l p ∙ act-r refl ＝ act-l refl ∙ act-r p
      act-l p ∙ refl  ＝ refl ∙ act-r p
            act-l p  ＝ act-r p

\begin{code}

  act-swap : (p q : ΩA) → act-l p ∙ act-r q ＝ act-l q ∙ act-r p
  act-swap p q = eq-congr
                  (⋆-in-terms-of-∙ p q)
                  (⋆-in-terms-of-∙ q p)
                  (comm-loop p q)

  act-l-refl : act-l refl ＝ refl
  act-l-refl = eq-congr-refl _

  act-r-refl : act-r refl ＝ refl
  act-r-refl = eq-congr-refl _

  only-one-act : (p : ΩA) → act-l p ＝ act-r p
  only-one-act p = eq-congr
                    (ap (act-l p ∙_) act-r-refl ∙ ∙refl _)
                    (ap (_∙ act-r p) act-l-refl ∙ refl∙ _)
                    (act-swap p refl)

\end{code}

Eckmann–Hilton: loop concatenation is commutative
─────────────────────────────────────────────────

We now know

  (v)  act-l p ∙ act-l p ＝ p                  (using act-l ＝ act-r)
  (vi) act-l p ∙ act-l q ＝ act-l q ∙ act-l p  (comm-lr, using act-swap)

Then

  p ∙ q
   ＝ (act-l p ∙ act-l p) ∙ (act-l q ∙ act-l q) (by ⋆-idemp-lr twice)
   ＝ (act-l q ∙ act-l q) ∙ (act-l p ∙ act-l p) (by comm₂, using comm-lr)
   ＝ q ∙ p

\begin{code}

  ⋆-idemp-lr : (p : ΩA) → act-l p ∙ act-l p ＝ p
  ⋆-idemp-lr p =
   ap (act-l p ∙_) (only-one-act p)
   ∙ eq-congr (⋆-in-terms-of-∙ p p) refl (⋆-idemp p)

  comm-lr : (p q : ΩA) → act-l p ∙ act-l q ＝ act-l q ∙ act-l p
  comm-lr p q =
   eq-congr
    (ap (act-l p ∙_) (sym (only-one-act q)))
    (ap (act-l q ∙_) (sym (only-one-act p)))
    (act-swap p q)

  loop-comm : (p q : ΩA) → p ∙ q ＝ q ∙ p
  loop-comm p q =
   eq-congr
    (ap₂ _∙_ (⋆-idemp-lr p) (⋆-idemp-lr q))
    (ap₂ _∙_ (⋆-idemp-lr q) (⋆-idemp-lr p))
    (comm₂ (comm-lr p q))

\end{code}

Associativity of _⋆_
────────────────────

assoc-paths says that * acts functorially on 2×1 grids of paths:

    (a*b)*c ══ *-paths (*-paths p q) r ══ (x*y)*z
        ║                                     ║
   assoc a b c                           assoc x y z
        ║                                     ║
    a*(b*c) ══ *-paths p (*-paths q r) ══ x*(y*z)

We compare two reductions of the triple self-product x₀*x₀*x₀, one
for each parenthesization:

    (x₀*x₀)*x₀ ══ idem-triple-l ══ x₀
    x₀*(x₀*x₀) ══ idem-triple-r ══ x₀

The path assoc-self is the loop

    x₀         ═ (by sym idem-triple-l)
    (x₀*x₀)*x₀ ═ (by assoc)
    x₀*(x₀*x₀) ═ (by idem-triple-r)
    x₀

that witnesses the path between the two strategies.  Equality
congruence with assoc-self gives ⋆-assoc'.  Since ΩA is commutative
(loop-comm) and the equality congruence witness satisfies the square
identity (eq-congr-sq), we can use ∙-cancel to strip assoc-self and
obtain ⋆-assoc.

\begin{code}

  assoc-paths : {a b c x y z : A} (p : a ＝ x) (q : b ＝ y) (r : c ＝ z)
              → eq-congr (assoc a b c) (assoc x y z) (*-paths (*-paths p q) r)
              ＝ *-paths p (*-paths q r)
  assoc-paths refl refl refl = eq-congr-refl _

  idem-triple-l : (x₀ * x₀) * x₀ ＝ x₀
  idem-triple-l = *-paths (idem x₀) refl ∙ idem x₀

  idem-triple-r : x₀ * (x₀ * x₀) ＝ x₀
  idem-triple-r = *-paths refl (idem x₀) ∙ idem x₀

\end{code}

We now have, recorded as triple-fold-l,

  (a*b)*d ════════════ *-paths (*-paths p q) r ════════════════════════ (a*b)*d
     ║                                                                     ║
 *-paths hab refl ∙ hcd                                   *-paths hab refl ∙ hcd
     ║                                                                     ║
     e ══ eq-congr hcd hcd (*-paths (eq-congr hab hab (*-paths p q)) r) ══ e

And we have that triple-fold-r does the same for the right-associated
parenthesization.

\begin{code}

  triple-fold-l : {a b c d e : A} (hab : a * b ＝ c) (hcd : c * d ＝ e)
                  (p : a ＝ a) (q : b ＝ b) (r : d ＝ d)
                → eq-congr (*-paths hab refl ∙ hcd) (*-paths hab refl ∙ hcd)
                   (*-paths (*-paths p q) r)
                ＝ eq-congr hcd hcd (*-paths (eq-congr hab hab (*-paths p q)) r)
  triple-fold-l refl refl p q r = refl

  triple-fold-r : {a b c d e : A} (hab : a * b ＝ c) (hcd : d * c ＝ e)
                  (p : a ＝ a) (q : b ＝ b) (r : d ＝ d)
                → eq-congr (*-paths refl hab ∙ hcd) (*-paths refl hab ∙ hcd)
                   (*-paths r (*-paths p q))
                ＝ eq-congr hcd hcd (*-paths r (eq-congr hab hab (*-paths p q)))
  triple-fold-r refl refl p q r = refl

  loop-triple-l : (p q r : ΩA)
                → eq-congr idem-triple-l idem-triple-l (*-paths (*-paths p q) r)
                ＝ (p ⋆ q) ⋆ r
  loop-triple-l p q r = triple-fold-l (idem x₀) (idem x₀) p q r

  loop-triple-r : (p q r : ΩA)
                → eq-congr idem-triple-r idem-triple-r (*-paths p (*-paths q r))
                ＝ p ⋆ (q ⋆ r)
  loop-triple-r p q r = triple-fold-r (idem x₀) (idem x₀) q r p

  assoc-self : ΩA
  assoc-self = sym idem-triple-l ∙ (assoc x₀ x₀ x₀ ∙ idem-triple-r)

  ⋆-assoc' : (p q r : ΩA)
           → eq-congr assoc-self assoc-self ((p ⋆ q) ⋆ r)
           ＝ p ⋆ (q ⋆ r)
  ⋆-assoc' p q r =
   eq-congr
    (sym (congr-∙ (assoc x₀ x₀ x₀) idem-triple-r _ idem-triple-r _)
      ∙ sym (congr-∙ (sym idem-triple-l) _ _ _ _))
    (loop-triple-r p q r)
    (ap (eq-congr idem-triple-r idem-triple-r)
      (ap (eq-congr (assoc x₀ x₀ x₀) _)
          (sym (eq-congr-sym (loop-triple-l p q r)))
        ∙ assoc-paths p q r))

  ⋆-refl : (p : ΩA) → p ⋆ refl ＝ act-l p
  ⋆-refl p =
   ⋆-in-terms-of-∙ p refl
   ∙ ap (act-l p ∙_) act-r-refl
   ∙ ∙refl (act-l p)

\end{code}

We strip assoc-self using commutativity of ΩA and the square identity:

  assoc-self ∙ ⋆-assoc'  ＝  (p ⋆ q) ⋆ r ∙ assoc-self

(by eq-congr-sq once we know loop-comm).

\begin{code}

  ⋆-assoc : (p q r : ΩA) → (p ⋆ q) ⋆ r ＝ p ⋆ (q ⋆ r)
  ⋆-assoc p q r =
   ∙-cancel assoc-self _ _ (loop-comm _ _ ∙ sym (eq-congr-sq _ _ _))
   ∙ ⋆-assoc' p q r

\end{code}

Conclusion: every loop is trivial
─────────────────────────────────

Step 1 — act-l is idempotent:

  act-l (act-l p)
   ＝ act-l (p ⋆ refl)    (by ⋆-refl)
   ＝ p ⋆ (refl ⋆ refl)   (by ⋆-assoc)
   ＝ p ⋆ (act-l refl)    (by ⋆-refl)
   ＝ p ⋆ refl            (by act-l-refl)
   ＝ act-l p             (by ⋆-refl)

\begin{code}

  act-l-idem : (p : ΩA) → act-l (act-l p) ＝ act-l p
  act-l-idem p =
   eq-congr
    (⋆-refl _ ∙ ap act-l (⋆-refl p))
    (ap (p ⋆_) (⋆-refl refl ∙ act-l-refl) ∙ ⋆-refl p)
    (⋆-assoc p refl refl)

\end{code}

Step 2 — act-l p ＝ refl.

  act-l p ∙ act-l p
   ＝ act-l (act-l p) ∙ act-l (act-l p)   (act-l-idem twice)
   ＝ act-l p                             (⋆-idemp-lr)

so act-l p acts as a right-identity on itself; left-cancel to get refl.

\begin{code}

  act-l-trivial : (p : ΩA) → act-l p ＝ refl
  act-l-trivial p =
   ∙-cancel (act-l p) (act-l p) refl
    ((ap₂ _∙_ (sym (act-l-idem p)) (sym (act-l-idem p))
       ∙ ⋆-idemp-lr (act-l p))
       ∙ sym (∙refl (act-l p)))

\end{code}

Step 3 — every loop is trivial:

  p  ＝  act-l p ∙ act-l p  ＝  refl ∙ refl  ＝  refl.

(The first step is ⋆-idemp-lr backwards; the second is act-l-trivial.)
This shows A is a set.

\begin{code}

  Ω-null : (p : x₀ ＝ x₀) → p ＝ refl
  Ω-null p =
   sym (⋆-idemp-lr p)
   ∙ ap₂ _∙_ (act-l-trivial p) (act-l-trivial p)
   ∙ ∙refl refl

\end{code}
