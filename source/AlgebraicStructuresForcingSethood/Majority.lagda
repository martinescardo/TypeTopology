Jakub Opršal, 11–12 Mar 2026.
Updated on 8 June 2026 by Tom de Jong to use minimal library imports.

In this note, I would like to explore the HoTT analogue of the following
theorem of Walter Taylor [1, Theorem 7.7].

THEOREM. (Taylor, 1977)
  A topological algebra with a ternary majority operation is homotopically
  weak-equivalent to a discrete set.

This is inspired by David Wärn's result about semilattices and its treatment
here [2, 3]; Wärn's theorem is an analogue of Taylor's Theorem 6.2.

[1] Walter Taylor. Varieties obeying homotopy laws. Can. J. Math., XXIX(3):
    498–527, 1977. https://doi.org/10.4153/CJM-1977-054-9.
[2] Martin Escardo. AlgebraicStructuresForcingSethood.Semilattice.lagda,
    23 February 2026.
[3] Tom de Jong. AlgebraicStructuresForcingSethood.Semilattice-streamlined.lagda,
    25—27 February 2026.

Taylor studied varieties of topological algebras, and how the equations
influence homotopy of the corresponding spaces. The results about semilattices
and majorities only scratch the surface of what he proved, and I want to
explore which part of the rest generalises to types later.

A majority is a ternary operation m that satisfies equations

  m(x, x, y) ＝ m(x, y, x) ＝ m(y, x, x) ＝ x.

A typical example is the lattice term:

  m(x, y, z) = (x ∧ y) ∨ (x ∧ z) ∨ (y ∧ z)

It might appear that this result about majority is therefore covered by the
result about semilattices, but in fact both are incomparable. There are algebras
that have a semilattice term, but no majority, and algebras that have a majority
but no semilattice. This file also serves as a proof-of-concept for providing a
common generalisation of both.

For types, we rephrase majority equations as witnessing Π types

  Π{x, y : A} m(x, x, y) ＝ x
  Π{x, y : A} m(x, y, x) ＝ x
  Π{x, y : A} m(y, x, x) ＝ x

In this file, I prove that if a type A is equipped with a ternary operation m
such that the above three types are inhabited, the type is a set.

Let me first start with sketching an outline of the proof of the analogous
statement for topological spaces with a majority operation. It consists of two
steps:

1. Prove that m acts on πᵢ(A, a₀) as a homomorphism.
2. Prove that if m commutes with a group operation, then the group satisfies
   x = y.

The first step is an exercise in category theory relying on the fact that πᵢ
preserves products and m is idempotent (and hence fixes a₀). The second step
can be argued equationally as follows:

  1 = 1 * 1 = m(1, 1, x) * m(x, 1, 1) = m(x, 1, x) = x

where 1 is the neutral element of the group. We will use an analogous
computation to show that if a majority acts on a type, then the type is a set.
The fact that this second step is an algebraic (equational) argument makes it
more amenable for type theory.

We will start with some very minimal imports.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module AlgebraicStructuresForcingSethood.Majority where

open import MLTT.Universes
open import MLTT.Id
open import UF.Base using
  ( ap₂
  ; ap₃
  ; refl-left-neutral
  ; ＝-congr
  ; ＝-congr-refl
  )

\end{code}

We will work with a type M with a single ternary idempotent operation m,
satisfying the majority identities.

\begin{code}

module type-with-majority
       (M   : 𝓤 ̇ )
       (m   : M → M → M → M)
       (eq₀ : (a b : M) → m b a a ＝ a)
       (eq₁ : (a b : M) → m a b a ＝ a)
       (eq₂ : (a b : M) → m a a b ＝ a)
       (m₀  : M)
       where

\end{code}

We start with the action of `m` on the paths.

\begin{code}

 m' : {x₀ x₁ x₂ y₀ y₁ y₂ : M}
    → x₀ ＝ y₀
    → x₁ ＝ y₁
    → x₂ ＝ y₂
    → m x₀ x₁ x₂ ＝ m y₀ y₁ y₂
 m' = ap₃ m

 ΩM : 𝓤 ̇
 ΩM = m₀ ＝ m₀

 ΩM' : 𝓤 ̇
 ΩM' = m m₀ m₀ m₀ ＝ m m₀ m₀ m₀

\end{code}

This action restricts to:

  m' : ΩM → ΩM → ΩM → ΩM'.

Which is how we will mostly use it. We will need that this action is a group
homomorphism (from the third power of ΩM to ΩM'). In fact, the statement is
about the whole action of m', not just the restriction.

\begin{code}

 m'-is-homo : {x₀ x₁ x₂ y₀ y₁ y₂ z₀ z₁ z₂ : M}
              (p₀ : x₀ ＝ y₀) (q₀ : y₀ ＝ z₀)
              (p₁ : x₁ ＝ y₁) (q₁ : y₁ ＝ z₁)
              (p₂ : x₂ ＝ y₂) (q₂ : y₂ ＝ z₂)
            → (m' p₀ p₁ p₂) ∙ (m' q₀ q₁ q₂) ＝ m' (p₀ ∙ q₀) (p₁ ∙ q₁) (p₂ ∙ q₂)
 m'-is-homo refl refl refl refl refl refl = refl

\end{code}

Now, the interesting part of the proof starts. The general strategy follows
step 2 of the algebraic proof outlined above:

refl ＝ refl ∙ refl
     ＝ (m' p refl refl) ∙ (m' refl refl p)      -- lifts of eq₀ and eq₂
     ＝ m'(p ∙ refl) (refl ∙ refl) (refl ∙ p)    -- m' is homomorphism
     ＝ m' p refl p                              -- evaluate arguments
     ＝ p                                        -- lift of eq₁

The goal would be better drawn as a triangle with sides refl, refl, and p as:

        m₀
       /  \
    refl  refl           (goal)
     /      \
    m₀ --p-- m₀

We prove this by applying majority on three commuting triangles:

        m₀                m₀                m₀
       /  \             /   \              /  \
      p   refl       refl   refl        refl   p
     /      \         /       \          /      \
    m₀ --p-- m₀      m₀ -refl- m₀       m₀ --p-- m₀

Which gives us a new triangle with all vertices m(m₀, m₀, m₀), and edges m'(p,
refl, refl), m'(p, refl, p), and m'(refl, refl, p). Subsequently, we use the
majority equations to reduce these sides to the required refl, refl, and p,
respectively. Although, it should be noted that this is a vast oversimplifica-
tion.

\begin{code}

 refl₀ : ΩM
 refl₀ = refl

 triangle : (p : ΩM)
          → (m' p refl₀ refl₀) ∙ (m' refl₀ refl₀ p) ＝ (m' p refl₀ p)
 triangle p = homomorphism ∙ simplify-arguments
  where
   homomorphism : (m' p refl refl) ∙ (m' refl refl p)
                ＝ m'(p ∙ refl) (refl ∙ refl) (refl ∙ p)
   homomorphism = m'-is-homo p refl refl refl refl p

   simplify-arguments : m' (p ∙ refl) (refl ∙ refl) (refl ∙ p) ＝ m' p refl p
   simplify-arguments = ap₃ m' refl refl refl-left-neutral

\end{code}

The next step is to show that the edges collapse to refl, p, and refl,
respectively. Nevertheless, this is not true since m'(refl, refl, p) : ΩM', but
p : ΩM. In fact, what we can achieve (in a similar manner as for the semilattice
case) is only filling the following square.

  m m₀ m₀ m₀ ══ m' p refl p ══ m m₀ m₀ m₀
      ║                            ║
    idem₁                        idem₁
      ║                            ║
      m₀ ═══════════ p ═══════════ m₀

The sides of this square are proofs of idempotence of m. We have nevertheless
three different proofs of that fact, so we have to be careful about which one
to use here — it has to agree with the equation, i.e., idem₁ = eq₁ m₀ m₀.

\begin{code}

 idem₁ : m m₀ m₀ m₀ ＝ m₀
 idem₁ = eq₁ m₀ m₀

 side₁-is-p : (p : ΩM) → ＝-congr idem₁ idem₁ (m' p refl₀ p) ＝ p
 side₁-is-p p = eq₁' p refl
  where
   eq₁' : {a b c d : M}
        → (p : a ＝ b)
        → (q : c ＝ d)
        → ＝-congr (eq₁ a c) (eq₁ b d) (m' p q p) ＝ p
   eq₁' {a} {_} {c} {_} refl refl = ＝-congr-refl (eq₁ a c)

\end{code}

We could repeat the same argument for the other two equations, but the problem
is that we would get squares with sides idem₀ = eq₀ m₀ m₀ and idem₂ = eq₂ m₀ m₀,
respectively, and these do not fit together. Originally, I thought that the only
way to resolve that is to assume that idem₀ ＝ idem₁ ＝ idem₂, i.e., that we need
some higher coherence. To my suprise, I realised, a few days after finishing the
proof with coherences, that they are not needed!

Instead, we do a sleigh of hand, and show that m' p refl refl ＝ refl, where the
refl on the right-hand side is refl of type m m₀ m₀ m₀ ＝ m m₀ m₀ m₀; I will
denote it by reflₘ. Similarly, we show m' refl refl p ＝ refl. This helps us
avoid problems with conjugation since conjugation fixes refl.

\begin{code}

 reflₘ : ΩM'
 reflₘ = refl

 side₀-is-refl : (p : ΩM) → (m' p refl₀ refl₀) ＝ reflₘ
 side₀-is-refl p = use-eq₀ ∙ (＝-congr-refl idem₀)
  where
   idem₀ : m₀ ＝ m m₀ m₀ m₀
   idem₀ = (eq₀ m₀ m₀) ⁻¹

   eq₀' : {a b c d : M}
        → (p : a ＝ b)
        → (q : c ＝ d)
        → (m' q p p) ＝ ＝-congr ((eq₀ a c) ⁻¹) ((eq₀ b d) ⁻¹) p
   eq₀' {a} {_} {c} {_} refl refl = (＝-congr-refl ((eq₀ a c) ⁻¹)) ⁻¹

   use-eq₀ : (m' p refl₀ refl₀) ＝ ＝-congr idem₀ idem₀ refl₀
   use-eq₀ = eq₀' refl₀ p

 side₂-is-refl : (p : ΩM) → (m' refl₀ refl₀ p) ＝ reflₘ
 side₂-is-refl p = use-eq₂ ∙ (＝-congr-refl idem₂)
  where
   idem₂ : m₀ ＝ m m₀ m₀ m₀
   idem₂ = (eq₂ m₀ m₀) ⁻¹

   eq₂' : {a b c d : M}
        → (p : a ＝ b)
        → (q : c ＝ d)
        → (m' p p q) ＝ ＝-congr ((eq₂ a c) ⁻¹) ((eq₂ b d) ⁻¹) p
   eq₂' {a} {_} {c} {_} refl refl = (＝-congr-refl ((eq₂ a c) ⁻¹)) ⁻¹

   use-eq₂ : (m' refl₀ refl₀ p) ＝ ＝-congr idem₂ idem₂ refl₀
   use-eq₂ = eq₂' refl₀ p

\end{code}

With these two equations and the triangle, we can derive the following identity,
which gets us almost there.

\begin{code}

 almost-there : (p : ΩM) → reflₘ ＝ (m' p refl₀ p)
 almost-there p =
  ap₂ _∙_ ((side₀-is-refl p) ⁻¹) ((side₂-is-refl p) ⁻¹)
  ∙ (triangle p)

\end{code}

Finally, the almost-there statement tells us that there is a homotopy between
the upper side of the square and refl. By conjugating this homotopy by idem₁,
we can transport it to the required refl₀ ＝ p.

\begin{code}

 M-is-set : (p : ΩM) → refl ＝ p
 M-is-set p = ((＝-congr-refl idem₁) ⁻¹) ∙ conjugate ∙ (side₁-is-p p)
  where
   conjugate : ＝-congr idem₁ idem₁ reflₘ ＝ ＝-congr idem₁ idem₁ (m' p refl₀ p)
   conjugate = (ap (＝-congr idem₁ idem₁) (almost-there p))

\end{code}
