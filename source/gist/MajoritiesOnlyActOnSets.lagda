Jakub Opršal 11th Mar 2026.

In this note, I would like to explore the HoTT analogue of the following
theorem of Walter Taylor [1, Theorem 7.7].

THEOREM. (Taylor, 1977)
  A topological algebra with a ternary majority operation is homotopically
  weak-equivalent to a discrete set.

[1] Walter Taylor. Varieties obeying homotopy laws. Can. J. Math., XXIX(3):
    498–527, 1977. https://doi.org/10.4153/CJM-1977-054-9.

A majority is a ternary operation m that satisfies equations

  m(x, x, y) = m(x, y, x) = m(y, x, x) = x.

For types, we will rephrase this as Π types

  Π{x, y : A} m(x, x, y) = x
  Π{x, y : A} m(x, y, x) = x
  Π{x, y : A} m(y, x, x) = x

Hence the theorem proved in this file is stated as:

THEOREM.
  A type equiped with a ternary operation satisfying the majority identities
  is a set.

This is inspired by earlier result of David Wärn about semilattices, which is
an analogue of Taylor's Theorem 6.2.

Taylor studied varieties of topological algebras, and how the equations
influence homotopy of the corresponding spaces. The results about semilattices
and majorities only scratch the surface of what he proved, and I want to
explore which part of the rest generalises to types later.

Let me first start with sketching the classical proof of this statement. It
comes in two steps:

1. Prove that m acts on πᵢ(A, a₀) as a homomorphism.
2. Prove that if m commutes with a group operation, then the group satisfies
   x = y.

The first step is an exercise in category theory relying on the fact that πᵢ
preserves products and m is idempotent (and hence fixes a₀). The second step
can be argued equationally as follows:

1 = 1 * 1 = m(1, 1, x) * m(x, 1, 1) = m(x, 1, x) = x

We will use an analogous computation to show that if a majority acts on a
type, then the type is a set. The fact that this second step is an algebraic
(equational) argument makes it more amenable for type theory.

We will start where Martin left off with proving that there are no higher
semilattices:

\begin{code}
{-# OPTIONS --safe --without-K #-}
module gist.MajoritiesOnlyActOnSets where

open import gist.ThereAreNoHigherSemilattices
open import Agda.Primitive renaming (Set to Type)

ap₃ : {A B C D : Type} (f : A → B → C → D) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → c₁ ＝ c₂
    → f a₁ b₁ c₁ ＝ f a₂ b₂ c₂
ap₃ f refl refl refl = refl
\end{code}

We will work with a type M with a single ternary idempotent operation m,
satisfying the majority identities.

\begin{code}
module _
         (M    : Type)
         (m    : M → M → M → M)
         (eq₀  : (a b : M) → m b a a ＝ a)
         (eq₁  : (a b : M) → m a b a ＝ a)
         (eq₂  : (a b : M) → m a a b ＝ a)
         (m₀   : M)
       where
\end{code}


We start with the action of `m` on the paths.

\begin{code}
  m' : {x₀ x₁ x₂ y₀ y₁ y₂ : M}
     → x₀ ＝ y₀ → x₁ ＝ y₁ → x₂ ＝ y₂
     → m x₀ x₁ x₂ ＝ m y₀ y₁ y₂
  m' = ap₃ m

  ΩM : Type
  ΩM = m₀ ＝ m₀

  ΩM' : Type
  ΩM' = m m₀ m₀ m₀ ＝ m m₀ m₀ m₀
\end{code}

This action restricts to:

m' : ΩM' → ΩM' → ΩM' → ΩM.

Which is how we will mostly use it. We will need that this action is a group
homomorphism (from the third power of ΩM' to ΩM). In fact, the statement is
about the whole action of m', not just the restriction.

\begin{code}
  m'-is-homo : {x₀ x₁ x₂ y₀ y₁ y₂ z₀ z₁ z₂ : M}
            → (p₀ : x₀ ＝ y₀) →  (q₀ : y₀ ＝ z₀)
            → (p₁ : x₁ ＝ y₁) →  (q₁ : y₁ ＝ z₁)
            → (p₂ : x₂ ＝ y₂) →  (q₂ : y₂ ＝ z₂)
            → (m' p₀ p₁ p₂) ∙ (m' q₀ q₁ q₂) ＝ m' (p₀ ∙ q₀) (p₁ ∙ q₁) (p₂ ∙ q₂)
  m'-is-homo refl refl refl refl refl refl = refl
\end{code}

Now, the interesting part of the proof starts. The general strategy follows
step 2 of the algebraic proof outlined above:

refl  ＝ refl ∙ refl
      ＝ (m' p refl refl) ∙ (m' refl refl p)      -- lifts of eq₀ and eq₂
      ＝ m'(p ∙ refl) (refl ∙ refl) (refl ∙ p)    -- m'-is-homo
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
  triangle p = homomorphism ∙ simplify-arguments where
    homomorphism : (m' p refl refl) ∙ (m' refl refl p)
                   ＝ m'(p ∙ refl) (refl ∙ refl) (refl ∙ p)
    homomorphism = m'-is-homo p refl refl refl refl p
    simplify-arguments : m' (p ∙ refl) (refl ∙ refl) (refl ∙ p) ＝ m' p refl p
    simplify-arguments = ap₃ m' (∙refl p) refl (refl∙ p)
\end{code}

The next step is to show that the edges collapse to refl, p, and refl,
respectively. Nevertheless, this is not exactly true since m'(refl, refl, p) :
ΩM', but p : ΩM. In fact, what we can achieve (in a similar manner as for the
semilattice case) is only filling the following square.

  m m₀ m₀ m₀ ══ m' p refl p ══ m m₀ m₀ m₀
      ║                            ║
    idem₁                        idem₁
      ║                            ║
      m₀ ═══════════ p ═══════════ m₀

The sides of this square are proofs of idempotence of m. We have nevertheless
three different proofs of that fact, so we have to be careful about which one
to use here — it has to agree with the equation, i.e., idem₁ = eq₁ m₀ m₀.
The problem with this is that for the other two equations, we would get squares
with sides idem₀ = eq₀ m₀ m₀ and idem₂ = eq₂ m₀ m₀, respectively, and these do
not fit together!

Instead, we do a sleigh of hand, and show that m' p refl refl = refl, where the
refl on the right-hand side is of type m m₀ m₀ m₀ = m m₀ m₀ m₀! I will denote
it by reflₘ. Similarly, we show m' refl refl p = refl. This helps us avoid
problems with conjugation since conjugation fixes refl.

\begin{code}
  reflₘ : ΩM'
  reflₘ = refl

  side₀-is-refl : (p : ΩM) → (m' p refl₀ refl₀) ＝ reflₘ
  side₀-is-refl p = use-eq₀ ∙ (eq-congr-refl idem₀) where
    idem₀ : m₀ ＝ m m₀ m₀ m₀
    idem₀ = sym (eq₀ m₀ m₀)

    eq₀' : {a b c d : M}
            → (p : a ＝ b) → (q : c ＝ d)
            → (m' q p p) ＝ eq-congr (sym (eq₀ a c)) (sym (eq₀ b d)) p
    eq₀' {a} {_} {c} {_} refl refl = sym (eq-congr-refl (sym (eq₀ a c)))

    use-eq₀ : (m' p refl₀ refl₀) ＝ eq-congr idem₀ idem₀ refl₀
    use-eq₀ = eq₀' refl₀ p

  side₂-is-refl : (p : ΩM) → (m' refl₀ refl₀ p) ＝ reflₘ
  side₂-is-refl p = use-eq₂ ∙ (eq-congr-refl idem₂) where
    idem₂ : m₀ ＝ m m₀ m₀ m₀
    idem₂ = sym (eq₂ m₀ m₀)

    eq₂' : {a b c d : M}
            → (p : a ＝ b) → (q : c ＝ d)
            → (m' p p q) ＝ eq-congr (sym (eq₂ a c)) (sym (eq₂ b d)) p
    eq₂' {a} {_} {c} {_} refl refl = sym (eq-congr-refl (sym (eq₂ a c)))

    use-eq₂ : (m' refl₀ refl₀ p) ＝ eq-congr idem₂ idem₂ refl₀
    use-eq₂ = eq₂' refl₀ p
\end{code}

As of now, we have produced the following path, which takes us almost there.

\begin{code}
  almost-there : (p : ΩM) → reflₘ ＝ (m' p refl₀ p)
  almost-there p = x ∙ (triangle p) where
    x = ap₂ _∙_ (sym (side₀-is-refl p)) (sym (side₂-is-refl p))
\end{code}

The last majority identity is used to show that p and m' p refl p are
conjugated by idem₁, i.e., the square above.

\begin{code}
  idem₁ : m m₀ m₀ m₀ ＝ m₀
  idem₁ = eq₁ m₀ m₀

  side₁-is-p : (p : ΩM) → eq-congr idem₁ idem₁ (m' p refl₀ p) ＝ p
  side₁-is-p p = eq₁' p refl where
    eq₁' : {a b c d : M}
          → (p : a ＝ b) → (q : c ＝ d)
          → eq-congr (eq₁ a c) (eq₁ b d) (m' p q p) ＝ p
    eq₁' {a} {_} {c} {_} refl refl = eq-congr-refl (eq₁ a c)
\end{code}

Finally, The almost-there statement tells us that there is a homotopy between
the upper side of the square and refl. We can bring this homotopy down by
conjugating with idem₁. The result is our goal, p = refl.

\begin{code}
  M-is-set : (p : ΩM) → refl ＝ p
  M-is-set p = sym (eq-congr-refl idem₁)
              ∙ (ap (eq-congr idem₁ idem₁) (almost-there p))
              ∙ (side₁-is-p p)
\end{code}
