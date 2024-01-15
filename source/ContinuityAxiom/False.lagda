Martin Escardo 27th Nov 2013, last updated 4th Dec 2013, ported to
this repository 2nd June 2023

In intensional Martin-Löf type theory, if all functions (ℕ → ℕ) → ℕ
are continuous, then 0 = 1

1. Introduction
2. Informal proof of the theorem
3. Formal proof in Agda notation
4. Discussion
   References

Introduction
------------

In Brouwer's intuitionistic mathematics, it can be proved that all
functions f : (ℕ → ℕ) → ℕ are continuous [5]. This means that the
value f(α) depends only on a finite prefix of the infinite sequence
α : ℕ → ℕ. Then, of course, Brouwer's mathematics is incompatible with
excluded middle, as excluded middle easily defines non-continuous
functions.

Intensional Martin-Löf type theory (MLTT) [2] is an alternative
foundation for constructive mathematics [5]. Like Bishop's
constructive mathematics [5], it is compatible with classical
mathematics. It doesn't prove or disprove excluded middle, which can
be consistently postulated, albeit with loss of computational content,
for the purposes of developing classical mathematics.

In the version of (intensional) MLTT considered here, we have identity
types Id X x y (written x = y and called propositional equality), some
basic types such as that of natural numbers (written ℕ) and that of
finite sequences of natural numbers of length n (written Vec ℕ n), and
dependent type constructors Π (written ∀) and Σ.  We have the
eliminator J for identity types, but not Streicher's eliminator K, and
we don't have the equality reflection rule. We don't have the axiom of
function extensionality (any two pointwise equal functions are equal).

A possible formulation of continuity in MLTT under the so-called BHK
(Brouwer-Heyting-Kolmogorov) interpretation Σ of the quantifier ∃ is

  ∀(α : ℕ → ℕ), Σ n : ℕ , ∀(β : ℕ → ℕ) , α =[n] β → f(α) = f(β),

where α =[n] β means that the sequences α and β agree at the first n
positions.

We show in MLTT that, with this formulation of continuity, if all
functions f : (ℕ → ℕ) → ℕ are continuous, then 0 = 1.

We write the proof both informally and formally in Agda notation [3].
See Bauer [1] for a related well-known phenomenon with the same proof
ingredients used here.

We emphasize that our proof doesn't use the axiom of function
extensionality (any two pointwise equal functions are equal), which
anyway is not available in MLTT (but is in Homotopy Type Theory
(HoTT)). It also doesn't require universes.

In HoTT [2], there is an alternative constructive existential
quantifier, written ∃, corresponding to the topos theoretic
existential quantifier, in which witnesses are hidden, but can be
disclosed via unique choice, formulated as the axiom of description by
Coquand [6].

Brouwer's continuity axiom with Σ replaced by ∃ is consistent with
MLTT, even when MLTT is extended with the axiom of function
extensionality. Hopefully it is compatible with the HoTT extensions of
MLTT too, but this is an open problem.


2. Informal proof of the theorem
--------------------------------

The proof in this section is the informal rendering of the formal
proof given in Section 3 below. It is based on a proof attributed to
van Dalen and Troelstra by Bauer [1] for a different theorem.

Write

  Baire = ℕ → ℕ

to denote the type of sequences, and let

  0^ω = the infinite sequence of zeros,

and

  0^n k^ω = the sequence of n many zeros followed by infinitely many k's.

Then

  (0^n k^ω) =[n] 0^ω     and    (0^n k^ω)(n) = k.

Assume that all functions are continuous, with the Σ-formulation of
continuity as in the introduction:

 ∀(f : Baire → ℕ). ∀(α : Baire). Σ(n : ℕ). ∀(β : Baire). α =[n] β → f(α) = f(β).

By projection, with α = 0^ω, this gives a modulus-of-continuity
function

 M : (Baire → ℕ) → ℕ

such that

 ∀ (f : Baire → ℕ) , ∀ (β : Baire) , 0^ω =[M f] β → f(0^ω) = f(β).    (0)

We use M to define a non-continuous function f : Baire → ℕ and hence
get a contradiction. What this really says is that no such function M
can be continuous. See the discussion in Section 4 below.  Notice also
that if we were using ∃ rather than Σ to define continuity, as
discussed in the introduction, we would need choice to get M.

Let

  m = M (λ α. 0),

and define f : Baire → ℕ by

  f β = M (λ α. β (α m)).

Observe that, by simply expanding the definitions, with the
understanding that 0^ω defined above is λ i. 0,

  f(0^ω) = m.

By the defining property (0) of M,

  ∀(β : Baire). 0^ω =[ M f ] β → m = f β.    (1)


Case 0. M f = 0.
------

By (1),

  ∀(β : Baire). m = f β.

The choice β i = i gives

  m = f(λ i. i) = M (λ α. α m).

By the defining property (0) of M, this means that

  ∀(α : Baire). 0^ω =[ m ] α → 0 = α m.

But this gives 0 = 1 if we choose e.g. the sequence α = 0^m 1^ω.


Case 1. M f > 0.
------

For any β : Baire, by the continuity of λ α. β (α m), by the definition
of f, and by the defining property (0) of M, we have that

  ∀(α : Baire). 0^ω =[ f β ] α → β 0 = β (α m).

Considering

  β = 0^(M f) 1^ω,

this gives

  ∀(α : Baire). 0^ω =[ m ] α → β 0 = β (α m),

because f β = m as 0^ω =[ M f ] β and f(0^ω) = m. Considering

  α = 0^m (M f)^ω,

this in turn gives 0 = β 0 = β (α m) = β (M f) = 1. Q.E.D.


3. Formal proof in Agda notation
--------------------------------

The main reason for giving a formal proof is to be certain that the
above argument doesn't use function extensionality (any two pointwise
equal functions are equal) inadvertently.

3.1. Standard preliminary definitions
-------------------------------------

The option without-K is used to disable the UIP (uniqueness of
identity proofs) principle, also known as Streicher's Axiom K, which
is not part of MLTT:

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ContinuityAxiom.False where

open import MLTT.Spartan
open import MLTT.Vector

Baire : 𝓤₀ ̇
Baire = ℕ → ℕ

_⟦_⟧ : {X : 𝓤 ̇} → (ℕ → X) → (n : ℕ) → Vector X n
α ⟦ 0      ⟧ = []
α ⟦ succ n ⟧ = α 0 ∷ ((λ i → α (succ i)) ⟦ n ⟧)

_＝⟦_⟧_ : {X : 𝓤₀ ̇} → (ℕ → X) → ℕ → (ℕ → X) → 𝓤₀ ̇
α ＝⟦ n ⟧ β = α ⟦ n ⟧ ＝ β ⟦ n ⟧

\end{code}

The above definitions are standard in type theory/constructive
mathematics. The second last one takes a finite prefix of a given
length of a given infinite sequence, and hence the last one defines
when two given sequences agree at the first n positions.


3.2 Formulation of the theorem
------------------------------

The following is Brouwer's definition of continuity, formulated with Σ
rather than ∃:

\begin{code}

continuous : (Baire → ℕ) → 𝓤₀ ̇
continuous f = (α : Baire) → Σ n ꞉ ℕ , ((β : Baire) → α ＝⟦ n ⟧ β → f α ＝ f β)

\end{code}

In Brouwer's mathematics, all functions are continuous, but this can't
be true if continuity is (incorrectly) formulated with Σ as above:

\begin{code}

theorem : ((f : Baire → ℕ) → continuous f) → 0 ＝ 1

\end{code}

We need some preparation to prove that.

3.3 Preliminary proofs and constructions
----------------------------------------

The following is standard in MLTT:

For future reference, notice that all uses of ap below are for
(first-order) functions of types

  ℕ → ℕ
  vec ℕ (succ n) → ℕ
  vec ℕ n → vec ℕ (succ n)

only.

The following definition of (n zeros-and-then k) gives a sequence of n
many zeros followed by k and then by something irrelevant (infinitely
many k's, in fact, but we don't need to know that):

\begin{code}

_zeros-and-then_ : ℕ → ℕ → Baire
( 0       zeros-and-then k)  i       = k
((succ n) zeros-and-then k)  0       = 0
((succ n) zeros-and-then k) (succ i) = (n zeros-and-then k) i

o : Baire
o = λ i → 0

zeros-and-then-spec₀ : (n k : ℕ) → (n zeros-and-then k) n ＝ k
zeros-and-then-spec₀  0       k = refl
zeros-and-then-spec₀ (succ n) k = zeros-and-then-spec₀ n k

zeros-and-then-spec₁ : (n k : ℕ) → o ＝⟦ n ⟧ (n zeros-and-then k)
zeros-and-then-spec₁ n k = zeros₀ n ∙ zeros₁ n k
 where
  zeros : (n : ℕ) → Vector ℕ n
  zeros  0       = []
  zeros (succ n) = 0 ∷ zeros n

  zeros₀ : (n : ℕ) → o ⟦ n ⟧ ＝ zeros n
  zeros₀  0       = refl
  zeros₀ (succ n) = ap (λ ns → 0 ∷ ns) (zeros₀ n)

  zeros₁ : (n k : ℕ) → zeros n ＝ (n zeros-and-then k) ⟦ n ⟧
  zeros₁  0       k = refl
  zeros₁ (succ n) k = ap (λ ns → 0 ∷ ns) (zeros₁ n k)

\end{code}


3.4 Proof of the theorem
------------------------

Finally, here is the proof of the claim. It uses the modulus of
continuity functional M such that M f is a modulus of continuity at
the constant zero sequence o (defined above), which exists because we
are using the existential quantifier Σ rather than ∃ in our
(unsatisfactory) definition of continuity, in order to define a
non-continuous function f and hence get a contradiction.

Recall that our goal is to prove

  theorem : ((f : Baire → ℕ) → continuous f) → 0 ＝ 1

formulated above in Agda.

\begin{code}

theorem continuity = γ
 where
  M : (Baire → ℕ) → ℕ
  M f = pr₁ (continuity f o)

  continuity₀ : (f : Baire → ℕ) (β : Baire) → o ＝⟦ M f ⟧ β → f o ＝ f β
  continuity₀ f = pr₂ (continuity f o)

  m : ℕ
  m = M (λ α → 0)

  f : Baire → ℕ
  f β = M (λ α → β (α m))

  observation : f o ＝ m
  observation = refl

  fact₀ : (β : Baire) → o ＝⟦ M f ⟧ β → m ＝ f β
  fact₀ = continuity₀ f

  lemma₀ : M f ＝ 0 → 0 ＝ 1
  lemma₀ r =
   0   ＝⟨ claim₄ α (zeros-and-then-spec₁ m 1) ⟩
   α m ＝⟨ α-fact₀ ⟩
   1   ∎
   where
    claim₀ : (β : Baire) → m ＝ f β
    claim₀ β = fact₀ β claim₁
      where
       claim₁ : o ＝⟦ M f ⟧ β
       claim₁ = transport (λ - → o ＝⟦ - ⟧ β) (r ⁻¹) refl

    claim₂ : m ＝ M (λ α → α m)
    claim₂ = claim₀ (λ i → i)

    claim₃ : (α : Baire) → o ＝⟦ M (λ α → α m) ⟧ α → 0 ＝ α m
    claim₃ = continuity₀ (λ α → α m)

    claim₄ : (α : Baire) → o ＝⟦ m ⟧ α → 0 ＝ α m
    claim₄ = transport (λ - → (α : Baire) → o ＝⟦ - ⟧ α → 0 ＝ α m) (claim₂ ⁻¹) claim₃

    α : Baire
    α = m zeros-and-then 1

    α-fact₀ : α m ＝ 1
    α-fact₀ = zeros-and-then-spec₀ m 1

  lemma₁ : (Σ n ꞉ ℕ , M f ＝ succ n) → 0 ＝ 1
  lemma₁ (n , r) =
    0   ＝⟨ claim (transport (λ - → o ＝⟦ - ⟧ β) r β-fact₁) ⟩
    β 0 ＝⟨ fact₄ ⟩
    1   ∎
   where
    β : Baire
    β = (M f) zeros-and-then 1

    β-fact₀ : β (M f) ＝ 1
    β-fact₀ = zeros-and-then-spec₀ (M f) 1

    β-fact₁ : o ＝⟦ M f ⟧ β
    β-fact₁ = zeros-and-then-spec₁ (M f) 1

    fact₀' : f β ＝ m
    fact₀' = (fact₀ β β-fact₁)⁻¹

    fact₁ : (α : Baire) → o ＝⟦ f β ⟧ α → β 0 ＝ β (α m)
    fact₁ α = continuity₀ (λ α → β (α m)) α

    fact₂ : (α : Baire) → o ＝⟦ m ⟧ α → β 0 ＝ β (α m)
    fact₂ = transport (λ n → (α : Baire) → o ＝⟦ n ⟧ α → β 0 ＝ β (α m)) fact₀' fact₁

    α : Baire
    α = m zeros-and-then (M f)

    α-fact₀ : α m ＝ M f
    α-fact₀ = zeros-and-then-spec₀ m (M f)

    α-fact₁ : o ＝⟦ m ⟧ α
    α-fact₁ = zeros-and-then-spec₁ m (M f)

    fact₃ : β 0 ＝ β (α m)
    fact₃ = fact₂ α α-fact₁

    fact₄ : β 0 ＝ 1
    fact₄ =
     β 0     ＝⟨ fact₃ ⟩
     β (α m) ＝⟨ ap β α-fact₀ ⟩
     β (M f) ＝⟨ β-fact₀ ⟩
     1       ∎

    claim : o ＝⟦ succ n ⟧ β → 0 ＝ β 0
    claim = ap head

  lemma : (Σ n ꞉ ℕ , M f ＝ n) → 0 ＝ 1
  lemma (0      , r) = lemma₀ r
  lemma (succ n , r) = lemma₁ (n , r)

  γ : 0 ＝ 1
  γ = lemma (M f , refl)

\end{code}

4. Discussion
-------------

For a large research community, the terminology "extensionality"
usually refers to the rule

    x ＝ y implies f x ＝ f y,

which here is called "ap" and defined above. This form of
extensionality is a feature of intensional type theory, and can be
regarded as a property of identity types.

A red herring in connection with Andrej Bauer's post [1] is that the
"extensionality" of M, that is, the availability of the function
ap _ _ M of type f ＝ g → M f ＝ M g, is not used in the above proof. We
only use the "extensionality" of first-order functions.  However, one
of these functions, namely β, is defined indirectly from M, and so its
"extensionality" relies on that of M, at least loosely speaking.

What is important is that we don't use the so-called axiom of function
extensionality (any two pointwise equal functions are equal), which is
not available in intensional type theory.

The fundamental reason for the contradiction is a topological
phenomenon: there can't be any continuous modulus-of-continuity
functional M. No finite part of a continuous function f : (ℕ → ℕ) → ℕ
is enough to tell which finite part of α : ℕ → ℕ is sufficient to
determine f(α).  In fact, what the above proof does is to use the
hypothetical M to construct a non-continuous function f.

In the topological topos all functions Baire → ℕ are continuous, both
externally and internally, but there is no continuous M.

The right notion of continuity, which is validated in some models, is

 ∀ (f : Baire → ℕ) , ∀(α : Baire) , ∥ Σ n : ℕ , ∀ (β : Baire), α ＝⟦ n ⟧ β → f α ＝ f β ∥,

where we use propositional truncation (or bracket types), which can
be written, using HoTT notation [2], as

 ∀ (f : Baire → ℕ) , ∀ (α : Baire) , ∃ n : ℕ) , ∀ (β : Baire) , α ＝⟦ n ⟧ β → f α ＝ f β.

This implies the weaker statement

 ∀ (f : Baire → ℕ) , ∀ (α : Baire) , ¬¬Σ n : ℕ , ∀ (β : Baire), α ＝⟦ n ⟧ β → f α ＝ f β,

which can be expressed without hpropositional truncation and hence in
MLTT. It is an interesting problem whether the ∃-formulation of
continuity can be formulated in pure MLTT (with or without universes).

Both the ∃-version and the ¬¬Σ version are validated in the
topological topos interpretation and hence are consistent.

Notice that a topos has both ∃ (via the subobject classifier) and Σ
(via its local cartesian closed structure). What the above says is
that continuity formulated with Σ is false in any topos, but
continuity formulated with ∃ holds in some toposes.

This is similar to the fact that the axiom of choice formulated with Σ
holds in any topos, but often fails when formulated with ∃.

Other continuity axioms that hold in Browerian mathematics do admit a
consistent Σ formulation in MLTT, such as uniform continuity

 ∀(f : Cantor → ℕ).Σ(n : ℕ).∀(α β : Cantor). α ＝⟦ n ⟧ β → f α ＝ f β,

where Cantor is the type of infinite binary sequences [4].


References
----------

[0] This file is available in two forms:
    http://www.cs.bham.ac.uk/~mhe/continuity-false/continuity-false.lagda
    http://www.cs.bham.ac.uk/~mhe/continuity-false/continuity-false.html

[1] Andrej Bauer.
    http://math.andrej.com/2011/07/27/definability-and-extensionality-of-the-modulus-of-continuity-functional/

[2] The HoTT Book. http://homotopytypetheory.org/book/

    Chapter 1 introduces intensional MLTT without its homotopical extensions.
    The appendix gives a formal treatment of MLTT with and without the extensions.

[3] The Agda Wiki. http://wiki.portal.chalmers.se/agda/pmwiki.php

[4] Chuangjie Xu and M.H. Escardó.
    A constructive model of uniform continuity.
    M. Hasegawa (Ed.): TLCA 2013, LNCS 7941, pp. 236-249. Springer, Heidelberg 2013.

[4'] M.H. Escardó and Chuangjie Xu.
    A constructive manifestation of the Kleene-Kreisel continuous functionals. Submitted.
    http://www.cs.bham.ac.uk/~mhe/papers/kleene-kreisel.pdf

[5] M. Beeson. Foundations of Constructive Mathematics:
    Metamathematical Studies, Springer, Berlin/Heidelberg/New York, 1985.

[6] T. Coquand. Type Theory and Univalent Foundation.
    Royal Society meeting, 26 Nov 2013.
    http://www.cse.chalmers.se/~coquand/rs.pdf
