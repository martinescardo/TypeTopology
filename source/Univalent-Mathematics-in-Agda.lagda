Martin Escardo, 4th March 2019.

----------------
Lecture notes on
-----------------------------
Univalent mathematics in Agda
-----------------------------

Keywords. Agda.
          Univalent mathematics.
          Univalent foundations.
          Univalent type theory.
          Univalence axiom.
          Homotopy type theory.
          ∞-Groupoid.
          Type.
          Intensional Martin-Löf type theory.
          Dependent type theory.
          Identity type.
          Cubical type theory.
          Cubical Agda.
          Proof assistants.

Course material originally developed for for MGS'2019
http://events.cs.bham.ac.uk/mgs2019/

------------------------
Incomplete working DRAFT
-----------------------

This is a draft and is expected to change considerably, by deletions
or additions or both. I am just experimenting with ideas at the
moment.

This is a so-called "literate" Agda file, with the formal mathematical
development within "code" environments, and the usual mathematical
discussion outside them. Most of this file is not Agda code.

Github pull requests to fix typos or make improvements are welcome.

------------
Introduction
------------

A univalent type theory is the underlying formal system for a
foundation for univalent mathematics as conceived by Voevodsky.

In the same way as there isn't just one set theory (we have e.g. ZFC
and NBG among others), there isn't just one univalent type theory (we
have e.g. the underlying type theory used in UniMath, HoTT-book type
theory, and cubical type theory, among others, and more are expected
to come in the foreseeable future before the foundations of univalent
mathematics stabilize).

The salient differences between univalent mathematics and traditional,
set-based mathematics are pehaps shocking at firt sight:

 1. The kinds of objects we take as basic.

    - Certain things called types, or higher-groupoids, rather than sets, are the primitive objects.
    - Sets, also called 0-groupoids, are particular kinds of types.
    - So we have more general objects as a starting point.
    - E.g. The type ℕ of natural numbers is a set, and this is a theorem, not a definition.
    - E.g. The type of monoids is not a set, but instead a 1-groupoid, automatically.
    - E.g. The type of categories is a 2-groupoid, again automatically.

 2. The treatment of logic.

    - Mathematical statements are interpreted as types rather than truth-values.
    - Truth-values are particular kinds of types, called -1-groupoids, with at most one element.
    - Logical operations are particular cases of mathematical operations on types.
    - Mathematics comes first, with logic as a derived concept.
    - E.g. when we say "and", we are taking the cartesian product of two types, which may be truth values.

 3. The treatment of equality.

    - The value of an equality x ≡ y is a type (called the identity type) which is not necessarily a truth value.
    - It collects the ways in which the mathematical objects x and y are identified.
    - E.g. it is a truth value for elements of ℕ, as there is at most one way for two natural numbers to be equal.
    - E.g. For the type of monoids, it is a set, amounting to the type of monoid isomorphisms, automatically.
    - E.g. For the type of categories, it is a 1-groupoid, amounting to the equivalences of categories,
      again automatically.

The important word in the above description of univalent foundations
is "automatic". For example, we don't *define* equality of monoids to
be isomorphism. Instead, collection of monoids as the type of types
that are sets, equipped with a binary multiplication operation and a
unit satisfying associativity of multiplication and neutrality of the
unit in the usual way, and then we *prove* that the native notion of
equality that comes with univalent type theory happens to coincide
with monoid isomorphism.

Voevodsky's way to achive this is to start with a Martin-Löf type
theory (MLTT), including identity types and type universes, and
postulate a single axiom, named "univalence". This axiom stipulates a
canonical bijection between type equivalences (in a suitable sense
defined by Voevodsky) and type identifications (in the original sense
of Martin-Löf's identity type). Voevodsky's notion of type
equivalence, formulated in MLTT, is a refinement of the notion of
isomorphism, which works uniformly for all higher groupoids,
i.e. types.

In particular, Voevodsky didn't design a new type theory, but instead
gave an axiom for an existing type theory (or any of a family of
possible type theories, to be more precise).

The main technical contributions in type theory by Voevodsky are

 (i)   The definition of type levels in MLTT, classifying them as n-groupoids including the possibility n=∞.
 (ii)  The (simple and elegant) definition of type equivalence that works uniformly for all type levels in MLTT.
 (iii) The formulation of the univalence axiom in MLTT.

Univalent mathematics begins with (i) and (ii) before we postulate
univalence. In fact, as the reader will see, we will do a fair amount
of univalent before we formulate or assume the univalence axiom.

All of (i)-(iii) rely on Martin-Löf's identity type. Initially,
Voevodsky thought that a new concept would be needed in the type
theory to achieve (i)-(iii) and hence (1) and (3). But he eventually
discovered that Martin-Löf's identity type is precisely what he
needed.

It is somewhat miraculous that the addition of the univalence axiom
alone to MLTT can achieve (1) and (3). Martin-Löf type theory was
designed to achieve (2), and, regarding (1), types were
imagined/conceived as sets (and even named "sets" in some of the
original expositions by Martin-Löf), and the identity type was
imagined/conceived as having at most one element, even if MLTT cannot
prove or disprove this statement, as was eventually shown by Hofmann &
Streicher with their groupoid model of types in the early 1990's.

Another important aspect of univalent mathematics is the presence of
explicit mechanisms for distinguishing

 (4) property (e.g. an unspecified thing exists) and

 (5) data (e.g. a designated thing exists),

which are common place in current mathematical practice
(e.g. cartesian closedness of a category is a property in some sense
(up to isomorphism), whereas monoidal closedness is necessarily data
or structure).

Lastly, univalent type theories don't assume the axiom of choice or
the principle of excluded middle, and so in some sense they are
constructive by default. But we emphasize that these two axioms are
constistent and hence can be safely used as assumptions, and we will
give examples of their use for the sake of illustration. However,
virtually all theorems of univalent mathematics, e.g. in UniMath, have
been proved without assuming them, with natural arguments.

In these notes we will explore the above ideas, using Agda to write
MLTT definitions, constructions, theorems and proofs, with univalence
as an assumption. We will have a further assumption, the existence of
certain propositional, or truth-value, truncations in order to be able
to deal with the distinction between property and data, and in
particular with the distinction between unspecified existence (for
example to be able to define the notions of image of a function and of
surjective function). However, we will not assume them globally, so
that the students can see clearly when univalence or truncation are or
are not needed. In fact, the foundational definitions, constructions,
theorems and proofs of univalent mathematics don't require univalence
or propositional truncation, and so can be developed in a version of
the original Martin-Löf type theories, and this is what happens in
these notes, and what Voevodsky did in his brilliant original
developmentin Coq. Our use of Agda, rather than Coq, is a personal
matter of taste only.

Univalent type theory is often called homotopy type theory for reasons
that we will not attempt to explain here. Terminologically speaking,
here we are following Voevodsky, who coined the terminologies
"univalent foundations" and "univalement mathematics".

--------------------
Homotopy type theory
--------------------

We regard the terminology "homotopy type theoy" as probably more
appropriate to the development of homotopy theory within univalent
mathematics, for which we refer the reader to the HoTT book.

However, "homotopy type theory" is also used as a synonym for
univalent type theory, not only because univalent type theory has a
model in homotopy types (as defined in homotopy theory), but also
because, without considering models, types do behave like homotopy
types, automatically. We will not discuss how to do homotopy theory
using univalent type theory in these notes. We refer the reader to the
HoTT book as a starting point.

----------
References
----------

We will unashamedly not provide enough references or attributions in
these notes, for which we refer the students to

   - https://homotopytypetheory.org/references/
   - https://homotopytypetheory.org/book/
   - https://ncatlab.org/nlab/show/homotopy+type+theory#References

It particular, it is recommended to read the concluding notes for each
chapter in the HoTT Book for discussion of original sources. Moreover,
the whole HoTT book is a recommended complementary reading for this
course.

And, after the reader has gained enough experience:

   - https://github.com/vladimirias/Foundations (in Coq)
   - https://github.com/UniMath/UniMath         (in Coq)
   - https://github.com/HoTT/HoTT               (in Coq)
   - https://github.com/HoTT/HoTT-Agda          (in Agda)

Regarding the computer language Agda, we recommend the following as
starting points:

   - https://wiki.portal.chalmers.se/agda/pmwiki.php
   - https://agda.readthedocs.io/en/latest/getting-started/index.html
   - https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation

We have based our presentation here
on the slides of our talk "logic in univalent type theory"
https://www.newton.ac.uk/seminar/20170711100011001


-------------
What is Agda?
-------------

There are two views:

 1. Agda is a dependently-typed functional programming language.

 2. Agda is a language for defining mathematical notions (e.g. group
    or topological space), formulating constructions to be performed
    (e.g. a type of real numbers, a group structure on the integers, a
    topology on the reals), formulating theorems (e.g. a certain
    construction is indeed a group structure, there are infinitely
    many primes), and proving theorems (e.g. with Euclid's argument).

This doesn't mean that Agda has two sets of features, one for (1) and
the other for (2). The same set of features account simultaneously for
(1) and (2). Programs are mathematical constructions that happen not
to use non-constructive principles such as excluded middle. In order
to illustrate that Agda or its underlying type theory are not
restricted to be constructive, we will formulate and prove theorems
that use both excluded middle and univalent choice (which implies
excluded middle).

In these notes we study a minimal univalent type theory and do
mathematics with it using the computer language Agda as a vehicle.

We emphasize strongly that univalent mathematics can be done in a
blackboard with natural language and pictures, just as traditional
mathematics (see the HoTT Book) and we don't need computers to even
exist for univalent mathematics to make sense and be an interesting
and beatiful foundation of mathematics.  But the purpose of these
notes is to see how we can do univalent mathematics formally with a
computer, and we choose Agda to do that.

Agda is a so-called "proof assistant". I don't agree with this
terminology. "Computer referee" would be a much better
terminology. While mathematical referees can occasionally assist the
author of a paper submitted for publication, most of the time they
work as opponents or devil advocates, as they should, telling the
author what is wrong, what may be wrong, or that some things don't
make sense or seem to make sense. Agda is a perfect referee in this
sense, inflicting maximum pain to the author. But when Agda is happy,
there should be no mathematical errors. Unless, of course, Agda itself
has a bug. And it does have bugs occasionally. This is no different
from a referee who misses an existing mistake or gap, or thinks there
is a gap when there is none, both of which are often the case. People
who implement Agda are only human, like the mathematical
referees. This only means that we still need to know what we are
doing, just as with pencil and paper mathematics. There is no such
thing as guaranteed mathematical correctness in publications or in
computer checked files such as this one. Mathematics is, as has been
claimed many times, a social process. Here we explore what the
computer can add to that, but our emphasis is on the mathematics and
not on the computer.

--------------------------
Our Martin-Löf type theory
--------------------------

Before embarking into a full definition of our Martin-Löf type
theory in Agda, we summarize the particular, spartan, Martin-Löf type
theory that we will consider, by naming the concepts that we will
include. We will have:

   * Universes (types of types), ranged over by 𝓤,𝓥,𝓦,𝓣,
   * An empty type 𝟘.
   * A one-element type 𝟙.
   * A type of ℕ natural numbers.
   * Type formers + (binary sum), Π (product), Σ (sum), Id (identity type).

And nothing else.


spartan
  /ˈspɑːt(ə)n/
  adjective:

      showing or characterized by austerity or a lack of comfort or
      luxury.


We will also be rather spartan with the subset of Agda that we choose
to discuss. Many things we do here can be written in more concise ways
using more advanced features. The readers can consult the Agda manual
if they wish, but this is not necessary.  Here we introduce a minimal
subset of Agda where everything in our minimal MLTT can be expressed.

-----------------------------------
Our axiomatic univalent type theory
-----------------------------------

    * Spartan MLTT as above.
    * Univalence axiom.
    * Existence of truth-value, or propositional, truncations axiom.

But, as discussed above, rather than postulating these axioms we will
use them as explicit assumptions each time they are needed.

We emphasize that there are univalent type theories in which the
univalence and propositional truncation axioms are theorems, for
example cubical type theory, which has a version available in Agda,
called cubical Agda. We will not discuss this here, but we emphasize
that cubical type theory is a rather important development in the
subject.

With such a spartan univalent type theory it is possible to do
e.g. analysis, group theory, topology, category theory, as testified
by UniMath.

---------------------------
Design plan for these notes
---------------------------

This plan may not reflect what we actually get when we complete the
lecture notes.

We will do the following, not necessarily in the given order.

    * Fully introduce our type theory in Agda.
    * Define type levels, and in particular, the notions of proposition and set.
    * Notion of retraction.
    * Define the notion of equivalence. Prove that invertibles maps are equivalences.
    * Formulate the univalence axiom.
    * Define the types of monoids and topological spaces.
    * Apply it to characterize equality of monoids as monoid isomorphism,
      and equality of topological spaces as homeomorphism (no, this would be too much, we shoulf only discuss it instead..
    * Formulate and prove a structure of identity principle.
    * Prove that univalence implies function extensionality.
    * Various things are subsingletons under funext.
    * Formulate propositional truncation, and define ∃ and image and surjection.

Maybe this is too much for just one week. I will write the full Agda
development from scratch here so that I can have a better idea of how
much this amount to.

---------
Exercises
---------

Search for the words "exercise" and "Exercise" (or simply
"xercise"). Some exercises rely, deliberately, on material that will
come later. This is to challenge the students and and maybe tempt them
to read ahead of time. Some exercises are mathematically trivial, and
are just for the purposes of practicing / developing Agda skills.

-----
CHAOS
-----

Raw material to try to build an exposition.

We don't use any Agda library. For pedagogical purposes, we start from
scratch.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Univalent-Mathematics-in-Agda where

\end{code}

 * The option --without-K disables Streicher's K axiom, which we don't
   want for univalent mathematics.

 * The option --exact-split makes Agda to only accept definitions with
   equality that behave like so-called judgmental equalities.

 * The option --safe disables features that may make Agda inconsistent
   (such as --type-in-type, postulates and more)

-----------
Universes I
-----------

A universe 𝓤 is a type of types. One use of universes is to define
families of types indexed by a type X as functions X → 𝓤. Such a
function is sometimes seen as a property of elements of X, under the
Curry-Howard interpretation of mathematical statements and logic,
which is discussed later.  An other use of universes, as we shall see,
is to define types of mathematical structures, such as groups,
topological spaces, categories etc.

Sometimes we need more than one universe. For example, the type of
groups in a universe lives in a bigger universe, and given a category
in one universe, its presheaf category also lives in the next
universe.

We will work with a tower of type universes

  𝓤₀, 𝓤₁ , 𝓤₂, 𝓤₃, ...

These are actually universe names. We reference the universes
themselves by a deliberately almost-invisible superscript dot. For
example, we will have

 𝟙 : 𝓤₀ ̇

where 𝟙 is the one-point type to be defined shortly. We have that the
universe 𝓤₀ is a type in the universe 𝓤₁, which is a type in the
universe 𝓤₂ and so one. The assumption that 𝓤₀ : 𝓤₀ or that any
universe is in itself or a smaller universe gives rise to a
contradiction, similar to Russell's Paradox.

 𝓤₀ ̇ : 𝓤₁ ̇
 𝓤₁ ̇ : 𝓤₂ ̇
 𝓤₂ ̇ : 𝓤₃ ̇

We now bring our notation for universes by importing the following
file. "open" means that we make the definitions visible here.

\begin{code}

open import Univalent-Mathematics-in-Agda-Universes

\end{code}

We will refer to the above universes by letters 𝓤,𝓥,𝓦,𝓣 when we don't
care at which level we want to work:

\begin{code}

variable
 𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe
\end{code}

----------------------
The one-element type 𝟙
----------------------

We place it in the first universe, and we name it unique element "*":

\begin{code}

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

\end{code}

It is important that the point "*" belongs to the type 𝟙 and no other
type. There isn't dual citizenship in our type theory. When we create
a type, we also create freshly new elements for it, in this case "*".

Next we want to give a mechanism to prove that all its elements satify
a given property A.

  * The property is a function A : 𝟙 → 𝓤 ̇ for some universe, e.g. the first one 𝓤₀.

  * The value A(x), which we will write simply write A x, doesn't need
    to be a truth value (defined below).  It can be any type. We will
    meet examples shortly.

  * Mathematical statements, for example, the one named 𝟙-induction below, are types.
    In this example, the type would be written in MLTT as

      Π (A : 𝟙 → 𝓤), A * → Π (x : 𝟙), A x.

    We read this in natural language as "for any given property A of
    elements of the type 𝟙, if we can show that A * holds, then it
    follows that A x holds for all x : 𝟙". Which happens to be true.

    In Agda these Π-types are written as

     (A : 𝟙 → 𝓤 ̇ ) → A * → (x : 𝟙) → A x.

   This is the type of functions with three arguments A : 𝟙 → 𝓤 ̇
   and a : A * and x : 𝟙, and value in the type A x.

  * A proof of a mathematical statement rendered as a type is a
    construction of an element of the type.  In our example, we have
    to construct a function. We do this as follows:

\begin{code}


𝟙-induction : (A : 𝟙 → 𝓤 ̇ )
            → A ⋆
            → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

\end{code}

Notice that we supply A and a as arbitrary arguments, but instead of
an arbitrary x we written "*". Agda accepts this because it knows from
the definition of 𝟙 that "*" is the only element of 𝟙. This is called
"pattern matching.

A particular case occurs of 𝟙-induction when the family is constant
with value B, which can be written as variously as A = λ (x : 𝟙) → B,
or A = λ x → B if we want Agda to figure out the type of x by itself,
or A = λ _ → B if we don't want to name the argument of A because it
is not used. In mathematics such a lambda expression is usually
written "x ↦ B" (x is mapped to B).

Given a type B and a point b : B, we construct the function 𝟙 → B
that maps any x : 𝟙 to b.

\begin{code}

𝟙-induction' : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-induction' B b x = 𝟙-induction (λ _ → B) b x

\end{code}

Not all types have to be seen as mathematical statements (for example
the type ℕ of natural numbers defined below). But the above definition
has a dual interpretation as a mathematical function, and as the
statement "B implies (true implies B)" where 𝟙 is the type encoding
the truth value "true".

We will not use this induction principle directly, as we can
prove properties of 𝟙 by pattern matching on *, just as we defined the
induction principle.

The unique function to 𝟙 will be named "!𝟙". We define two versions to
illustrate "implicit arguments" which correspond in mathematics to
"subscripts that are omitted when the read can safely infer them", as
for example for the identity arrow of an object in a category.


\begin{code}

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

\end{code}

This means that when we write "!1 x" we have to recover the (uniquely)
missing X with x:X "from the context". When Agda can't figure it out,
we need to supply it and write "!1 {𝓤} {X} x". This is because 𝓤 is
also an implicit argument (all "variables" as in the above example are
implicit arguments). There are other, non-positional, ways to indicate
X without having to indicate 𝓤 too - see the Agda manual.

Occasionally, people define variants of a function with different
choices of "implicitness", as above.

--------------
The empty type
-------------

It is defined like 𝟙, except that no elements are listed for it:

\begin{code}

data 𝟘 : 𝓤₀ ̇  where

\end{code}

That's the complete definition. This has a dual interpretation as the
empty set (we will actually prove that this type is a set, once we
know the definition of set) and the truth-value "false".

\begin{code}

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction A ()

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 A a = 𝟘-induction (λ _ → A) a

\end{code}

The expression "()" corresponds the mathematical expression "vacuously true".
https://en.wikipedia.org/wiki/Vacuous_truth

When we write the "pattern" (), Agda checks if there is any case we
missed. If there is none, our definition is accepted.

We give two names to the same function now:

\begin{code}

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = (X → 𝟘)

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = (X → 𝟘)

\end{code}

This says that a type is empty precisely when we have a function to
the empty type. Assuming univalence, once we have defined equality
"≡", we will be able to prove that "is-empty X ≡ (X ≡ 𝟘)". We will
also be able to prove things like "(2 + 2 ≡ 5) ≡ 𝟘"
and "(2 + 2 ≡ 4) ≡ 𝟙".

When we view 𝟘 as representing "false", we can read the definition of
the "negation" ¬ X as saying that "X implies false". With univalence
we will be able to show that "(false → false) ≡ true", which amounts
to "(𝟘 → 𝟘) ≡ 𝟙", which says that there is precisely one function
𝟘 → 𝟘, namely the (vacuous) identity function.

---------------
Natural numbers
---------------

The definition is similar but not quite the same as that via Peano Axioms.
https://en.wikipedia.org/wiki/Peano_axioms

We stipulate an element zero : ℕ and a successor function ℕ → ℕ, and
then define induction. Once we have defined equality "≡", we will
*prove* the other peano axioms.

\begin{code}

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ

ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A zero
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a f = h
 where
  h : (n : ℕ) → A n
  h zero     = a
  h (succ n) = f n (h n)

\end{code}

Notice that the proof of induction is by primitive recursion. So the
principle of induction is a construction that given the base case "a"
and the induction step "f" and a number n says how to get an element
of the type A n.

Notice also that ℕ-induction is the dependently typed version of
primitive recursion:

\begin{code}

ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration A a f = ℕ-recursion A a (λ n a → f a)

\end{code}

Agda checks that any recursive definition as above is well founded,
with recursive invokations with structurally smaller arguments
only. If it isn't, the definition is not accepted.

In official Martin-Löf type theories, we have to use the ℕ-induction
function to define everything else with the natural numbers. But Agda
allows us to define functions by structural recursion, like we defined
ℕ-induction. Let's do addition and multiplication for the sake of
illustration.

First in Peano style. We will create a local "module" so that the
definitions are not globally visible, as we want to have the symbols
"+" and "×" free for type operations of MLTT to be define soon. The
things in the module are indented and are visible outside the module
only if we "open" the module or if we write them as
e.g. Arithmetic-I.+ in the following example.

\begin{code}

module Arithmetic where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + zero   = x
  x + succ y = succ (x + y)

  x × zero   = zero
  x × succ y = x + x × y

  infixl 0 _+_
  infixl 1 _×_

\end{code}

Equivalent definitions using ℕ-induction on the second argument y, via
ℕ-iteration:

\begin{code}

module Arithmetic' where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ


  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ zero (x +_)

  infixl 0 _+_
  infixl 1 _×_

\end{code}

Here x +_ is the function ℕ → ℕ that adds x to its argument. So to
multiply x by y, we apply y times the function x +_ to zero.

As another example, we define the less-than-or-equal relation by
nested induction, on the first argument and then the second, but we
use patern matching for the sake of readability (exercise: write it
using ℕ-induction, recursion or iteration, as appropriate).

\begin{code}

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  zero   ≤ y      = 𝟙
  succ x ≤ zero   = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

\end{code}

Exercise.

  After you have learned Σ and _≡_ explained below, prove that

    x ≤ y if and only if Σ \(z : ℕ) → x + z ≡ y,

  so that we can use this as a perhaps more natural definition.


If we want to be able to write 5 rather than

 (succ (succ (succ (succ (succ zero)))))

or 1000 rather than something we will not write due to limitations on
space imposed by the editorial board#, we can use the "directive":

\begin{code}

{-# BUILTIN NATURAL ℕ #-}

\end{code}

If we are doing applied mathematics and want to actually compute, we
can define a type for binary notation, and of course people have done
that. Here are not concerned with efficiency but only with
understanding how we encode mathematics in type theory.

-------
Σ-types
-------

Given a type X in a universe 𝓤 and a family Y : X → 𝓥 of types in a
universe 𝓥 indexed by X, we want to construct its sum, which is a type
whose elements are of the form (x , y) with x : X and y : Y x. This
sum type will live in the least upper bound of the universes 𝓤 and 𝓥,
written 𝓤 ⊔ 𝓥. For example, if 𝓤 is 𝓤₀ abd 𝓥 is 𝓤₁, then 𝓤 ⊔ 𝓥 is 𝓤₁.

We will write this sum

  Σ Y

with X, as well as the universes, implicit. Often Agda (and people)
can figure out what the unwritten X is, from the definition of Y. But
sometimes there may be either lack of enough information, or of
enough concentration power by people, or sufficiently power inference
algorithms in the implementation of Agda. In such cases we can write

  Σ λ(x : X) → Y x

because Y = λ (x : X) → Y x by a so-called η-rule. However, we will
often use the synonym "\" of "λ" for Σ, as if considering it as part
of the Σ syntax.

  Σ \(x : X) → Y x

In MLTT we would write Σ (x : X), Y x or

  Σ   Y(x)
 x:X

Or it may be that the name Y is not defined, and we work with a
nameless family defined on the fly, as in the exercise proposed above:

  Σ \(z : ℕ) → x + z ≡ y

where Y z = (x + z ≡ y) in this case, and where we haven't defined "≡"
yet.

\begin{code}

record Σ {𝓤 𝓥} {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor _,_
  field
   x : X
   y : Y x

\end{code}

This says we are defining a binary operator "," to construct the
elements of this type as "x , y". The brackets are not needed, but we
will often write them to get the more familir "(x , y)". The
definition says that an element of Σ Y has two fields, giving the
types for them.

NB. Beginners may safely ignore this remark: Normally people will call
these two fields something like pr₁ and pr₂ for projections (or fst
and snd for first and second projection), and then do "open Σ public"
and have the projections avaiable automatically. But we will
deliberately not do that, and instead define the projections
ourselves, because this is confusing for beginners, no matter how
mathematically or computationally versed they may be, in particular
because it will not be immediately clear that the projections have the
following types (with the family made implicit by Agda, and by
ourselves here).

We project out of Σ Y as follows:

\begin{code}

pr₁ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

\end{code}

How do we prove that A z holds for all z : Σ Y, for a given property A?

We just prove that we have A (x , y) for all given x : X and for all y : Y x.

This is called Σ-induction or Σ elimination or uncurry.

\begin{code}

uncurry : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇}
        → ((x : X) (y : Y x) → A (x , y))
        → (z : Σ Y) → A z
uncurry g (x , y) = g x y

\end{code}

This function has an inverse:

\begin{code}

curry : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇}
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

\end{code}

https://en.wikipedia.org/wiki/Haskell_Curry

An important particular case of the sum type is the binary cartesian
product, when the type family doesn't depend on the indexing family:

\begin{code}

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y

\end{code}

We have seen that the function type symbol "→" represents logical
implication, and that a dependent function type (x : X) → A x
represents a universal quantification.

We have the following uses of Σ.

  * The binary cartesian product represents conjunction "and". If the
    types A and B are mathematical statements, then the mathematical
    statement "A and B" is encoded as A × B. This is because to prove
    "A and B" we have to provide a pair (a , b) of proofs a:A and b:B.

    So notice that proofs are mathematical objects, rather than
    meta-mathematical ones like in set theory.

  * The more general Σ \(x : X), A x, if X encodes a mathematical
    object and A encodes a mathematical statement, represents
    *designated* existence "there is a designated x:X with A x".  To
    prove this, one has to provide a designated x:X and a proof a : A x
    that holds in a pair (x , a)".

  * Later we will discuss *unspecified* existence ∃ \(x : X) → A x,
    which will be obtained by a sort of quotienting of Σ \(x : X), A x,
    written ∥ Σ \(x : X), A x ∥ that identifies all the elements of
    the type Σ \(x : X), A x in a single equivalence class, called
    propositional truncation or subsingleton truncation.

  * Another reading of Σ \(x : X), A x is as "the type of x : X with A x",
    similar to { x ∈ X | A x } in set theory. But have to be
    careful because if there is more than one element in A x, then x
    is put more than once in this type. In such situations, if we
    don't want that, we have to be careful so ensure that either the
    type A x has at most one element for every, or instead consider
    the type ∥ A x ∥.

-------
Π-types
-------

Π-types are builtin with a different notation in Agda, as discussed
above, but we introduce the notation Π for them, similar to that for Σ:

\begin{code}

Π : {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

\end{code}

Notice that the function type X → Y is the particular case of the Π
type when the family is constant, or doesn't depend on X.

We take the opportunity to define the identity function and function
composition:

\begin{code}

id : {X : 𝓤 ̇} → X → X
id x = x

\end{code}

Usually the type of function composition _∘_ is simply

 (Y → Z) → (X → Y) → (X → Z).

With dependent functions, we can be give it a more general type:

\begin{code}

_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

\end{code}

Notice that this type of composition can be read as mathematical
statement: If Z y holds for all y, then for any given f : X → Y we
have that Z (f x) holds for all x : X. And the non-dependent one is
just the transitivity of implication.


The following functions are sometimes useful when we are using
implicit arguments, in order to recover them explicitly without having
to list them as given arguments:

\begin{code}

domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X

\end{code}

-----------
Binary sums
-----------

We now define the disjoint sum of two types X and Y. The elements of
the type X + Y are all of the form inl x for x : X or inr y for y : Y.

\begin{code}

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
  inl : X → X + Y
  inr : Y → X + Y

\end{code}

To prove that a property of the sum holds for all A, it is enough to
prove that A(inl x) holds for all x : X and that A (inr y) holds for
all x : X.

\begin{code}

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X + Y → 𝓦 ̇}
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction f g (inl x) = f x
+-induction f g (inr y) = g y

\end{code}

When A and B are understood as mathematical statements, A + B is
understood as "A or B", because to prove "A or B" when has to prove
either A or B. When A and B are simultaneously possible, we have two
proofs, but sometimes we want to deliberately ignore which one we get,
when we want to get a truth value, and in this case we use the
truncation ∥ A + B ∥.

-----------------
The identity type
-----------------

Intuitively, the following definition says that the only element of
the type x ≡ x is something called "refl x" (for reflexivity).

\begin{code}

data _≡_ {𝓤} {X : 𝓤 ̇} : X → X → 𝓤 ̇  where
 refl : (x : X) → x ≡ x

\end{code}

An intuition for this type family _≡_ : X → X → 𝓤 is that it gives the
least reflexive relation on X.

Whereas we can make the intuition that x ≡ x has precisely one element
good by postulating a certain K axiom due to Thomas Streicher, which
comes with Agda by default but we have disabled, we cannot *prove*
that refl x is the only element of x ≡ x. And this non-provability
result was established by Martin Hofmann and Thomas Streicher.

In fact, the univalence axiom will say, in particular, that for some
types X and x : X, the type x ≡ x does have more than one element.

A possible way to understand the point refl x of the type x ≡ x is as
the "generic identification" between x and itself, but which is by no
means the necessarily *only* identitification in univalent
foundations. It is generic in the sense that to explain what happens
with all identifications p : x ≡ y between points x and y of a type X,
it suffices to explain what happens with the generic identification
refl x : x ≡ y for all x:X. This is the principle of induction, which
is traditionally called J but we will call ≡-induction.

\begin{code}

≡-induction : {X : 𝓤 ̇} (x : X) (A : (y : X) → x ≡ y → 𝓥 ̇ )
            → A x (refl x) → (y : X) (p : x ≡ y) → A y p
≡-induction x A a x (refl x) = a

\end{code}

Cf. the Yoneda Lemma in category theory, if you are familiar with
this subject, which says that certain natural transformations are
uniquely determined by their action on the identity arrow, even if
they are defined for all arrows.

Martin-Löf's identity type is given the data

  * _≡_ (which he called Id)
  * refl
  * ≡-induction (which he called J)
  * The equation we gave for induction

However, we will not use this induction principle, because we can
instead work with the instances we need by "pattern matching on refl"
(which is just what we did to define the principle itself) and there
is a theorem by Jesper Cockx which says that with the option
without-K, pattern matching on refl can define/prove precisely what J
can (https://dl.acm.org/citation.cfm?id=2628139).

For the record, we define the original MLTT notations for the above in
Agda, where the original J has the arguments in a slightly different
way as our ≡-induction.

\begin{code}

Id : (X : 𝓤 ̇ ) → X → X → 𝓤 ̇
Id X x y = x ≡ y

J : (X : 𝓤 ̇ ) (B : (x y : X) → x ≡ y → 𝓥 ̇)
 → ((x : X) → B x x (refl x)) → (x y : X) (p : x ≡ y) → B x y p
J X B f x = ≡-induction x (λ y p → B x y p) (f x)

\end{code}

Exercise. It is much harder, but possible, to define ≡-induction from
Martin-Löf's J. You may wish to have a go.

With this, we have concluded the rendering of our spartan MLTT in Agda
notation.

------------------------------------------------------------------
Pause to give an example: formulation of the twin-prime conjecture
------------------------------------------------------------------

We illustrate the above constructs of MLTT to formulate this
conjecture.

\begin{code}

module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n) × is-prime p × is-prime (p ∔ 2)

\end{code}

Thus, can we write down not only definitions, constructions, theorems
and proofs, but also conjectures. They are just definitions of types.

------------------------------------------
The identity type in univalent mathematics
------------------------------------------

In the same way ℕ-recursion can be seen as the non-dependent special
case of ℕ-induction, the following transport function could be seen as
the non-dependent special case of ≡-induction if we had written its
type with the argument swapped as A x → x ≡ y → A y.  That is, to
define a function x ≡ y → A y, it is enough to give a point of A x.

\begin{code}

transport : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl _) = id

\end{code}

We can view a type X as a sort of category with home-types rather than
hom-sets, with composition defined as follows (and written in
so-called diagramatic order rather than the usual backwards order like
we wrote function composition).

Again the following is for use when we want to recover implicit
arguments without mentioning them.

\begin{code}

lhs : {X : 𝓤 ̇} {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇} {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

\end{code}

Given two identifications p : x ≡ y and q : y ≡ z, we can compose them
to get an identification p ∙ q : x ≡ y. This can also be seen as
transitivity of equality. Because the type of composition doesn't
mention p and q, we can use the non-dependent version of ≡-induction.

\begin{code}

_∙_ : {X : 𝓤 ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p

\end{code}

Here we are considering A t = x ≡ t, and using q to transport
A y to A z, that is x ≡ y to x ≡ z. (Exercise: define an alternative
version that uses p to transport. Can you prove that the two versions
give equal results?)

If we wanted to prove the following without pattern matching, this
time we would need the dependent version of induction on _≡_
(exercise: try to do this).

We have that refl provides a neutral element for composition of
identifications:

\begin{code}

refl-left : {X : 𝓤 ̇} {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇} {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p

\end{code}

And composition is associative:

\begin{code}

∙assoc : {X : 𝓤 ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)

\end{code}

And so we can view X has a category with hom-types x ≡ y. But all
arrows, the identifications, are invertible:

\begin{code}

_⁻¹ : {X : 𝓤 ̇} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))


⁻¹-left∙ : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

\end{code}

A category in which all arrows are invertible is called a
groupoid. The above is the basis for the Hofmann--Streicher groupoid
model of type theory.

But we actually get higher groupoids, because because given
identifications

   p q : x ≡ y

we can consider the identity type p ≡ q, and given

   u v : p ≡ q

we can consider the type u ≡ v, and so on ad infinitum.

https://arxiv.org/abs/0812.0298
https://lmcs.episciences.org/1062

For some types, like the natural numbers, we can prove that this
process trivializes after the first step, because the type x ≡ y has
at most one element. Such types are called sets.

Voevodsky defined the notion of hlevel to measure how long it takes
for the process to trivialize (see below).

Here are some related constructions with identifications:

\begin{code}

⁻¹-involutive : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

\end{code}

Given an identification p : x ≡ x' we get an identification
ap f p : f x ≡ f x' for any f : X → Y:

\begin{code}

ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p (refl (f (lhs p)))

\end{code}

This operation on identifications is functorial, in the sense that is
preserves the neutral element and commutes with composition.:

\begin{code}

ap-refl : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

\end{code}

Transport is also functorial with respect to identification
composition and function composition. By construction, it maps the
neutral element to the identity function. The apparent contravarience
is that we have defined function composition in the usual way, but
identification composition backwards (as is customary).

\begin{code}

transport∙ : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)

\end{code}

We will work with pointwise equality of functions, defined as follows,
which, using univalence, will be equivalent to equality of functions
(this conclusion is called function extensionality).

\begin{code}

_∼_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → ((x : X) → A x) → ((x : X) → A x) → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

\end{code}

When writing p ∙ q, we lose information on the lhs and rhs of the
identification, which makes some definitions hard to read. We now
introduce notation to be able to write e.g.

    x ≡⟨ p ⟩ y ≡⟨ q ⟩ z ∎

as a synonym of p ∙ q with some of the implicit arguments of _∙_ made
explicit. We have one ternary "mixfix" operator _≡⟨_⟩_ and one unary
"postfix" operator _∎.

\begin{code}

_≡⟨_⟩_ : {X : 𝓤 ̇} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇} (x : X) → x ≡ x
x ∎ = refl x

\end{code}

------------------------------------------
Dependent equality and equality in Σ types
------------------------------------------

If we have A : X → 𝓥 ̇ and an identification p : x ≡ y for x y : X, we
get the identification ap A p : A x ≡ A y. However, if we have a : A x
and b : B y, we cannot write down the type a ≡ b. This is because the
types A x and A y are not the same, but only identified, and in
general there can be many identifications, not just ap A p.

So we define a notion of dependent equality between elements a : A x
and b : A y, where the dependency is on an given identification
p : x ≡ y. We write

  dId A p a b

for the type of "identifications of a and b dependent on p over the
family A".

We can define this by

  dId A (refl x) a b = (a ≡ b).

Because

  transport A (refl x) a = a,

by definition, we may as well defined dId as follows.

\begin{code}

dId : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y) → A x → A y → 𝓥 ̇
dId A p a b = transport A p a ≡ b

\end{code}

We will define a special syntax to be able to write this in a more
symmetrical way, so that we can write

  a ≡[ p / A ] b

for equality of a and b dependent on p over A. Because we have chosen
to say "over", we may as well use the symbol "/" to express this.

\begin{code}

syntax dId A p a b = a ≡[ p / A ] b

\end{code}

Notice that this is a quaternary "mix-fix" operator _≡[_/_ ]_.

We have designed things so that, by construction, we get the
following.

\begin{code}

≡-on-refl-is-≡ : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
               → (a ≡[ refl x / A ] b) ≡ (a ≡ b)

≡-on-refl-is-≡ A {x} a b = refl (a ≡ b)

\end{code}

Notice the perhaps unfamiliar nested use of equality: the type
"transport A (refl x) a ≡ b" is equal to the identity type "a ≡ b".
The proof is the reflexivity identification of the type "a ≡ b".

This is possible only because universes are genuine types (and because
transport A (refl x) a = a by definition).  We rewrite the above
making the implicit arguments of refl explicit so that this becomes
apparent:

\begin{code}

≡-on-refl-is-≡' : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
                → (a ≡[ refl x / A ] b) ≡ (a ≡ b)

≡-on-refl-is-≡' {𝓤} {𝓥} {X} A {x} a b = refl {𝓥 ⁺} {𝓥 ̇} (a ≡ b)

\end{code}

This says that we are taking the reflexivity proof of the equality type
of the universe 𝓥, which lives in the next universe 𝓥 ⁺, for the
element "a ≡ b" (which is a type) of 𝓥.

With this notion, we can characterize equality in Σ types as follows.

-------------------
Equality in Σ types
-------------------

\begin{code}

to-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A}
       → σ ≡ τ
       → Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ
from-Σ-≡ (refl (x , a)) = refl x , refl a

\end{code}

If we define "logical equivalence" by

\begin{code}

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

\end{code}

then the above gives

  (σ ≡ τ) ⇔ Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ

But this is a very weak statement when the left and right-hand
equality types may have multiple elements, which is precisely the
point of univalent mathematics (to allow equality types with multiple
elements and put them to good use).

What we want is the lhs and rhs to be isomorphic, or more precisely,
equivalent in the sense of Voevodsky.

Once we have defined this notion _≃_ of type equivalence, this
characterization will become an equivalence

  (σ ≡ τ) ≃ Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ

Even this is not sufficiently precise, because in general there are
many equivalences, for example in the type

  𝟙 + 𝟙 ≃ 𝟙 + 𝟙,

which has precisely two equivalences:

  (𝟙 + 𝟙 ≃ 𝟙 + 𝟙) ≃ 𝟙 + 𝟙

What we want to say is that the map from-Σ-≡ is an equivalence.

Voevodsky came up with a definition of a type "f is an equivalence"
which is always a subsingleton: a given function f can be an
equivalence in an most one way.

------------------------------------
Voevodsky's notion of hlevel in MLTT
------------------------------------

Voevodsky's hlevels 0,1,2,3,... are shifted by 2 and correspond to
-2-groupoids (constractible types), -1-groupoids (subsingletons),
0-groupoids (sets),...

First Voevodsky defined a notion of "contractible" type, which here we
refer to as "singleton type".

\begin{code}

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)

\end{code}

Then the hlevel relation is defined by induction on types, with the
induction step working on the identity types:

\begin{code}

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → (x ≡ x') is-of-hlevel n

\end{code}

It is sometimes convenient to have an equivalent formulations of the
levels 1 (as subsingletons) and 2 (as sets) which is used often in
practice, which we now develop.

When working with singleton types, it will be convenient to have
distinghished names for the two projections:

\begin{code}

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ

\end{code}

-----------------------------------------------
Subsingletons (or propositions or truth values)
-----------------------------------------------

A type is a subsingleton (or a proposition or a truth value) if it has
at most one element, that is, any two of its elements are equal.

\begin{code}

is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton ⋆ ⋆ = refl ⋆

\end{code}

The following are more logic-oriented terminologies for the notion.

\begin{code}

is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop = is-subsingleton
is-truth-value = is-subsingleton

\end{code}

The terminology "is-subsingleton" is more mathematical and avoids the
clash with the "propositions as types" slogan.
https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

\begin{code}

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y ⟩
                                             y ∎

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ ) → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)

\end{code}

------------------------------------------
The univalent principle of excluded middle
------------------------------------------

Under excluded middle, these are the only two subsingletons, up to
equivalence. In fact, excluded middle in univalent mathematics says
precisely that.

\begin{code}

EM EM' : 𝓤 ⁺ ̇
EM   {𝓤} = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM'  {𝓤} = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X

\end{code}

Notice that the above don't assert excluded middle, but instead say
what excluded middle is (like when we said what the twin-prime
conjecture is), in two logically equivalence versions:

\begin{code}

EM-gives-EM' : EM {𝓤} → EM'  {𝓤}
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr x) = inr x

EM'-gives-EM : EM' {𝓤} → EM  {𝓤}
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x

\end{code}

We will not assume or deny excluded middle, which is an independent
statement (can't be proved or disproved).

----
Sets
----

A type is a set if there is at most one way for any two of its
elements to be equal:

\begin{code}

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)

\end{code}

To characterize sets as the types of hlevel 2, we will use the
following.

------------------------------
A version of Hedberg's Theorem
------------------------------

We first need to show that subsingletons are sets, and this is not
easy. We use an argument due to Hedberg
https://homotopytypetheory.org/references/hedberg/
in its version formulated in the paper
https://link.springer.com/chapter/10.1007/978-3-642-38946-7_14

\begin{code}

wconstant : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

\end{code}

NB. "w" stands for "weakly". We won't discuss this here. The readers
can entertain themselves by looking at innumerous old discussions in
the HoTT mailing list archives. Perhaps "incoherently constant" would
be a better terminology, with "coherence" understood in the
∞-categorical sense. Beginners can safely ignore this remark. The
following is also probably not very good terminology, but we haven't
come up with a better one yet.

\begin{code}

collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ \(f : X → X) → wconstant f

collapser : (X : 𝓤 ̇ ) → collapsible X → X → X
collapser X (f , w) = f

collapser-wconstancy : (X : 𝓤 ̇ ) (c : collapsible X) → wconstant (collapser X c)
collapser-wconstancy X (f , w) = w

hedberg : {X : 𝓤 ̇} (x : X)
        → ((y : X) → collapsible (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)
hedberg {𝓤} {X} x c y p q =
 p                       ≡⟨ a y p ⟩
 f x (refl x)⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 f x (refl x)⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹ ⟩
 q                       ∎
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = pr₁ (c y)
  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = pr₂ (c y)
  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹

\end{code}

--------------------------
A characterization of sets
--------------------------

\begin{code}

≡-collapsible : 𝓤 ̇ → 𝓤 ̇
≡-collapsible X = (x y : X) → collapsible(x ≡ y)

sets-are-≡-collapsible : (X : 𝓤 ̇ ) → is-set X → ≡-collapsible X
sets-are-≡-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q

≡-collapsibles-are-sets : (X : 𝓤 ̇ ) → ≡-collapsible X → is-set X
≡-collapsibles-are-sets X c x = hedberg x (λ y → collapser (x ≡ y) (c x y) ,
                                                 collapser-wconstancy (x ≡ y) (c x y))

\end{code}

----------------------
Subsingletons are sets
----------------------

In the definition of the auxiliary function f, we ignore the argument p,
using the fact that X is a subsingleton instead, to get a wconstant function:

\begin{code}

subsingletons-are-≡-collapsible : (X : 𝓤 ̇ ) → is-subsingleton X → ≡-collapsible X
subsingletons-are-≡-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = ≡-collapsibles-are-sets X (subsingletons-are-≡-collapsible X s)

\end{code}

-------------------------------------------
The types of hlevel 1 are the subsingletons
-------------------------------------------

\begin{code}

subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ ) → is-subsingleton X → X is-of-hlevel 1
subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ ) → X is-of-hlevel 1 → is-subsingleton X
types-of-hlevel-1-are-subsingletons X = f
 where
  f : ((x y : X) → is-singleton (x ≡ y)) → (x y : X) → x ≡ y
  f s x y = center (x ≡ y) (s x y)

\end{code}

----------------------------------
The types of hlevel 2 are the sets
----------------------------------

\begin{code}

sets-are-of-hlevel-2 : (X : 𝓤 ̇ ) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
 where
  g : ((x y : X) → is-subsingleton (x ≡ y)) → (x y : X) → (x ≡ y) is-of-hlevel 1
  g t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 ̇ ) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X = f
 where
  f : ((x y : X) → (x ≡ y) is-of-hlevel 1) → (x y : X) → is-subsingleton (x ≡ y)
  f s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)

\end{code}

----------------------------
The hlevels are upper closed
----------------------------

A singleton is a subsingleton, a subsingleton is a set, ... , a type
of hlevel n is of hlevel n+1 too, ...

\begin{code}

hlevel-upper : (X : 𝓤 ̇ ) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X zero = γ
 where
  γ : (h : is-singleton X) (x y : X) → is-singleton (x ≡ y)
  γ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h
    p : x ≡ y
    p = k x y
hlevel-upper X (succ n) = λ h x y → hlevel-upper (x ≡ y) n (h x y)

\end{code}

To be consistent with the above, all types have level ∞. We don't need
a definition for this vacuous notion. But what may happen (and it does
with univalence) is that there are types which don't have any finite
hlevel. Such types then have "minimal hlevel ∞".

Exercise. Formulate and prove the following. The type 𝟙 has minimal
hlevel 0. The type 𝟘 has minibal hlevel 1, the type ℕ has minimal
hlevel 2.

-------------------
Example: ℕ is a set
-------------------

We first prove the Peano axioms that we had left until we had a
notion of equality in our type theory, which we now do.

This is how one proves in MLTT that ¬(succ x ≡ 0). Agda allows one to
prove this rather easily with "()" patterns, but this mechanism
doesn't belong to the realm of MLTT. For this reason, we are using
this feature only once, to prove 𝟘-induction, which does belong to MLTT.

\begin{code}

positive-not-zero : (x : ℕ) → ¬(succ x ≡ 0)
positive-not-zero x = k
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f
  h : 𝟙 ≡ 𝟘 → 𝟙 → 𝟘
  h = transport id
  k : succ x ≡ 0 → 𝟘
  k p = h (g p) ⋆

not-≡-sym : {X : 𝓤 ̇} {x y : X} → ¬(x ≡ y) → ¬(y ≡ x)
not-≡-sym {𝓤} {X} {x} {y} k = λ (p : y ≡ x) → k (p ⁻¹)
pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred

\end{code}

With this we have proved all the Peano axioms.

Without excluded middle, we can prove that ℕ has decidable equality:

\begin{code}

ℕ-has-decidable-equality : (x y : ℕ) → (x ≡ y) + ¬(x ≡ y)
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (not-≡-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : (x ≡ y) + ¬(x ≡ y) → (succ x ≡ succ y) + ¬(succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))

\end{code}

Exercise. You should do this kind of thing at least once in your
academic life: rewrite the above proof of the decidability of equality
of ℕ to use ℕ-induction instead of pattern matching and recursion.

And using the decidability of equality we can define a wconstant
function x ≡ y → x ≡ y and hence conclude that ℕ is a set. This
argument is due to Hedberg.

\begin{code}

ℕ-is-set : is-set ℕ
ℕ-is-set = ≡-collapsibles-are-sets ℕ ℕ-≡-collapsible
 where
  ℕ-≡-collapsible : ≡-collapsible ℕ
  ℕ-≡-collapsible x y = f (ℕ-has-decidable-equality x y) ,
                        κ (ℕ-has-decidable-equality x y)
   where
    f : (x ≡ y) + ¬(x ≡ y) → x ≡ y → x ≡ y
    f (inl p) q = p
    f (inr g) q = !𝟘 (x ≡ y) (g q)
    κ : (d : (x ≡ y) + ¬(x ≡ y)) → wconstant (f d)
    κ (inl p) q r = refl p
    κ (inr g) q r = !𝟘 (f (inr g) q ≡ f (inr g) r) (g q)

\end{code}

Exercise. Hedberg proved this for any type with decidable
equality. Generalize the above to account for this and hence develop /
practice your Agda skills.

----------------------------------------
Example: the types of magmas and monoids
----------------------------------------

A magma is a set equipped with a binary operation subject to no laws
(Bourbaki).

We can define the type of Magmas in a universe 𝓤, which lives in the
successor universe 𝓤 ⁺, as follows.

\begin{code}

Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X × (X → X → X)

\end{code}

This doesn't define what a magma is. It defines the type of magmas. A
magma is an element of this type.

If we omit the set-hood condition, we get the type of what we could
call ∞-magmas (then the type of magmas could be called 1-Magma).

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → (X → X → X)

\end{code}

A monoid is a set equipped with an associative binary operation and
with a two-sided neutral element, and so we get the type of monoids as
follows.

We first define the three laws:

\begin{code}

left-neutral : {X : 𝓤 ̇} → X → (X → X → X) → 𝓤 ̇
left-neutral {𝓤} {X} e _·_ = (x : X) → e · x ≡ x

right-neutral : {X : 𝓤 ̇} → X → (X → X → X) → 𝓤 ̇
right-neutral {𝓤} {X} e _·_ = (x : X) → x ≡ e · x

associative : {X : 𝓤 ̇} → (X → X → X) → 𝓤 ̇
associative {𝓤} {X}  _·_ = (x y z : X) → (x · y) · z ≡ x · (y · z)

\end{code}

Then a monoid is a set equipped with such e and _·_ satisfying these
three laws:

\begin{code}

Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoid 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X
                         × Σ \(_·_ : X → X → X)
                         → Σ \(e : X)
                         → left-neutral e _·_
                         × right-neutral e _·_
                         × associative _·_

\end{code}

NB. People are more likely to use "records" in Agda rather than
iterated Σ's as above (remember that we defined Σ using a
record). This is fine, because records amount to iterated Σ types
(remember that also _×_ is a Σ type, by definition). Here, however, we
are being deliberately purist. Once we have defined our Agda notation
for MLTT, we want to stick to it. This is for teaching purposes (of
MLTT, encoded in Agda, not of Agda itself in its full glory).

We could drop the "is-set X" condition, but then we wouldn't get
∞-monoids in any reasonable sense. We would instead get "wild
∞-monoids" or "incoherent ∞-monoids". The reason is that in monoids
(with sets as carriers) the neutrality and associativity equations can
hold in at most one way, by definition of set. But if we drop the
set-hood requirement, then the equations can hold in multiple
ways. And then one is forced to consider equations between the
witnesses of the equations (all the way up in the ∞-case), which is
what "coherence data" means. The wildness or incoherence amounts to
the absence of such data.

Exercise. Define the type of groups (with sets as carriers).

Exercise. Prove that the types of magmas, monoids and groups have
hlevel 3 (it is a 1-groupoid).  Prove that this is their minimal
level (can you do this with what we have learned so far?).

Exercise. Write down the various types of categories defined in the
HoTT book in Agda.

Exercise. Try to define a type of topological spaces.

-----------------------------------------
Each hlevel is closed under Π, Σ , Id, +
-----------------------------------------

TODO. We will need at least function extensionality. A proof with full
univalence is quicker. So this section should be moved to somewhere
appropriate. If we do it.

--------
Retracts
--------

Here we use retracts as a technique to transfer properties between
types. For instance, retracts of singletons are singletons. Showing
that a type X is a singleton may be difficult to do directly by
applying the definition, but it may be easy to show that X is a
retract of Y for a type Y that is already known to be a singleton, or
that is easy to show to be a singleton. In these notes, a major
application will be to get a simple proof that invertible maps are
equivalences in the sense of Voevodsky.

A section of a function is a left inverse.

\begin{code}

has-section : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ \(s : codomain r → domain r) → r ∘ s ∼ id

\end{code}

Notice that "has-section r" is the type of all sections (s , η) of r,
which may well be empty. So a point of this type is a designated
section s of r, together with the datum η. Unless the domain of r is a
set, this datum is not property, and we may well have an element
(s , η') of the type "has-section r" with η' distinct from η for the same s.

We read "X ◁ Y" has "X is a retract of Y". But this type actually
collects all the ways in which X is a retract of Y (and so is data or
structure, rather than property, where properties are taken to be
subsingleton valued).

\begin{code}

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ \(r : Y → X) → has-section r

\end{code}

A function that has a section is called a retraction. We use this
terminology also for the function that projects out the retraction.

\begin{code}

retraction : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇} {Y : 𝓥 ̇} (ρ : X ◁ Y) → retraction ρ ∘ section ρ ∼ id
retract-equation (r , s , η) = η

\end{code}

The identity retraction:

\begin{code}

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl X = id , id , refl

\end{code}

Exercise: The identity retraction is by no means the only retraction
of a type onto itself in general, of course. Prove that we have (that
is, produce an element of the type) ℕ ◁ ℕ with the function
pred : ℕ → ℕ defined above as the retraction to exercise your Agda
abilities.

The composition of two retractions.

\begin{code}

_◁∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
     → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , p)
 where
  p = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
            r (s x)           ≡⟨ η x ⟩
            x                 ∎

\end{code}

Composition with an implicit argument made explicit:

\begin{code}


_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

\end{code}

Postfix notation for the identity retraction:

\begin{code}

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = ◁-refl X

\end{code}

-----------------------
Natural transformations
----------------------

\begin{code}

Nat : {X : 𝓤 ̇} → (X → 𝓥 ̇ ) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x

Nats-are-natural : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y) → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

NatΣ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

\end{code}

------------------------------------------------
Behaviour of Σ types with respect to retractions
------------------------------------------------

\begin{code}

Σ-retract : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇) (B : X → 𝓦 ̇)
          → ((x : X) → (A x) ◁ (B x)) → Σ A ◁ Σ B
Σ-retract X A B ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)
  s : (x : X) → A x → B x
  s x = section (ρ x)
  η : (x : X) (a : A x) → r x (s x a) ≡ a
  η x = retract-equation (ρ x)
  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ≡ σ
  η' (x , a) = x , r x (s x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
               x , a           ∎

\end{code}

Reindexing of retracts of Σ types.

\begin{code}

Σ-retract-reindexing : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X → 𝓦 ̇} (r : Y → X)
                     → has-section r
                     → (Σ \(x : X) → A x) ◁ (Σ \(y : Y) → A (r y))
Σ-retract-reindexing {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)
  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = (s x , transport A ((η x)⁻¹) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (η x , p)
   where
    p : transport A (η x) (transport A ((η x)⁻¹) a) ≡ a
    p = transport A (η x) (transport A ((η x)⁻¹) a) ≡⟨ (ap (λ - → - a) (transport∙ A ((η x)⁻¹) (η x)))⁻¹ ⟩
        transport A ((η x)⁻¹ ∙ η x ) a              ≡⟨ ap (λ - → transport A - a) (⁻¹-left∙ (η x)) ⟩
        transport A (refl x) a                      ≡⟨ refl a ⟩
        a                                           ∎

\end{code}

The above defines the property of a type being a singleton. The
following defines singleton types, which have the property of being
singletons.

\begin{code}

singleton-type : {X : 𝓤 ̇} → X → 𝓤 ̇
singleton-type x = Σ \y → y ≡ x

singleton-type-center : {X : 𝓤 ̇} (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇} (x y : X) (p : y ≡ x) → singleton-type-center x ≡ (y , p)
singleton-type-centered x x (refl x) = refl (singleton-type-center x)

singleton-types-are-singletons : {X : 𝓤 ̇} (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons {𝓤} {X} x = singleton-type-center x , a
 where
  a : (σ : singleton-type x) → singleton-type-center x ≡ σ
  a (y , p) = singleton-type-centered x y p

\end{code}

Technique to show that some types are singletons:

\begin{code}

retract-of-singleton : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                     → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ : (y : codomain r) → r c ≡ y
  γ y = r c     ≡⟨ ap r (φ (s y)) ⟩
        r (s y) ≡⟨ η y ⟩
        y       ∎

\end{code}

-----------------------
Fibers and equivalences
-----------------------

The main MLTT definitions conceived by Voevodsky are of singleton type
(or contractible type), hlevel (including subsingleton and set), and
of type equivalence, which we now define and study.

We first define invertible maps (quasi-inverses in the HoTT-book terminology.)

\begin{code}

invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

\end{code}

The problem with this notion is that invertibility is not a
subsingleton in general: we can prove that g is unique when it exists,
but the data is not unique in general unique. Voevodsky came up with
the following notion of equivalence, which is always a subsingleton in
univalent mathematics, and logically equivalent to invertibility (so
we will have a retraction "is-equiv f ◁ invertible f").

\begin{code}

fiber : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ \(x : domain f) → f x ≡ y

is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)

inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = pr₁ (center (fiber f y) (e y))

inverse-is-section : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f)
                   → (y : Y) → f (inverse f e y) ≡ y
inverse-is-section f e y = pr₂ (center (fiber f y) (e y))

inverse-centrality : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f) (y : Y)
                   → (t : fiber f y) → (inverse f e y , inverse-is-section f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverse-is-retraction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f)
                      → (x : X) → inverse f e (f x) ≡ x
inverse-is-retraction f e x = ap pr₁ (inverse-centrality f e (f x) (x , (refl (f x))))

\end{code}

Relationship beween equivalence and invertible maps:

\begin{code}

equivs-are-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → invertible f
equivs-are-invertible f e = (inverse f e , inverse-is-retraction f e , inverse-is-section f e)

invertibles-are-equivs : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → invertible f → is-equiv f
invertibles-are-equivs {𝓤} {𝓥} {X} {Y} f (g , η , ε) y₀ = γ
 where
  a : (y : Y) → (f (g y) ≡ y₀) ◁ (y ≡ y₀)
  a y = r , s , rs
   where
    r : y ≡ y₀ → f (g y) ≡ y₀
    r p = f (g y) ≡⟨ ε y ⟩
          y       ≡⟨ p ⟩
          y₀      ∎
    s : f (g y) ≡ y₀ → y ≡ y₀
    s q = y       ≡⟨ (ε y)⁻¹ ⟩
          f (g y) ≡⟨ q ⟩
          y₀      ∎
    rs : (q : f (g y) ≡ y₀) → r (s q) ≡ q
    rs q = ε y ∙ ((ε y)⁻¹ ∙ q) ≡⟨ (∙assoc (ε y) ((ε y)⁻¹) q)⁻¹ ⟩
           (ε y ∙ (ε y)⁻¹) ∙ q ≡⟨ ap (_∙ q) (⁻¹-right∙ (ε y)) ⟩
           refl (f (g y)) ∙ q  ≡⟨ refl-left ⟩
           q                   ∎
  b : fiber f y₀ ◁ singleton-type y₀
  b = (Σ \(x : X) → f x ≡ y₀)     ◁⟨ Σ-retract-reindexing g (f , η) ⟩
      (Σ \(y : Y) → f (g y) ≡ y₀) ◁⟨ Σ-retract Y (λ y → f (g y) ≡ y₀) (λ y → y ≡ y₀) a ⟩
      (Σ \(y : Y) → y ≡ y₀)       ◀
  γ : is-singleton (fiber f y₀)
  γ = retract-of-singleton b (singleton-types-are-singletons y₀)

\end{code}

Composition of invertible maps:

\begin{code}

∘-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)
∘-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {f'} (g' , gf' , fg') (g , gf , fg)  = g ∘ g' , η , ε
 where
  η : (x : X) → g (g' (f' (f x))) ≡ x
  η x = g (g' (f' (f x))) ≡⟨ ap g (gf' (f x)) ⟩
        g (f x)           ≡⟨ gf x ⟩
        x                 ∎
  ε : (z : Z) → f' (f (g (g' z))) ≡ z
  ε z = f' (f (g (g' z))) ≡⟨ ap f' (fg (g' z)) ⟩
        f' (g' z)         ≡⟨ fg' z ⟩
        z                 ∎

\end{code}

Identity equivalence, and composition of equivalences by reduction to
invertible maps:

\begin{code}

id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (id {𝓤} {X})
id-is-equiv X = singleton-types-are-singletons

∘-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)
∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = invertibles-are-equivs (g ∘ f)
                                                    (∘-invertible (equivs-are-invertible g i)
                                                                  (equivs-are-invertible f j))
\end{code}

The type of equivalences:

\begin{code}

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq-to-fun : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ≃ Y → X → Y
Eq-to-fun (f , e) = f

Eq-to-fun-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} (e : X ≃ Y) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv (f , i) = i

\end{code}

Identity and composition of equivalences:

\begin{code}

≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = id , id-is-equiv X

_●_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_●_ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} (f , d) (f' , e) = f' ∘ f , ∘-is-equiv e d

\end{code}

We can use the following for equational reasoning with equivalences:

\begin{code}

_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = ≃-refl

\end{code}

------------------------
Examples of equivalences
------------------------

The function "transport A p" is an equivalence.

\begin{code}

transport-is-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)

transport-≃ : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X}
            → x ≡ y → A x ≃ A y
transport-≃ A p = transport A p , transport-is-equiv A p

\end{code}

A longer proof for the sake of illustration:

\begin{code}

transport-is-equiv' : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                    → is-equiv (transport A p)
transport-is-equiv' A p = invertibles-are-equivs
                          (transport A p)
                          (transport A (p ⁻¹) ,
                           (λ a → transport A (p ⁻¹) (transport A p a) ≡⟨ (ap (λ - → - a) (transport∙ A p (p ⁻¹)))⁻¹ ⟩
                                  transport A (p ∙ p ⁻¹) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-right∙ p) ⟩
                                  a                                    ∎) ,
                            λ a → transport A p (transport A (p ⁻¹) a) ≡⟨ (ap (λ - → - a) (transport∙ A (p ⁻¹) p))⁻¹ ⟩
                                  transport A (p ⁻¹ ∙ p) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-left∙ p) ⟩
                                  a                                    ∎)
\end{code}

Characterization of equality in Σ types:

\begin{code}

Σ-≡-equivalence : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (σ τ : Σ A)
                → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
Σ-≡-equivalence  {𝓤} {𝓥} {X} {A}  σ τ = from-Σ-≡ ,
                                        invertibles-are-equivs from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ) → from-Σ-≡ (to-Σ-≡ w) ≡ w
  η (refl p , refl q) = refl (refl p , refl q)
  ε : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε (refl σ) = refl (refl σ)

\end{code}

----------------------------
Voevodsky's univalence axiom
----------------------------

There is a canonical transformation (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y that
sends the identity identification "refl X : X X ≡ X" to the identity
equivalence "≃-refl X" by induction on identifications. The univalence
axiom, for the universe 𝓤, say that this canonical map is itself an
equivalence.

\begin{code}

Id-to-Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id-to-Eq X X (refl X) = ≃-refl X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id-to-Eq X Y)

univalence : 𝓤ω
univalence = (𝓤 : Universe) → is-univalent 𝓤

\end{code}

We emphasize that this doesn't posit that univalence holds. It says
what univalence is (like the type that says what the twin-prime
conjecture is).

\begin{code}

Eq-to-Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq-to-Id ua X Y = inverse (Id-to-Eq X Y) (ua X Y)

\end{code}

Two ways to convert a type equality into a function:

\begin{code}

Id-to-fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id-to-fun {𝓤} {X} {Y} p = Eq-to-fun (Id-to-Eq X Y p)

Id-to-fun' : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id-to-fun' = transport id

Id-to-funs-agree : {X Y : 𝓤 ̇} (p : X ≡ Y)
                 → Id-to-fun p ≡ Id-to-fun' p
Id-to-funs-agree (refl X) = refl id

\end{code}


----------------------------------------
What characterizes univalent mathematics
----------------------------------------

It is not the univalence axiom. We have defined and studied the main
concepts of univalent mathematics in a pure, spartan MLTT. It is the
concepts of hlevel, including singleton, subsingleton and set, and the
notion of equivalence. Univalence *is* a fundamental ingredient, but
first we need the "correct" notion of equivalence to be able to
formulate it. If we formulate univalence with invertible maps instead,
we get a statement that is provable false. TODO. Probably include this
proof, so that the students can see how this fails.

-------------------------------------------------------
Exercises with sample solutions at the end of this file
-------------------------------------------------------

Here are some facts whose proofs are left to the reader.

Define functions for the following type declarations. As a matter of
procedure, I suggest that for each type declaration below you add
another one with the same type and new name
e.g. section-are-lc-solution, because we already have solutions with
these names at the end of the file.

We start with left cancellability of functions.

\begin{code}

left-cancellable : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ≡ f x' → x ≡ x'

lc-maps-reflect-subsingletonness : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                                 → left-cancellable f
                                 → is-subsingleton Y
                                 → is-subsingleton X

has-retraction : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ \(r : codomain s → domain s) → r ∘ s ∼ id

sections-are-lc : {X : 𝓤 ̇} {A : 𝓥 ̇} (s : X → A) → has-retraction s → left-cancellable s

equivs-have-retractions : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → has-retraction f

equivs-have-sections : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → has-section f

equivs-are-lc : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-equiv f → left-cancellable f

equivs-reflect-subsingletonness : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                                → is-equiv f
                                → is-subsingleton Y
                                → is-subsingleton X

sections-closed-under-∼ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f g : X → Y)
                        → has-retraction f
                        → g ∼ f
                        → has-retraction g

retractions-closed-under-∼ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g
\end{code}

An alternative notion of equivalence, equivalent to Voevodsky's, has
been given by Andre Joyal:

\begin{code}

is-joyal-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f

\end{code}

Provide definitions for the following type declarations:

\begin{code}

joyal-equivs-are-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                            → is-joyal-equiv f → invertible f

joyal-equivs-are-equivs : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                        → is-joyal-equiv f → is-equiv f

invertibles-are-joyal-equivs : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                        → is-equiv f → is-joyal-equiv f

equivs-closed-under-∼ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f g : X → Y)
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g

equivs-closed-under-∼' : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f g : X → Y)
                       → is-equiv f
                       → f ∼ g
                       → is-equiv g
equivs-closed-under-∼' f g e h = equivs-closed-under-∼ f g e (λ x → (h x)⁻¹)

≃-gives-◁ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇) → X ≃ Y → X ◁ Y

≃-gives-▷ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇) → X ≃ Y → Y ◁ X

equiv-to-singleton : (X : 𝓤 ̇ ) (Y : 𝓥 ̇)
                   → X ≃ Y → is-singleton Y → is-singleton X

pr₁-equivalence : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇)
                → ((x : X) → is-singleton (A x))
                → is-equiv (pr₁ {𝓤} {𝓥} {X} {A})

ΠΣ-distr-≃ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {P : (x : X) → A x → 𝓦 ̇}
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))

Σ-cong : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇}
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

⁻¹-≃ : {X : 𝓤 ̇} (x y : X) → (x ≡ y) ≃ (y ≡ x)

singleton-type' : {X : 𝓤 ̇} → X → 𝓤 ̇
singleton-type' x = Σ \y → x ≡ y

singleton-types-≃ : {X : 𝓤 ̇} (x : X) → singleton-type' x ≃ singleton-type x

singleton-types-are-singletons' : {X : 𝓤 ̇} (x : X) → is-singleton (singleton-type' x)

singletons-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇)
                      → is-singleton X → is-singleton Y → X ≃ Y

maps-of-singletons-are-equivs : (X : 𝓤 ̇ ) (Y : 𝓥 ̇) (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f

NatΣ-fiber-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇) (φ : Nat A B)
                 → (x : X) (b : B x) → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇) (φ : Nat A B)
                                 → is-equiv(NatΣ φ) → ((x : X) → is-equiv(φ x))

\end{code}

---------------------------------------
Function extensionality from univalence
---------------------------------------

Function extensionality says that any two pointwise equal functions
are equal. This is known to be not provable or disprovable in MLTT. It
is an independent statement, which we abbreviate "funext". There will
be two stronger statements in a moment, namely the generalization to
dependent functions, and the construction of an equivalence (f ∼ g) ≃
(f ≡ g) and hence a designated equality among all possible ones. We
begin with the weak statement.

\begin{code}

funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} {f g : X → Y} → f ∼ g → f ≡ g

\end{code}

Exercise. Assuming funext, prove that, if f : X → Y is an equivalence
then so is the function (-) ∘ f : (Y → Z) → (X → Z).

Voevodsky's proved that univalence implies funext was to prove that the
precomposition function of the exercise using univalence rather than
funext, and then use this to prove funext.

\begin{code}

transport-is-pre-comp : (ua : is-univalent 𝓤) {X X' Y : 𝓤 ̇} (e : X ≃ X') (g : X' → Y)
                      → transport (λ - → - → Y) ((Eq-to-Id ua X X' e)⁻¹) g ≡ g ∘ Eq-to-fun e
transport-is-pre-comp ua {X} {X'} {Y} e g = f e (Eq-to-Id ua X X' e) (refl (Eq-to-Id ua X X' e))
 where
  f : (e : X ≃ X') (p : X ≡ X')
    → p ≡ Eq-to-Id ua X X' e
    → transport (λ - → - → Y) (p ⁻¹) g ≡ g ∘ Eq-to-fun e
  f e (refl x) = γ
   where
    γ : refl X ≡ Eq-to-Id ua X X e → g ≡ g ∘ Eq-to-fun e
    γ q = ap (g ∘_) b
     where
      a : ≃-refl X ≡ e
      a = ≃-refl X                         ≡⟨ ap (Id-to-Eq X X) q ⟩
          Id-to-Eq X X (Eq-to-Id ua X X e) ≡⟨ inverse-is-section (Id-to-Eq X X) (ua X X) e ⟩
          e                                ∎
      b : id ≡ Eq-to-fun e
      b = ap Eq-to-fun a

pre-comp-is-equiv : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇} (f : X → Y)
                  → is-equiv f
                  → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv ua {X} {Y} {Z} f i = j
 where
  e : X ≃ Y
  e = (f , i)

  of-course : Eq-to-fun e ≡ f
  of-course = refl f

  φ γ : (Y → Z) → (X → Z)
  φ g = g ∘ f
  γ g = transport (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹) g

  γ-is-equiv : is-equiv γ
  γ-is-equiv = transport-is-equiv (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹)

  h' : (g : Y → Z) → transport (λ - → - → _) ((Eq-to-Id ua X Y e)⁻¹) g ≡ g ∘ Eq-to-fun e
  h' = transport-is-pre-comp ua e

  h : γ ∼ φ
  h = h'

  j : is-equiv φ
  j = equivs-closed-under-∼' γ φ γ-is-equiv h

\end{code}

With this we can now prove the promised results.

\begin{code}

univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext ua {X} {Y} {f₀} {f₁} h = γ
 where
  Δ = Σ \(y₀ : Y) → Σ \(y₁ : Y) → y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl y)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (y : Y) → π₀ (δ y) ≡ y
    η y = refl y
    ε : (d : Δ) → δ (π₀ d) ≡ d
    ε (y , y , refl y) = refl (y , y , refl y)

  πδ : π₀ ∘ δ ≡ π₁ ∘ δ
  πδ = refl id

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = pre-comp-is-equiv ua δ δ-is-equiv

  π₀-equals-π₁ : π₀ ≡ π₁
  π₀-equals-π₁ = equivs-are-lc φ φ-is-equiv πδ

  γ : f₀ ≡ f₁
  γ = ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁

\end{code}

This definition of γ is probably too quick. Here are all the steps
performed silently by Agda, by expanding judgmental equalities,
indicated with refl here:

\begin{code}

  γ' = f₀                              ≡⟨ refl _ ⟩
       (λ x → f₀ x)                    ≡⟨ refl _ ⟩
       (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
       (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl _ ⟩
       (λ x → f₁ x)                    ≡⟨ refl _ ⟩
       f₁                              ∎

\end{code}

So notice that this relies on the so-called η-rule for judgmental
equality of functions, namely f = λ x → f x. Without it, we would get
that f₀ ∼ f₁ → (λ x → f₀ x) ≡ (λ x → f₁ x) instead.

-----------------------------------------------------------
Variations of function extensionality and their equivalence
-----------------------------------------------------------

Dependent function extensionality:

\begin{code}

dfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g

\end{code}

The above says that there is some map f ~ g → f ≡ g. The following
instead says that the canonical map in the other direction is an
equivalence:

\begin{code}

happly : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

\end{code}

Voevodsky showed that all notions of function extensionaliry are
equivalent to saying that products of singletons are singletons:

\begin{code}

vvfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇} {A : X → 𝓥 ̇} → ((x : X) → is-singleton (A x)) → is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe i = (λ x → pr₁ (i x)) , (λ f → fe (λ x → pr₂ (i x) (f x)))

\end{code}

We need some lemmas to get hfunext from vvfunext:

\begin{code}

post-comp-is-invertible : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇}
          → funext 𝓦 𝓤 → funext 𝓦 𝓥
          → (f : X → Y) → invertible f → invertible (λ (h : A → X) → f ∘ h)
post-comp-is-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

post-comp-is-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → funext 𝓦 𝓤 → funext 𝓦 𝓥
                   → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
post-comp-is-equiv fe fe' f e = invertibles-are-equivs
                                 (λ h → f ∘ h)
                                 (post-comp-is-invertible fe fe' f (equivs-are-invertible f e))

vvfunext-gives-hfunext : vvfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
vvfunext-gives-hfunext {𝓤} {𝓥} vfe {X} {Y} f = γ
 where
  a : (x : X) → is-singleton (Σ \(y : Y x) → f x ≡ y)
  a x = singleton-types-are-singletons' (f x)
  c : is-singleton ((x : X) → Σ \(y : Y x) → f x ≡ y)
  c = vfe a
  R : (Σ \(g : Π Y) → f ∼ g) ◁ (Π \(x : X) → Σ \(y : Y x) → f x ≡ y)
  R = ≃-gives-▷ _ _ ΠΣ-distr-≃
  r : (Π \(x : X) → Σ \(y : Y x) → f x ≡ y) → Σ \(g : Π Y) → f ∼ g
  r = λ _ → f , (λ x → refl (f x))
  d : is-singleton (Σ \(g : Π Y) → f ∼ g)
  d = retract-of-singleton R c
  e : (Σ \(g : Π Y) → f ≡ g) → (Σ \(g : Π Y) → f ∼ g)
  e = NatΣ (happly f)
  i : is-equiv e
  i = maps-of-singletons-are-equivs (Σ (λ g → f ≡ g)) (Σ (λ g → f ∼ g)) e (singleton-types-are-singletons' f) d
  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (λ g → f ≡ g) (λ g → f ∼ g) (happly f) i

\end{code}

And finally the seemingly rather weak, non-dependent funext implies
the seemingly strongest one, which closes the circle of logical
equivalences.

\begin{code}

funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = retract-of-singleton (r , s , rs) i
  where
   f : Σ A → X
   f = pr₁
   f-is-equiv : is-equiv f
   f-is-equiv = pr₁-equivalence X A φ
   g : (X → Σ A) → (X → X)
   g h = f ∘ h
   g-is-equiv : is-equiv g
   g-is-equiv = post-comp-is-equiv fe fe' f f-is-equiv
   i : is-singleton (Σ \(h : X → Σ A) → f ∘ h ≡ id)
   i = g-is-equiv id
   r : (Σ \(h : X → Σ A) → f ∘ h ≡ id) → Π A
   r (h , p) x = transport A (happly (f ∘ h) id p x) (pr₂ (h x))
   s : Π A → (Σ \(h : X → Σ A) → f ∘ h ≡ id)
   s φ = (λ x → x , φ x) , refl id
   rs : ∀ φ → r (s φ) ≡ φ
   rs φ = refl (r (s φ))

\end{code}

Corollaries:

\begin{code}

funext-gives-hfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')

funext-gives-dfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')

univalence-gives-hfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
univalence-gives-hfunext' ua ua' = funext-gives-hfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
univalence-gives-vvfunext' ua ua' = funext-gives-vvfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-hfunext : is-univalent 𝓤 → hfunext 𝓤 𝓤
univalence-gives-hfunext ua = univalence-gives-hfunext' ua ua

univalence-gives-dfunext : is-univalent 𝓤 → dfunext 𝓤 𝓤
univalence-gives-dfunext ua = hfunext-gives-dfunext (univalence-gives-hfunext ua)

univalence-gives-vvfunext : is-univalent 𝓤 → vvfunext 𝓤 𝓤
univalence-gives-vvfunext ua = univalence-gives-vvfunext' ua ua

\end{code}

------------------------------
Univalence is a (sub)singleton
------------------------------

If we use a type as an axiom, it should have at most one element. We
prove some generally useful lemmas first.

\begin{code}

Π-is-subsingleton : dfunext 𝓤 𝓥 → {X : 𝓤 ̇} {A : X → 𝓥 ̇}
                  → ((x : X) → is-subsingleton (A x)) → is-subsingleton (Π A)
Π-is-subsingleton fe i f g = fe (λ x → i x (f x) (g x))

being-a-singleton-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇} → is-subsingleton (is-singleton X)
being-a-singleton-is-a-subsingleton fe {X} (x , φ) (y , γ) = to-Σ-≡ (φ y , fe (λ z → s y z _ _))
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)
  s : is-set X
  s = subsingletons-are-sets X i

being-an-equiv-is-a-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                 → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                                 → is-subsingleton (is-equiv f)
being-an-equiv-is-a-subsingleton fe fe' f = Π-is-subsingleton fe (λ x → being-a-singleton-is-a-subsingleton fe')

univalence-is-a-subsingleton : is-univalent (𝓤 ⁺) → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingleton {𝓤} ua⁺ ua ua' = i ua ua'
 where
  fe₀ : funext 𝓤 𝓤
  fe₀ = univalence-gives-funext ua
  fe₁ : funext 𝓤 (𝓤 ⁺)
  fe₁ = univalence-gives-funext ua⁺
  fe₂ : funext (𝓤 ⁺) (𝓤 ⁺)
  fe₂ = univalence-gives-funext ua⁺
  dfe₁ : dfunext 𝓤 (𝓤 ⁺)
  dfe₁ = funext-gives-dfunext fe₁ fe₀
  dfe₂ : dfunext (𝓤 ⁺) (𝓤 ⁺)
  dfe₂ = funext-gives-dfunext fe₂ fe₂

  i : is-subsingleton (is-univalent 𝓤)
  i = Π-is-subsingleton dfe₂
       (λ X → Π-is-subsingleton dfe₂
               (λ Y → being-an-equiv-is-a-subsingleton dfe₁ dfe₂ (Id-to-Eq X Y)))

\end{code}

So if all universe all univalent then being univalent is a
subsingleton (and hence a singleton). This hypothesis of global
univalence cannot be expressed in our MLTT that only has countably
many universes, because global univalence would have to live in the
first universe after them. Agda does have such a universe 𝓤ω, and so
we can formulate it this. There would be no problem in extending our
MLTT to have such a universe if we so wished, in which case we would
be able to formulate and prove:

\begin{code}

global-univalence : 𝓤ω
global-univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-a-subsingleton₀ : global-univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingleton₀ {𝓤} α = univalence-is-a-subsingleton (α (𝓤 ⁺))

univalence-is-a-subsingleton₁ : global-univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-subsingleton₁ {𝓤} α = pointed-subsingletons-are-singletons
                                        (is-univalent 𝓤)
                                        (α 𝓤)
                                        (univalence-is-a-subsingleton₀ α)
\end{code}

--------------------------------------
hfunext and vvfunext are subsingletons
--------------------------------------

This is left as an exercise. Like univalence, the proof that these two
forms of function extensional extensionality require assumptions of
function extensionality at higher universes. So perhaps it is more
convenient to just assume global univalence. An inconvinience is that
the natural tool to use, Π-is-subsingleton, needs products with
explicit arguments, but we made some of the arguments of hfunext and
vvfunext implicit. One way around this problem is to define equivalent
versions with the arguments explicit, and establish an equivalence
between the new version and the original version.

--------------------------------------------
More applications of function extensionality
--------------------------------------------

\begin{code}

being-a-subsingleton-is-a-subsingleton : {X : 𝓤 ̇} → dfunext 𝓤 𝓤 → is-subsingleton (is-subsingleton X)
being-a-subsingleton-is-a-subsingleton {𝓤} {X} fe i j = c
 where
  l : is-set X
  l = subsingletons-are-sets X i
  a : (x y : X) → i x y ≡ j x y
  a x y = l x y (i x y) (j x y)
  b : (x : X) → i x ≡ j x
  b x = fe (a x)
  c : i ≡ j
  c = fe b


\end{code}

Here is a situation where hfunext is what is needed:

\begin{code}

Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇} {A : X → 𝓥 ̇}
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))
  b : is-subsingleton(f ≡ g)
  b = equivs-reflect-subsingletonness (happly f g) (hfe f g) a

being-set-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇} → is-subsingleton (is-set X)
being-set-is-a-subsingleton {𝓤} fe {X} = Π-is-subsingleton fe
                                          (λ x → Π-is-subsingleton fe
                                                  (λ y → being-a-subsingleton-is-a-subsingleton fe))

\end{code}

More generally:

\begin{code}

hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤 → (n : ℕ) (X : 𝓤 ̇ ) → is-subsingleton (X is-of-hlevel n)
hlevel-relation-is-subsingleton {𝓤} fe zero     X = being-a-singleton-is-a-subsingleton fe
hlevel-relation-is-subsingleton {𝓤} fe (succ n) X = Π-is-subsingleton fe
                                                      (λ x → Π-is-subsingleton fe
                                                              (λ x' → hlevel-relation-is-subsingleton {𝓤} fe n (x ≡ x')))
\end{code}

Exercise. The hlevels are closed under Σ and, using hfunext, also
under Π. Univalence is not needed, but makes the proof easier.  (If
you don't use univalence, you will need to show that hlevels are
closed under equivalence.)

------------------
Curry-Howard logic
------------------

Up to this point Curry-Howard logic has been enough for the purposes
of univalent mathematics.
https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

  * Mathematics statements are types.
  * Implication is function type "→".
  * Conjunction "and" is the type former _×_
  * "False" is the empty type 𝟘.
  * The negation of

But now consider the following attemps to define the notion of
surjective function and of image of a function.

\begin{code}

module surjection-image-attempt where



\end{code}


-----------------------------------------------
Voevodsky's approach to subsingleton truncation
-----------------------------------------------

Now we want to say that a type is inhabited in such a way that the
statement of inhabitedness is a subsingleton (using funext or
univalence if needed).

\begin{code}

is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

\end{code}

This says that if we have a function from X to a subsingleton P, then
P must have a point. So this fails when X=𝟘. When P=𝟘, we conclude
that ¬(¬X) if X is inhabited, which says that X is non-empty. However,
in the absence of excluded middle, inhabitedness is stronger than
excluded middle.

For simplicity in the formulation of the theorems, we assume global
dfunext.

\begin{code}

global-dfunext : 𝓤ω
global-dfunext = ∀ 𝓤 𝓥 → dfunext 𝓤 𝓥

inhabitedness-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ ) → is-subsingleton (is-inhabited X)
inhabitedness-is-a-subsingleton {𝓤} fe X = Π-is-subsingleton (fe (𝓤 ⁺) 𝓤)
                                            λ P → Π-is-subsingleton (fe 𝓤 𝓤)
                                                   (λ (s : is-subsingleton P)
                                                         → Π-is-subsingleton (fe 𝓤 𝓤) (λ (f : X → P) → s))

inhabited-intro : (X : 𝓤 ̇ ) → X → is-inhabited X
inhabited-intro X x = λ P s f → f x

inhabited-elim : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-elim X P s f φ = φ P s f

inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ ) → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-elim P P s id

\end{code}

There are two problems with this definition.

  * Inhabitedness has values in the next universe.

  * We can eliminate into propositions of the same universe only.

And there are proposed two ways to solve this:

  * Voevodsky works with certain resizing rules for subsingletons.
    http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf At the time
    of writing, the (relative) consistency of the system with such
    rules is an open question.

  * The HoTT book works with certain higher inductive types (HIT's).
    This is the same approach of taken by cubical Agda.

We will instead work with propositional truncations axiomatially,
which is compatible with the above two proposals.

----------------------------------
Axiomatic propositional truncation
----------------------------------

We consider its global version.




-------------------------------
Structure of identity principle
-------------------------------

Don't give code. Just gives some examples, including monoids, but not
only that.


------------------
Exercise solutions
------------------

We only give solutions to the exercises we stated in Agda.

\begin{code}

lc-maps-reflect-subsingletonness f l s x x' = l (s (f x) (f x'))

sections-are-lc s (r , ε) {x} {y} p = x       ≡⟨ (ε x)⁻¹ ⟩
                                      r (s x) ≡⟨ ap r p ⟩
                                      r (s y) ≡⟨ ε y ⟩
                                      y       ∎

equivs-have-retractions f e = (inverse f e , inverse-is-retraction f e)

equivs-have-sections f e = (inverse f e , inverse-is-section f e)

equivs-are-lc f e = sections-are-lc f (equivs-have-retractions f e)

equivs-reflect-subsingletonness f e = lc-maps-reflect-subsingletonness f (equivs-are-lc f e)

sections-closed-under-∼ f g (r , rf) h = (r ,
                                          λ x → r (g x) ≡⟨ ap r (h x) ⟩
                                                r (f x) ≡⟨ rf x ⟩
                                                x       ∎)
retractions-closed-under-∼ f g (s , fs) h = (s ,
                                             λ y → g (s y) ≡⟨ h (s y) ⟩
                                                   f (s y) ≡⟨ fs y ⟩
                                                   y ∎)

joyal-equivs-are-invertible f ((s , fs) , (r , rf)) = (s , sf , fs)
 where
  sf = λ (x : domain f) → s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
                          r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
                          r(f x)       ≡⟨ rf x ⟩
                          x            ∎

invertibles-are-joyal-equivs f (g , gf , fg) = ((g , fg) , (g , gf))

joyal-equivs-are-equivs f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)

equivs-are-joyal-equivs f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)

\end{code}

One way to show that equivalences are closed under pointwise equality
is by reduction to the above.

\begin{code}

equivs-closed-under-∼ f g e h = joyal-equivs-are-equivs g
                                 (retractions-closed-under-∼ f g (equivs-have-sections f e) h ,
                                  sections-closed-under-∼ f g (equivs-have-retractions f e) h)

\end{code}

Exercise. Prove that equivalences are closed under pointwise equality
directly, without the detour via Joyal equivalences.

\begin{code}

≃-gives-◁ X Y (f , e) = (inverse f e , f , inverse-is-retraction f e)


≃-gives-▷ X Y (f , e) = (f , inverse f e , inverse-is-section f e)

equiv-to-singleton X Y e = retract-of-singleton (≃-gives-◁ X Y e)

pr₁-equivalence {𝓤} {𝓥} X A s = invertibles-are-equivs pr₁ (g , η , ε)
 where
  g : X → Σ A
  g x = x , pr₁(s x)
  ε : (x : X) → pr₁ (g x) ≡ x
  ε x = refl (pr₁ (g x))
  η : (σ : Σ A) → g (pr₁ σ) ≡ σ
  η (x , a) = to-Σ-≡ (ε x , singletons-are-subsingletons (A x) (s x) _ a)

ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = φ , invertibles-are-equivs φ (γ , η , ε)
 where
  φ : (Π \(x : X) → Σ \(a : A x) → P x a) → Σ \(f : Π A) → Π \(x : X) → P x (f x)
  φ g = ((λ x → pr₁ (g x)) , λ x → pr₂ (g x))

  γ : (Σ \(f : Π A) → Π \(x : X) → P x (f x)) → Π \(x : X) → Σ \(a : A x) → P x a
  γ (f , φ) x = f x , φ x
  η : γ ∘ φ ∼ id
  η = refl
  ε : φ ∘ γ ∼ id
  ε = refl

Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ = (NatΣ f , invertibles-are-equivs (NatΣ f) (NatΣ g , H , E))
 where
  f : (x : X) → A x → B x
  f x = Eq-to-fun (φ x)
  g : (x : X) → B x → A x
  g x = inverse (f x) (Eq-to-fun-is-equiv (φ x))
  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inverse-is-retraction (f x) (Eq-to-fun-is-equiv (φ x))
  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inverse-is-section (f x) (Eq-to-fun-is-equiv (φ x))

  H : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  H (x , a) = x , g x (f x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
              x , a           ∎

  E : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  E (x , b) = x , f x (g x b) ≡⟨ ap (λ - → x , -) (ε x b) ⟩
              x , b           ∎

⁻¹-≃ x y = (_⁻¹ , invertibles-are-equivs _⁻¹ (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive))

singleton-types-≃ x = Σ-cong (λ y → ⁻¹-≃ x y)

singleton-types-are-singletons' x = equiv-to-singleton
                                      (singleton-type' x)
                                      (singleton-type x)
                                      (singleton-types-≃ x)
                                      (singleton-types-are-singletons x)

singletons-equivalent X Y i j = f , invertibles-are-equivs f (g , η , ε)
 where
  f : X → Y
  f x = center Y j
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε = centrality Y j

maps-of-singletons-are-equivs X Y f i j = invertibles-are-equivs f (g , η , ε)
 where
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε y = singletons-are-subsingletons Y j (f (g y)) y


NatΣ-fiber-equiv A B φ x b = (f , invertibles-are-equivs f (g , ε , η))
 where
  f : fiber (φ x) b → fiber (NatΣ φ) (x , b)
  f (a , refl _) = ((x , a) , refl (x , φ x a))
  g : fiber (NatΣ φ) (x , b) → fiber (φ x) b
  g ((x , a) , refl _) = (a , refl (φ x a))
  ε : (w : fiber (φ x) b) → g (f w) ≡ w
  ε (a , refl _) = refl (a , refl (φ x a))
  η : (t : fiber (NatΣ φ) (x , b)) → f (g t) ≡ t
  η ((x , a) , refl _) = refl ((x , a) , refl (NatΣ φ (x , a)))

NatΣ-equiv-gives-fiberwise-equiv A B φ e x b = γ
 where
  γ : is-singleton (fiber (φ x) b)
  γ = equiv-to-singleton
         (fiber (φ x) b)
         (fiber (NatΣ φ) (x , b))
         (NatΣ-fiber-equiv A B φ x b)
         (e (x , b))

\end{code}

--------------
More Exercises
--------------

Possible exercises: formulate and prove that the function type of
sequences of natural numbers (ℕ → ℕ) is uncountable, using Cantor's
diagonal argument.

---------------------------------
Operator fixities and precedences
---------------------------------

\begin{code}

infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infix  3  _⁻¹
infix  1 _∎
infixr 0 _≡⟨_⟩_
infixl 2 _∙_
infix  4  _∼_
infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_
infix  0 _≃_
infix  1 _■
infixr 0 _≃⟨_⟩_
infixl 2 _●_

\end{code}
