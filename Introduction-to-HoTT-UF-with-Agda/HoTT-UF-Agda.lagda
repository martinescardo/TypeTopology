---
layout: default
title : Introduction to Univalent Foundations of mathematics with Agda
date : 2019-03-04
---

## <a name="lecturenotes">Introduction to Univalent Foundations of mathematics with Agda</a>

4th March 2019, draft version of {{ "now" | date: "%d %B %Y" }}.

[Martín Hötzel Escardó](http://www.cs.bham.ac.uk/~mhe/), University of Birmingham, UK.

**Abstract.** We introduce [Voevodsky](http://www.math.ias.edu/Voevodsky/)'s [univalent foundations](http://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/) and
[univalent mathematics](https://github.com/UniMath/UniMath/blob/master/README.md), and explain how to develop them with the
computer system [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), which based on [Martin-Löf type theory](https://github.com/michaelt/martin-lof).

Agda allows one to write mathematical definitions, constructions,
theorems and proofs, for example in number theory, analysis, group
theory, topology, category theory or programming language theory, checking
them for logical and mathematical correctness.

Agda is a constructive mathematical system by default, which amounts
to saying that it can also be considered as a programming
language. But we can postulate the axiom of choice or the principle of
excluded middle for pieces of mathematics that require them, at the
cost of losing the implicit programming-language character of
Agda. For a fully constructive development of univalent mathematics,
we would need to use [Cubical
Agda](https://homotopytypetheory.org/2018/12/06/cubical-agda/)
instead, and we hope these notes provide the base for researchers
interested in learning Cubical Type Theory and Cubical Agda as the
next step.

**Keywords.** Univalent mathematics. Univalent foundations. Univalent
  type theory. Univalence axiom. `∞`-Groupoid. Homotopy type. Type
  theory. Homotopy type theory. Intensional Martin-Löf type
  theory. Dependent type theory. Identity type. Type
  universe. Constructive mathematics. Agda. Cubical type
  theory. Cubical Agda. Computer-verified mathematics.

**About this document.** This is a so-called *literate* Agda file,
with the formal, verified, mathematical development within *code*
environments, and the usual mathematical discussion outside them. Most
of this file is not Agda code, and is in markdown format, and the html
web page is generated automatically from it using Agda and other
tools. [Github](https://github.com/) pull requests by students to fix
typos or mistakes and clarify ambiguities are welcome.

These notes were originally developed for the
[Midlands Graduate School 2019](http://events.cs.bham.ac.uk/mgs2019/).

[Table of contents ⇓](#contents)
### <a name="introduction"></a> Introduction

A univalent type theory is the underlying formal system for a
foundation for univalent mathematics as conceived by [Voevodsky](http://www.math.ias.edu/Voevodsky/).

In the same way as there isn't just one set theory (we have e.g. [ZFC](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)
and [NBG](https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory) among others), there isn't just one univalent type theory (we
have e.g. the underlying type theory used in [UniMath](https://github.com/UniMath/UniMath), [HoTT-book type
theory](https://homotopytypetheory.org/2015/01/07/the-hott-book-does-not-define-hott/), and [cubical type theory](https://arxiv.org/abs/1611.02108), among others, and more are expected
to come in the foreseeable future before the foundations of univalent
mathematics stabilize).

The salient differences between univalent mathematics and traditional,
set-based mathematics may be shocking at firt sight:

 1. The kinds of objects we take as basic.

    - Certain things called types, or higher-groupoids, rather than sets, are the primitive objects.
    - Sets, also called 0-groupoids, are particular kinds of types.
    - So we have more general objects as a starting point.
    - E.g. the type `ℕ` of natural numbers is a set, and this is a theorem, not a definition.
    - E.g. the type of monoids is not a set, but instead a 1-groupoid, automatically.
    - E.g. the type of categories is a `2`-groupoid, again automatically.

 2. The treatment of logic.

    - Mathematical statements are interpreted as types rather than truth values.
    - Truth values are particular kinds of types, called `-1`-groupoids, with at most one element.
    - Logical operations are particular cases of mathematical operations on types.
    - The mathematics comes first, with logic as a derived concept.
    - E.g. when we say "and", we are taking the cartesian product of two types, which may or may not be be truth values.

 3. The treatment of equality.

    - The value of an equality `x ≡ y` is a type, called the *identity type*, which is not necessarily a truth value.
    - It collects the ways in which the mathematical objects x and y are identified.
    - E.g. it is a truth value for elements of `ℕ`, as there is at most one way for two natural numbers to be equal.
    - E.g. for the type of monoids, it is a set, amounting to the type of monoid isomorphisms, automatically.
    - E.g. for the type of categories, it is a `1`-groupoid, amounting to the type of equivalences of categories, again automatically.

The important word in the above description of univalent foundations
is *automatic*. For example, we don't *define* equality of monoids to
be isomorphism. Instead, we define the collection of monoids as the
(large) type of (small) types that are sets, equipped with a binary
multiplication operation and a unit satisfying associativity of
multiplication and neutrality of the unit in the usual way, and then
we *prove* that the native notion of equality that comes with
univalent type theory (inherited from Martin-Löf type theory) happens
to coincide with monoid isomorphism. Largeness and smallness are taken
as relative concepts, with type *universes* incorporated in the theory
to account for this distinction.

Voevodsky's way to achive this is to start with a Martin-Löf type
theory (`MLTT`), including identity types and type universes, and
postulate a single axiom, named *univalence*. This axiom stipulates a
canonical bijection between *type equivalences* (in a suitable sense
defined by Voevodsky in type theory) and type identifications (in the
original sense of Martin-Löf's identity type). Voevodsky's notion of
type equivalence, formulated in `MLTT`, is a refinement of the notion
of isomorphism, which works uniformly for all higher groupoids,
i.e. types.

In particular, Voevodsky didn't design a new type theory, but instead
gave an axiom for an existing type theory (or any of a family of
possible type theories, to be more precise).

The main *technical* contributions in type theory by Voevodsky are:

<ol type="i">
   <li>The definition of type levels in MLTT, classifying them as n-groupoids including the possibility n=∞.</li>
   <li>The (simple and elegant) definition of type equivalence that works uniformly for all type levels in MLTT.</li>
   <li> The formulation of the univalence axiom in MLTT.</li>
</ol>

Univalent mathematics begins within `MLTT` with (i) and (ii) before we
postulate univalence. In fact, as the reader will see, we will do a
fair amount of univalent mathematics before we formulate or assume the
univalence axiom.

All of (i)-(iii) crucially rely on Martin-Löf's
identity type. [Initially](http://math.ucr.edu/home/baez/Voevodsky_note.ps), Voevodsky thought that a new concept would
be needed in the type theory to achieve (i)-(iii) and hence (1) and
(3) above. But he eventually discovered that Martin-Löf's identity
type is precisely what he needed.

It may be considered somewhat miraculous that the addition of the
univalence axiom alone to `MLTT` can achieve (1) and (3). Martin-Löf
type theory was designed to achieve (2), and, regarding (1), types
were imagined/conceived as sets (and even named *sets* in some of the
original expositions by Martin-Löf), and the identity type was
imagined/conceived as having at most one element, even if `MLTT`
cannot prove or disprove this statement, as was eventually shown by
[Hofmann](https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann) and [Streicher](https://en.wikipedia.org/wiki/Thomas_Streicher) with their [groupoid model of types](https://ieeexplore.ieee.org/document/316071) in the early
1990's.

Another important aspect of univalent mathematics is the presence of
explicit mechanisms for distinguishing

<ol type="a">
 <li>property (e.g. an unspecified thing exists),</li>
 <li>data or structure (e.g. a designated thing exists or is given),</li>
</ol>

which are common place in current mathematical practice
(e.g. cartesian closedness of a category is a property in some sense
(up to isomorphism), whereas monoidal closedness is given structure).

In summary, univalent mathematics is characterized by (1)-(3),
(i)-(iii) and (a)-(b) above, and not by the univalence axiom
alone. In fact, 3/4 of theses notes begin *without* the univalence
axiom (as measured by the number of lines in the source code for these
lecture notes until we formulate the univalence axiom and start to use
it).

Lastly, univalent type theories don't assume the axiom of choice or
the principle of excluded middle, and so in some sense they are
constructive by default. But we emphasize that these two axioms are
constistent and hence can be safely used as assumptions. However,
virtually all theorems of univalent mathematics, e.g. in UniMath, have
been proved without assuming them, with natural mathematical
arguments. The formulation of theses principles in univalent
mathematics differs from their traditional formulations in MLTT, and
hence we sometimes refer to them as the *univalent* principle of
excluded middle and the *univalent* axiom of choice.

In these notes we will explore the above ideas, using Agda to write
`MLTT` definitions, constructions, theorems and proofs, with
univalence as an explicit assumption eaxch time it is needed. We will
have a further assumption, the existence of certain subsingleton (or
propositional, or truth-value) truncations in order to be able to deal
with the distinction between property and data, and in particular with
the distinction between designated and unspecified existence (for
example to be able to define the notions of image of a function and of
surjective function). However, we will not assume them globally, so
that the students can see clearly when univalence or truncation are or
are not needed. In fact, the foundational definitions, constructions,
theorems and proofs of univalent mathematics don't require univalence
or propositional truncation, and so can be developed in a version of
the original Martin-Löf type theories, and this is what happens in
these notes, and what Voevodsky did in his brilliant [original
development in computer system
Coq](https://github.com/UniMath/Foundations). Our use of Agda, rather
than Coq, is a personal matter of taste only, and the students are
encouraged to learn Coq, too.

[Table of contents ⇓](#contents)
#### <a name="homotopytypetheory"></a> Homotopy type theory

Univalent type theory is often called *homotopy type theory*.  Here we
are following Voevodsky, who coined the phrases *univalent
foundations* and *univalement mathematics*.
We regard the terminology *homotopy type theory* as probably more
appropriate for referring to the *synthetic* development of homotopy
theory within univalent mathematics, for which we refer the reader to
the [HoTT book](https://homotopytypetheory.org/book/).

However, the terminlogy *homotopy type theory* is also used as a
synonym for univalent type theory, not only because univalent type
theory has a model in homotopy types (as defined in homotopy theory),
but also because, without considering models, types do behave like
homotopy types, automatically. We will not discuss how to do homotopy
theory using univalent type theory in these notes. We refer the reader
to the HoTT book as a starting point.

[Table of contents ⇓](#contents)
#### <a name="generalreferences"></a> General references

   - [Papers](https://github.com/michaelt/martin-lof) by [Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f).
   - Homotopy type theory website [references](https://homotopytypetheory.org/references/).
   - [HoTT book](https://homotopytypetheory.org/book/).
   - `ncatlab` [references](https://ncatlab.org/nlab/show/homotopy+type+theory#References).

It particular, it is recommended to read the concluding notes for each
chapter in the HoTT book for discussion of original sources. Moreover,
the whole HoTT book is a recommended complementary reading for this
course.

And, after the reader has gained enough experience:

   - Voevodsky's original [foundations of univalent mathematics in Coq](https://github.com/vladimirias/Foundations).
   - [UniMath project](https://github.com/UniMath/UniMath) in [Coq](https://coq.inria.fr/).
   - [Coq HoTT library](https://github.com/HoTT/HoTT).
   - [Agda HoTT library](https://github.com/HoTT/HoTT-Agda).

Regarding the computer language Agda, we recommend the following as
starting points:

   - [Agda wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php).
   - [Agda reference manual](https://agda.readthedocs.io/en/latest/getting-started/index.html).
   - Agda [furher references](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation).
   - [Cubical Agda blog post](https://homotopytypetheory.org/2018/12/06/cubical-agda/).
   - [Cubical Agda documentation](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical).

We have based these lecture notes
on the slides of our talk [*logic in univalent type theory*](https://www.newton.ac.uk/seminar/20170711100011001>).

[<sub>Table of contents ⇓</sub>](#contents)
### <a name="plan"></a> Choice of material

This is intended as an introductory graduate course. We include what
we regard as the essence of univalent foundations and univalent
mathematics, but we are certainly ommiting important material that is
needed to do univalent mathematics in practice, and the readers wish
to practice univalent mathematics should consult the above references.

### <a name="contents"></a> Table of contents

  1. [Front matter](#lecturenotes)
     1. [Lecture Notes in Univalent mathematics with Agda](#lecturenotes)
     1. [Introduction](#introduction)
     1. [Homotopy type theory](#homotopytypetheory)
     1. [General references](#generalreferences)
     1. [Choice of material](#plan)
     1. [Table of contents](#contents)
  1. [MLTT in Agda](#mlttinagda)
     1. [A spartan Martin-Löf type theory (MLTT)](#spartanmltt)
     1. [What is Agda?](#whatisagda)
     1. [Getting started with Agda](#gettingstartedagda)
     1. [Universes `𝓤,𝓥,𝓦`](#universes)
     1. [The one-element type `𝟙`](#onepointtype)
     1. [The empty type `𝟘`](#emptytype)
     1. [The type `ℕ` of natural numbers](#naturalnumbers)
     1. [The binary sum type constructor `_+_`](#binarysum)
     1. [`Σ`-types](#sigmatypes)
     1. [`Π`-types](#pitypes)
     1. [The identity type former `Id`, also written `_≡_`](#identitytype)
     1. [Basic constructions with the identity type](#basicidentity)
     1. [Proofs involving negation](#negation)
     1. [Example: formulation of the twin-prime conjecture](#twinprime)
  1. [Univalent Mathematics in Agda](#uminagda)
     1. [Our univalent type theory](#axiomaticutt)
     1. [Subsingletons (or propositions or truth values) and sets](#subsingletonsandsets)
     1. [Example: the types of magmas and monoids](#magmasandmonoids)
     1. [The identity type in univalent mathematics](#identitytypeuf)
     1. [Identifications that depend on identifications](#dependentequality)
     1. [Equality in Σ-types](#sigmaequality)
     1. [Voevodsky's notion of hlevel](#hlevel)
     1. [The univalent principle of excluded middle](#em)
     1. [Hedberg's Theorem](#hedberg)
     1. [A characterization of sets](#setscharacterization)
     1. [Subsingletons are sets](#subsingletonsaresets)
     1. [The types of hlevel 1 are the subsingletons](#hlevel1subsingleton)
     1. [The types of hlevel 2 are the sets](#hlevel2set)
     1. [The hlevels are upper closed](#hlevelsupper)
     1. [Example: ℕ is a set](#naturalsset)
     1. [Natural transformations](#naturaltranformations)
     1. [Retracts](#retracts)
     1. [Voevodsky' notion of equivalence](#fibersandequivalences)
     1. [Voevodsky's univalence axiom](#univalence)
     1. [Example of a type that is not a set under univalence](#notsets)
     1. [Facts left to the reader](#lefttothereader)
     1. [Function extensionality from univalence](#funextfromua)
     1. [Variations of function extensionality and their equivalence](#hfunext)
     1. [The univalence axiom is a (sub)singleton type](#univalencesubsingleton)
     1. [`hfunext` and `vvfunext` are subsingletons](#hfunextsubsingleton)
     1. [More applications of function extensionality](#morefunextuses)
     1. [Propositional extensionality](#propext)
     1. [The axiom of choice](#choice)
     1. [The univalent axiom of choice](#axiomsofchoice)
     1. [Subsingleton truncation](#truncation)
     1. [Structure of identity principle](#sip)
     1. [Solutions to the facts left to the reader](#solutions)
  1. [Appendix](#appendix)
     1. [Additional exercises](#moreexercises)
     1. [Operator fixities and precedences](#infix)
     1. [How to generate the html file from the Agda source of these notes](#howtogen)
     1. [Solution to additional exercises](#mlttexercisessol)


When the contents of this file become more or less stable, we may
split it into smaller files. This is a pressing practical issue, as
currrenly this file takes 8s to be verified for correctness, which
makes it impractical for interactive development, and in particular
for the students to attemmpt the solutions to the exercises.

[<sub>Table of contents ⇑</sub>](#contents)
## <a name="mlttinagda"></a> MLTT in Agda

### <a name="whatisagda"></a> What is Agda?

There are [two views](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html):

 1. Agda is a dependently-typed functional programming language.

 2. Agda is a language for defining mathematical notions (e.g. group
    or topological space), formulating constructions to be performed
    (e.g. a type of real numbers, a group structure on the integers, a
    topology on the reals), formulating theorems (e.g. a certain
    construction is indeed a group structure, there are infinitely
    many primes), and proving theorems (e.g. the infinitude of the
    collection of primes with Euclid's argument).

This doesn't mean that Agda has two sets of features, one for (1) and
the other for (2). The same set of features account simultaneously for
(1) and (2). Programs are mathematical constructions that happen not
to use non-constructive principles such as excluded middle.

In these notes we study a minimal univalent type theory and do
mathematics with it using a minimal subset of the computer language Agda
as a vehicle.

Agda allows one to construct proofs interactively, but we will not
discuss how to do this in these notes. Agda is not an automatic
theorem prover. We have to come up with our own proofs, which Agda
checks for correctness. We do get some form of interactive help to
input our proofs and render them as formal objects.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="spartanmltt"></a> A spartan Martin-Löf type theory (MLTT)

Before embarking into a full definition of our Martin-Löf type
theory in Agda, we summarize the particular Martin-Löf type
theory that we will consider, by naming the concepts that we will
include. We will have:

   * An empty type [`𝟘`](#emptytype).
   * A one-element type [`𝟙`](#onepointtype).
   * A type of [`ℕ`](#naturalnumbers) natural numbers.
   * Type formers [`+`](#binarysum) (binary sum), [`Π`](#pitypes) (product), [`Σ`](#sigmatypes) (sum), [`Id`](#identitytype) (identity type).
   * [Universes](#universes) (types of types), ranged over by `𝓤,𝓥,𝓦`.

This is enough to do number theory, analysis, group theory, topology, category theory and more.

spartan
  /ˈspɑːt(ə)n/
  adjective:

      showing or characterized by austerity or a lack of comfort or
      luxury.

We will also be rather spartan with the subset of Agda that we choose
to discuss. Many things we do here can be written in more concise ways
using more advanced features. Here we introduce a minimal
subset of Agda where everything in our spartan `MLTT` can be expressed.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="gettingstartedagda"></a> Getting started with Agda

We don't use any Agda library. For pedagogical purposes, we start from
scratch, and here is our first line of code:

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where
\end{code}

 * The option `--without-K` disables [Streicher's `K` axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29), which we don't
   want for univalent mathematics.

 * The option `--exact-split` makes Agda to only accept definitions with
   the equality sign "`=`" that [behave like so-called judgmental equalities](https://agda.readthedocs.io/en/latest/language/function-definitions.html#case-trees).

 * The option `--safe` disables features [that may make Agda inconsistent](https://agda.readthedocs.io/en/latest/language/safe-agda.html#safe-agda),
   such as `--type-in-type`, postulates and more.

 * Every Agda file is a [module](https://agda.readthedocs.io/en/latest/language/module-system.html). These lecture notes are an Agda file,
   which is converted to html by Agda after it successfully checks the
   mathematical development for correctness.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="universes"></a> Universes

A universe `𝓤` is a type of types.

 * One use of universes is to define families of types indexed by a
   type `X` as functions `X → 𝓤`.

 * Such a function is sometimes seen as a property of elements of `X.

 * An other use of universes, as we shall see, is to define types of
   mathematical structures, such as [monoids](#magmasandmonoids), groups, topological spaces,
   categories etc.

Sometimes we need more than one universe. For example, the type of
groups in a universe lives in a bigger universe, and given a category
in one universe, its presheaf category also lives in a larger universe.

We will work with a tower of type universes

   > `𝓤₀, 𝓤₁, 𝓤₂, 𝓤₃, ...`

These are actually universe names (also called levels). We reference
the universes themselves by a deliberately almost-invisible
superscript dot. For example, we will have

   > `𝟙 : 𝓤₀ ̇`

where `𝟙` is the one-point type to be defined shortly. We will sometimes
omit this superscript in our discussions, but are forced to write it
in Agda code. We have that the universe `𝓤₀` is a type in the universe
`𝓤₁`, which is a type in the universe 𝓤₂ and so on.

   > `𝓤₀ ̇` &nbsp;&nbsp;    `: 𝓤₁ ̇`

   > `𝓤₁ ̇` &nbsp;&nbsp;    `: 𝓤₂ ̇`

   > `𝓤₂ ̇` &nbsp;&nbsp;    `: 𝓤₃ ̇`

   > `       ⋮ `

The assumption that
`𝓤₀ : 𝓤₀` or that any universe is in itself or a smaller universe [gives
rise to a contradiction](https://link.springer.com/article/10.1007/BF01995104), similar to [Russell's Paradox](https://plato.stanford.edu/entries/russell-paradox/).

The least upper bound of two
universes `𝓤` and `𝓥` is written

   > `𝓤 ⊔ 𝓥`.

For example, if `𝓤` is `𝓤₀` and `𝓥` is `𝓤₁`, then `𝓤 ⊔ 𝓥` is `𝓤₁`.

We now bring our notation for universes by importing our Agda file
`Universes`. The Agda keyword
[`open`](https://agda.readthedocs.io/en/latest/language/module-system.html)
asks to make all definitions in the file `Universe` visible in our
file here. The Agda code in these notes has syntax highlighting and
html links, so that we can navigate to other modules, such as
`Universe` or to definitions in this file.

\begin{code}
open import Universes
\end{code}

We will refer to universes by letters `𝓤,𝓥,𝓦,𝓣`:

\begin{code}
variable
 𝓤 𝓥 𝓦 𝓣 : Universe
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="onepointtype"></a> The one-element type `𝟙`

We place it in the first universe, and we name its unique element
"`⋆`". We use the `data` declaration in Agda to introduce it:

\begin{code}
data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙
\end{code}

It is important that the point `⋆` lives in the type `𝟙` and in no other
type. There isn't dual citizenship in our type theory. When we create
a type, we also create freshly new elements for it, in this case
"`⋆`". (However, Agda has a limited form of overloading, which allows
one to sometimes use the same name for different things.)

Next we want to give a mechanism to prove that all points of the
type `𝟙` satify a given property `A`.

  * The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`.

  * The type `A(x)`, which we will write simply `A x`, doesn't
    need to be a [truth value](#subsingletonsandsets).  It can be any
    type. We will meet examples shortly.

  * Mathematical statements are types, such as

    > `Π (A : 𝟙 → 𝓤), A ⋆ → Π (x : 𝟙), A x`.

  * We read this in natural language as "for any given property `A` of
    elements of the type `𝟙`, if we can show that `A ⋆` holds, then it
    follows that `A x` holds for all `x : 𝟙`".


  * In Agda above `Π`-type is written as

    > `(A : 𝟙 → 𝓤 ̇ ) → A * → (x : 𝟙) → A x`.

    This is the type of functions with three arguments `A : 𝟙 → 𝓤 ̇` &nbsp;
    and `a : A ⋆` and `x : 𝟙`, with value in the type `A x`.

  * A proof of a mathematical statement rendered as a type is a
    construction of an element of the type.  In our example, we have
    to construct a function, which we will name `𝟙-induction`.

We do this as follows in Agda, where we first declare the type of the
function `𝟙-induction` with "`:`" and then define the function by an
equation:

\begin{code}
𝟙-induction : (A : 𝟙 → 𝓤 ̇ )
            → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
\end{code}

Notice that we supply `A` and `a` as arbitrary arguments, but instead of
an arbitrary `x : X` we have written "`⋆`". Agda accepts this because it
knows from the definition of `𝟙` that "`⋆`" is the only element of the
type `𝟙`. This mechanism is called *pattern matching*.

A particular case of `𝟙-induction` occurs when the family `A` is constant
with value `B`, which can be written as variously as `A = λ (x : 𝟙) → B`,
or `A = λ x → B` if we want Agda to figure out the type of `x` by itself,
or `A = λ _ → B` if we don't want to name the argument of `A` because it
is not used. In usual mathematical practice, such a [lambda expression](https://plato.stanford.edu/entries/lambda-calculus/) is [often
written](https://en.wikipedia.org/wiki/Function_(mathematics)#Arrow_notation) `x ↦ B` (`x` is mapped to `B`) and so `A = (x ↦ B)`.
Given a type `B` and a point `b : B`, we construct the function `𝟙 → B`
that maps any given `x : 𝟙` to `b`.

\begin{code}
𝟙-induction' : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-induction' B b x = 𝟙-induction (λ _ → B) b x
\end{code}

Not all types have to be seen as mathematical statements (for example
the type `ℕ` of natural numbers defined below). But the above definition
has a dual interpretation as a mathematical function, and as the
statement "`B` implies (*true* implies `B`)" where `𝟙` is the type encoding
the truth value *true*.

We will not use this induction principle directly, as we can
prove properties of `𝟙` by pattern matching on `⋆ : 𝟙`, just as we defined the
induction principle.

The unique function to `𝟙` will be named `!𝟙`. We define two versions
to illustrate [implicit
arguments](https://agda.readthedocs.io/en/language/implicit-arguments.html)
which correspond in mathematics to "subscripts that are omitted when
the reader can safely infer them", as for example for the identity
function of a set or the identity arrow of an object of a category.

\begin{code}
!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆
\end{code}

This means that when we write `!𝟙 x` we have to recover the (uniquely
determined) missing type `X` with `x : X` "from the context". When
Agda can't figure it out, we need to supply it and write `!𝟙 {𝓤} {X}
x`. This is because `𝓤` is also an implicit argument (all things
declared with the Agda keyword *variable* as above are implicit
arguments). There are
[other](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html),
non-positional, ways to indicate `X` without having to indicate `𝓤`
too. Occasionally, people define variants of a function with different
choices of "implicitness", as above.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="emptytype"></a> The empty type `𝟘`

It is defined like `𝟙`, except that no elements are listed for it:

\begin{code}
data 𝟘 : 𝓤₀ ̇  where
\end{code}

That's the complete definition. This has a dual interpretation,
mathematically as the empty set (we can actually prove that this type
is a set, once we know the definition of set - **exercise**), and
logically as the truth-value *false*. To prove that a property of
elements of the empty type holds for all elements of the empty type we
have to do nothing.

\begin{code}
𝟘-induction : (A : 𝟘 → 𝓤 ̇ )
            → (x : 𝟘) → A x
𝟘-induction A ()
\end{code}

When we write the pattern `()`, Agda checks if there is any case we
missed. If there is none, our definition is accepted.  The expression
`()` corresponds to the mathematical phrase [vacuously
true](https://en.wikipedia.org/wiki/Vacuous_truth). The unique
function from `𝟘` to any type is a particular case of `𝟘`-induction.

\begin{code}
!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 A a = 𝟘-induction (λ _ → A) a
\end{code}

We give the two names `is-empty` and `¬` to the same function now:

\begin{code}
is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘
\end{code}

This says that a type is empty precisely when we have a function to
the empty type. Assuming [univalence](#univalence), once we have
defined equality type former [`_≡_`](#identitytype), we will be able
to prove that `(is-empty X) ≡ (X ≡ 𝟘)`. We will also be able to prove
things like `(2 + 2 ≡ 5) ≡ 𝟘` and `(2 + 2 ≡ 4) ≡ 𝟙`.

This is for
*numbers*. If we define *types* `𝟚 = 𝟙 + 𝟙` and `𝟜 = 𝟚 + 𝟚` with two
and four elements respectively, where we are anticipating the
definition of [`_+_`](#binarysum) for types, then we will instead have
that `𝟚 + 𝟚 ≡ 𝟜` is a type with `4!` elements, which is [number of
permutations](https://en.wikipedia.org/wiki/Factorial) of a set with
four elements, rather than a truth value `𝟘` or `𝟙`, as a consequence
of the univalence axiom. That is, we will have `(𝟚 + 𝟚 ≡ 𝟜) ≡ (𝟜 + 𝟜 +
𝟜 + 𝟜 + 𝟜 + 𝟜)`, so that the type equality `𝟚 + 𝟚 ≡ 𝟜` holds in [many
more
ways](https://arxiv.org/abs/math/9802029)
than the numerical equation `2 + 2 ≡ 4`.

The above is possible only because universes are genuine types and
hence their elements (that is, types) have identity types themselves,
so that writing `X ≡ Y` for types `X` and `Y` (inhabiting the same
universe) is allowed.


When we view `𝟘` as *false*, we can read the definition of
the *negation* `¬ X` as saying that "`X` implies *false*". With univalence
we will be able to show that "(*false* → *false*) `≡` *true*", which amounts
to `(𝟘 → 𝟘) ≡ 𝟙`, which in turn says that there is precisely one function
`𝟘 → 𝟘`, namely the (vacuous) identity function.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="naturalnumbers"></a> The type `ℕ` of natural numbers

The definition is similar but not quite the same as the one via
[Peano Axioms](https://en.wikipedia.org/wiki/Peano_axioms).

We stipulate an element `zero : ℕ` and a successor function `ℕ → ℕ`, and
then define induction. Once we have defined equality `_≡_`, we will
[*prove*](#naturalsset) the other peano axioms.

\begin{code}
data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ
\end{code}

In general, declarations with `data` are inductive definitions. To write the number `5`, we have to write

   > `succ (succ (succ (succ (succ zero))))`

We can use the following Agda
[*pragma*](https://agda.readthedocs.io/en/latest/language/pragmas.html)
to be able to just write `5` as a shorthand:

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Apart from this notational effect, the above pragma doesn't play any
role in the Agda development of these lectures notes.

In the following, the type family `A` can be seen as playing the role
of a property of elements of `ℕ`, except that it doesn't need to be
necessarily [subsingleton](#subsingletonsandsets)-valued. When it is, the *type* of the function gives
the familiar [principle of mathematical induction](https://en.wikipedia.org/wiki/Mathematical_induction) for natural numbers, whereas, in general, its definition says how to compute with induction.

\begin{code}
ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)
\end{code}

The definition of `ℕ-induction` is itself by induction. It says that given a point `a₀ : A 0` and a function `f : (n : ℕ) → A n → A (succ n)`, in order to calculate an element of `A n` for a given `n : ℕ`, we just calculate `h n`, that is,

   > `f n (f (n-1) (f (n-2) (... (f 0 a₀)...)))`.

So the principle of induction is a construction that given a *base
case* `a₀ : A 0`, an *induction step* `f : (n : ℕ) → A n → A (succ n)` and a number `n`, says how to get
an element of the type `A n` by [primitive
recursion](https://www.encyclopediaofmath.org/index.php/Primitive_recursion).

Notice also that ℕ-induction is the dependently typed version of
primitive recursion, where the non-dependently type version is

\begin{code}
ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)
\end{code}

The following special case occurs often (and is related to the fact that `ℕ` is the [initial algebra](https://en.wikipedia.org/wiki/Initial_algebra) of the functor `𝟙 + (-)`):

\begin{code}
ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration A a f = ℕ-recursion A a (λ _ a → f a)
\end{code}

Agda checks that any recursive definition as above is well founded,
with recursive invokations with structurally smaller arguments
only. If it isn't, the definition is not accepted.

In official Martin-Löf type theories, we have to use the `ℕ-induction`
functional to define everything else with the natural numbers. But Agda
allows us to define functions by structural recursion, like we defined
`ℕ-induction`.


We now define addition and multiplication for the sake of illustration.
We first do it in Peano style. We will create a local [`module`](https://agda.readthedocs.io/en/latest/language/module-system.html#) so that the
definitions are not globally visible, as we want to have the symbols
`+` and `×` free for type operations of `MLTT` to be defined soon. The
things in the module are indented and are visible outside the module
only if we [`open`](https://agda.readthedocs.io/en/latest/language/module-system.html#) the module or if we write them as
e.g. `Arithmetic.+` in the following example.

\begin{code}
module Arithmetic where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 0 _+_
  infixl 1 _×_
\end{code}

The above `infix` operations allow us to indicate the precedences
(multiplication has higher precedence than addition) and their
associativity (here we take left-associativity as the convention, so that
e.g. `x+y+z` parses as `(x+y)+z`, but of course this doesn't matter as
both operations are
[associative](https://en.wikipedia.org/wiki/Associative_property)).

Equivalent definitions use `ℕ-induction` on the second argument `y`, via
`ℕ-iteration`:

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
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 0 _+_
  infixl 1 _×_
\end{code}

Here the expression "`x +_`" stands for the function `ℕ → ℕ` that adds
`x` to its argument. So to multiply `x` by `y`, we apply `y` times the
function "`x +_`" to `0`.

As another example, we define the less-than-or-equal relation by
nested induction, on the first argument and then the second, but we
use patern matching for the sake of readability.

*Exercise.* Write it using `ℕ-induction`, recursion or iteration, as
appropriate.

\begin{code}
module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x
\end{code}

*Exercise.* After you have learned [`Σ`](#sigmatypes) and
  [`_≡_`](#identitytype) explained below, prove that

   > `x ≤ y` if and only if `Σ \(z : ℕ) → x + z ≡ y`.

Later, when you have learned [univalence](#univalence) prove that in this case this implies

   > `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

That bi-implication can be turned into equality only holds for types
that are [subsingletons](#subsingletonsandsets).


If we are doing applied mathematics and want to actually compute, we
can define a type for binary notation, and of course people have done
that. Here we are not concerned with efficiency but only with
understanding how to codify mathematics in (univalent) type theory and
in Agda.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="binarysum"></a> The binary sum type constructor `_+_`

We now define the disjoint sum of two types `X` and `Y`. The elements of
the type

   > `X + Y`

are stipulated to be of the forms

   > `inl x` and `inr y`

for `x : X` and `y : Y`. If `X : 𝓤` and `Y : 𝓥`, we stipulate that
`X + Y : 𝓤 ⊔ 𝓥 `, where

   > `𝓤 ⊔ 𝓥 `

is the [least upper bound](#universes) of the two universes `𝓤` and
`𝓥`.  In Agda we can define this as follows.

\begin{code}
data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y
\end{code}

To prove that a property `A` of the sum holds for all `z : X + Y`, it is enough to
prove that `A(inl x)` holds for all `x : X` and that `A(inr y)` holds for
all `y : Y`. This amounts to definition by cases:

\begin{code}
+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y
\end{code}

When the types `A` and `B` are understood as mathematical statements,
the type `A + B` is understood as the statement "`A` or `B`", because
to prove "`A` or `B`" we have to prove one of `A` and `B`. When `A` and
`B` are simultaneously possible, we have two proofs, but sometimes we
want to deliberately ignore which one we get, when we want to get a
truth value rather than a possibly more general type, and in this case
we use the [truncation](#truncation) `∥ A + B ∥`.

But also `_+_` is used to construct mathematical objects. For example,
we can define a two-point type:

\begin{code}
𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙
\end{code}

We can name the left and right points as follows, using patterns, so
that they can be used in pattern matching:

\begin{code}
pattern ₀ = inl ⋆
pattern ₁ = inr ⋆
\end{code}

We can define induction on 𝟚 directly by pattern matching:
\begin{code}
𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁
\end{code}

Or can can prove it by induction on `_+_` and `𝟙`:
\begin{code}
𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="sigmatypes"></a> `Σ`-types

Given universes `𝓤` and `𝓥`, a type

   > `X : 𝓤`

and a type family

   > `Y : X → 𝓥 `,

we want to construct its sum, which
is a type whose elements are of the form

   > `(x , y)`

with `x : X` and `y : Y x`. This sum type will live in the [least
upper bound](#universes)

   > `𝓤 ⊔ 𝓥`.

of the universes `𝓤` and `𝓥`. We will write this sum

   > `Σ Y`,

with `X`, as well as the universes, implicit. Often Agda, and people,
can figure out what the unwritten type `X` is, from the definition of `Y`. But
sometimes there may be either lack of enough information, or of
enough concentration power by people, or sufficiently powerful inference
algorithms in the implementation of Agda. In such cases we can write

   > `Σ λ(x : X) → Y x`,

because `Y = λ (x : X) → Y x` by a so-called η-rule. However, we will
often use the synonym `\` of `λ` for Σ, as if considering it as part
of the `Σ` syntax.

   > `Σ \(x : X) → Y x`.

In `MLTT` we would write this as `Σ (x : X), Y x` or
[similar](https://en.wikipedia.org/wiki/Summation), for example with
the indexing `x : X` written as a subscript of `Σ` or under it.


Or it may be that the name `Y` is not defined, and we work with a
nameless family defined on the fly, as in the exercise proposed above:

   > `Σ \(z : ℕ) → x + z ≡ y`,

where `Y z = (x + z ≡ y)` in this case, and where we haven't defined
the [identity type former](#identitytype) `_≡_` yet.

We can construct the `Σ` type former as follows in Agda:

\begin{code}
record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor _,_
  field
   x : X
   y : Y x
\end{code}

This says we are defining a binary operator `_,_` to construct the
elements of this type as `x , y`. The brackets are not needed, but we
will often write them to get the more familiar notation `(x , y)`. The
definition says that an element of `Σ Y` has two `fields`, giving the
types for them.

*Remark.* Beginners may safely ignore this remark: Normally people
will call these two fields something like `pr₁` and `pr₂`, or `fst`
and `snd`, for first and second projection), rather than `x` and `y`,
and then do `open Σ public` and have the projections available as
functions automatically. But we will deliberately not do that, and
instead define the projections ourselves, because this is confusing
for beginners, no matter how mathematically or computationally versed
they may be, in particular because it will not be immediately clear
that the projections have the following types.

\begin{code}
pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y
\end{code}

To prove that `A z` holds for all `z : Σ Y`, for a given
property `A`, we just prove that we have `A(x , y)` for all given `x :
X and for all y : Y x`.  This is called `Σ` induction or `Σ`
elimination, or `uncurry`, after [Haskell
Curry](https://en.wikipedia.org/wiki/Haskell_Curry).
\begin{code}
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A(x , y))
            → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y
\end{code}

This function has an inverse:

\begin{code}
curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
\end{code}

An important particular case of the sum type is the binary cartesian
product, when the type family doesn't depend on the indexing family:

\begin{code}
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y
\end{code}

We have seen by way of examples that the function type symbol `→`
represents logical implication, and that a dependent function type
`(x : X) → A x` represents a universal quantification.

We have the following uses of `Σ`.

  * The binary cartesian product represents conjunction "and". If the
    types `A` and `B` stand for mathematical statements, then the mathematical
    statement "`A` and `B`" is codified as `A × B`. This is because to prove
    "`A` and `B`", we have to provide a pair `(a , b)` of proofs `a : A` and `b : B`.

    So notice that in type theory, proofs are mathematical objects,
    rather than meta-mathematical entities like in set theory. They are
    just elements of types.

  * The more general type `Σ \(x : X), A x`, if the type `X` stands
    for a mathematical object and `A` stands for a mathematical
    statement, represents *designated* existence "there is a
    designated `x : X` with `A x`".  To prove this, one has to provide
    a specific `x : X` and a proof `a : A x`, together in a pair
    `(x , a)`.

  * Later we will discuss *unspecified* existence `∃ \(x : X) → A x`,
    which will be obtained by a sort of quotient of `Σ \(x : X), A
    x`, written `∥ Σ \(x : X), A x ∥` that identifies all the elements
    of the type `Σ \(x : X), A x` in a single equivalence class,
    called its propositional or subsingleton [truncation](#truncation).

  * Another reading of `Σ \(x : X), A x` is as "the type of `x : X`
    with `A x`", similar to subset notation `{ x ∈ X | A x }` in set
    theory. But have to be careful because if there is more than one
    element in the type `A x`, then `x` is put more than once in this
    type. In such situations, if we don't want that, we have to be
    careful and either ensure that the type `A x` has at most one
    element for every `x : X`, or instead consider the truncated type
    `∥ A x ∥` and write `Σ \(x : X), ∥ A x ∥`.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="pitypes"></a> `Π`-types

`Π`-types are builtin with a different notation in Agda, as discussed
above, but we can introduce the notation `Π` for them, similar to that for `Σ`:

\begin{code}
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x
\end{code}

Notice that the function type `X → Y` is the particular case of the `Π`
type when the family `A` is constant with value `Y`.

We take the opportunity to define the identity function and function
composition:

\begin{code}
id : {X : 𝓤 ̇ } → X → X
id x = x
\end{code}

Usually the type of function composition `_∘_` is given as simply

   >  `(Y → Z) → (X → Y) → (X → Z)`.

With dependent functions, we can give it a more general type:

\begin{code}
_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
\end{code}

Notice that this type for the composition function can be read as a mathematical
statement: If `Z y` holds for all `y : Y`, then for any given `f : X →
Y` we have that `Z (f x)` holds for all `x : X`. And the non-dependent
one is just the transitivity of implication.

The following functions are sometimes useful when we are using
implicit arguments, in order to recover them explicitly without having
to list them as given arguments:

\begin{code}
domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="identitytype"></a> The identity type former `Id`, also written `_≡_`

We now introduce the central type constructor of `MLTT` from the point
of view of univalent mathematics. In Agda we can define Martin-Löf's
identity type as follows:

\begin{code}
data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x
\end{code}

Intuitively, the above definition would say that the only element
of the type `Id X x x` is something called `refl x` (for
reflexivity). But, as we shall see in a moment, this intuition turns
out to be incorrect.

Notice a crucial difference with the previous definitions using `data`
or induction: In the previous cases, we defined *types*, namely `𝟘`,
`𝟙`, `ℕ` , or a *type depending on parameters*, namely `_+_` , with `𝓤`
and `𝓥` fixed,

   > `_+_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇`

But here we are defining a *type family* indexed by the *elements* of
a give type, rather than a new type from old types. Given a type `X`
in a universe `𝓤`, we define a *function*

   > `Id X : X → X → 𝓤`

by some mysterious sort of induction. It is this that prevents us from
being able to prove that `refl x` would be the only element of the type `Id
X x x`, or that for `Id X x y` would have at most one element no
matter what `y : X` is. There is however, one interesting thing we
[can prove](#retractsofsigma), namely that for any fixed `x : X`, the
type


   > `Σ \(y : Y) → Id X x y`

is always a [singleton](#hlevel).

We will use the following alternative notation for the identity type
former `Id`, where the symbol "`_`" in the right-hand side of the
definition indicates that we ask Agda to infer which type we are
talking about (which is `X`, but this name is not available in the
scope of the *definiting equation* of `_≡_`):

\begin{code}
_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y
\end{code}

Another intuition for this type family `_≡_ : X → X → 𝓤` is that it
gives the least reflexive relation on the type `X`, as indicated by
Martin-Löf's induction principle `J` discussed below.

Whereas we can make the intuition that `x ≡ x` has precisely one
element good by postulating a certain [`K`
axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) due to
Thomas Streicher, which comes with Agda by default but we have
[disabled above](#gettingstartedagda), we cannot *prove* that `refl x`
is the only element of `x ≡ x` for an arbitrary type `X`. This
non-provability result was established by [Hofmann and
Streicher](https://ieeexplore.ieee.org/document/316071), by giving a
model of type theory in which types are interpreted as
[groupoids](https://en.wikipedia.org/wiki/Groupoid).

However, for the elements of *some* types, such as `ℕ`, it is possible
to prove that any identity type `x ≡ y` has at most one element. Such
types are called [sets in univalent
mathematics](#subsingletonsandsets).

If instead of `K` we adopt Voevodsky's [univalence](#univalence)
axiom, we get [specific examples](#notsets) of objects `x` and `y`
such that the type `x ≡ y` has multiple elements, *within* the type
theory.  It follows that the identity type `x ≡ y` is fairly
under-specified in general, in that we can't prove or disprove that it
has at most one element.

There are two opposing ways to resolve the ambiguity or
underspecification of the identity types: (1) We can consider the `K`
axiom, which postulates that all types are sets, or (2) we can
consider the univalence axiom, arriving at univalent mathematics,
which gives rise to types that are more general than sets, the
`n`-gropoids and `∞`-groupoids.  In fact, the univalence axiom will
say, in particular, that for some types `X` and elements `x y : X`, the
identity type `x ≡ y` does have more than one element.

A possible way to understand the point `refl x` of the type `x ≡ x` is
as the "generic identification" between `x` and itself, but which is
by no means necessarily the *only* identitification in univalent
foundations. It is generic in the sense that to explain what happens
with all identifications `p : x ≡ y` between any two points `x` and
`y` of a type `X`, it suffices to explain what happens with the
identification `refl x : x ≡ x` for all points `x : X`. This
what the induction principle for identity given by Martin-Löf says,
which he called `J` (we could have called it `≡-induction`, but we
prefer to honour `MLTT` tradition):

\begin{code}
J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
J X A f x x (refl x) = f x
\end{code}

This is [related](http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html) to the [Yoneda
Lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) in category theory,
if you are familiar with this subject, which says that certain natural
transformations are *uniquely determined* by their *action on the
identity arrows*, even if they are *defined for all arrows*. Similarly
here, `J` is uniquely determined by its action on reflexive
identifications, but is *defined for all identifications between any
two points*, not just reflexivities.

In summary, Martin-Löf's identity type is given by the data

  * `Id`,
  * `refl`,
  * `J`,
  * The above equation for `J`.

However, we will not use this induction principle, because we can
instead work with the instances we need by pattern matching on `refl`
(which is just what we did to define the principle itself) and there
is a [theorem by Jesper
Cockx](<https://dl.acm.org/citation.cfm?id=2628139) which says that
with the Agda option `without-K`, pattern matching on `refl` can
define/prove precisely what `J` can.

*Exercise*. Define
\begin{code}
H : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b x (refl x) = b
\end{code}

Then we can define `J` from `H` as follows:

\begin{code}
J' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
J' X A f x = H x (A x) (f x)

Js-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → J X A f x y p ≡ J' X A f x y p
Js-agreement X A f x x (refl x) = refl (f x)
\end{code}

Similarly define `H'` from `J` without using pattern matching on refl
and show that it coincides with `H` (possibly using pattern maatching
on `refl`). This is
[harder](http://www.cse.chalmers.se/~coquand/singl.pdf).

**Notational remark.** The symbols "`=`" and "`≡`" are swapped with
  respect to the [HoTT Book](https://homotopytypetheory.org/book/)
  convention for definitional/judgemental equality and typed-valued equality,
  and there is nothing we can do about that because "`=`" is a
  reserved Agda symbol for definitional equality. Irrespectively of
  this, it does make sense to use "`≡`" with a triple bar, if we
  understand this as indicating that there are multiple ways of
  identifying two things in general.

With this, we have concluded the rendering of our spartan `MLTT` in
Agda notation. Before embarking on the development of univalent
mathematics within our spartan `MLTT`, we pause to discuss some
basic examples of mathematics in Martin-Löf type theory.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="basicidentity"></a> Basic constructions with the identity type

*Transport along an identification.*
\begin{code}
transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = id
\end{code}

We can equivalently define transport using `J` as follows:

\begin{code}
transportJ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportJ {𝓤} {𝓥} {X} A {x} {y} = J X (λ x y _ → A x → A y) (λ x → id) x y
\end{code}

In the same way `ℕ`-recursion can be seen as the non-dependent special
case of `ℕ`-induction, the following transport function can be seen as
the non-dependent special case of the `≡`-induction principle `H` with
some of the arguments permuted and made implicit:

\begin{code}
nondep-H : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ≡ y → A y
nondep-H {𝓤} {𝓥} {X} x A = H x (λ y _ → A y)

transportH : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportH {𝓤} {𝓥} {X} A {x} {y} p a = nondep-H x A a y p
\end{code}

All the above transports coincide:

\begin{code}
transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → (transportH A p ≡ transportH A p)
                     × (transportJ A p ≡ transportH A p)
transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))
\end{code}



The following is for use when we want to recover implicit
arguments without mentioning them.

\begin{code}
lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y
\end{code}

*Composition of identifications.*
Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them
to get an identification `p ∙ q : x ≡ y`. This can also be seen as
transitivity of equality. Because the type of composition doesn't
mention `p` and `q`, we can use the non-dependent version of `≡`-induction.

\begin{code}
_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p
\end{code}

Here we are considering the family `A t = (x ≡ t)`, and using the
identification `q` to transport `A y` to `A z`, that is `x ≡ y` to `x
≡ z`.

*Exercise.* define an alternative version that uses `p` to
transport. Can you prove that the two versions give equal results?

*Inversion of identifications.* Given an identification, we get an
  identification in the opposite direction:

\begin{code}
_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))
\end{code}

*Application of a function to an identification*.
Given an identification `p : x ≡ x'` we get an identification
`ap f p : f x ≡ f x'` for any `f : X → Y`:

\begin{code}
ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p (refl (f (lhs p)))
\end{code}

Notice that we have so far used the recursion principle `transport`
only. To reason about `transport`, `_∙_`, `_⁻¹` and `ap`, we
[will need](#identitytypeuf) to use the full induction principle `J`.

*Pointwise equality of functions*. We will work with pointwise
equality of functions, defined as follows, which, using univalence,
will be [equivalent to equality of functions](#hfunext).

\begin{code}
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → A x) → ((x : X) → A x) → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="negation"></a> Proofs involving negation

We first introduce notation for double and triple negation to avoid
the use of brackets.

\begin{code}
¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
\end{code}

To prove that `A → ¬¬ A`, that is, `A → ((A → 𝟘) → 𝟘)`, we start with
a hypothetical element `a : A` and a hypothetical function `u : A → 𝟘`
and the goal is to get an element of `𝟘`. All we need to do is to
apply the function `u` to `a`.

\begin{code}
dni : {A : 𝓤 ̇ } → A → ¬¬ A
dni a u = u a
\end{code}

The reasoning is similar for the following. We assume we are given
hypothetical `f : A → B`, `v : B → 𝟘` and `a : A` and our goal is to
get an element of `𝟘`.

\begin{code}
contrapositive : {A : 𝓤 ̇ } {B : 𝓤 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)
\end{code}

And from this we get the three negations imply one:
\begin{code}
tno : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
tno = contrapositive dni
\end{code}

We now define a symbol for the negation of identity equality.

\begin{code}
_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)
\end{code}

In the following proof, we have `u : x ≡ y → 𝟘` and need to define a
function `y ≡ x → 𝟘`. So all we need to do is to compose the function
that inverts identifications with `u`:

\begin{code}
≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)
\end{code}

To show that the type `𝟙` is not equal to the type `𝟘`, we use that
`transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 ≡ id 𝟘` where `id` is the
[identity function](#pitypes). So if we have a
hypothetical identification `p : 𝟙 ≡ 𝟘`, then we get a function `𝟙 →
𝟘`. We apply this function to `⋆ : 𝟙` to conclude the proof.

\begin{code}
𝟙-is-not-𝟘 : ¬(𝟙 ≡ 𝟘)
𝟙-is-not-𝟘 p = f p ⋆
 where
  f : 𝟙 ≡ 𝟘 → 𝟙 → 𝟘
  f = transport id
\end{code}

To show that the elements `₁` and `₀` of the two-point type `𝟚` are
not equal, we reduce to the above case. We start with a hypothetical
identification `p : ₁ ≡ ₀`.

\begin{code}
₁-is-not-₀ : ¬(₁ ≡ ₀)
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p
\end{code}

*Remark.* Agda allows us to use a pattern `()` to get the following
quick proof.  However, this method of proof doesn't belong to the
realm of MLTT.

\begin{code}
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()
\end{code}

Perhaps the following is sufficiently self-explanatory given the above:

\begin{code}
𝟚-has-decidable-equality : (m n : 𝟚) → (m ≡ n) + (m ≢ n)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)
\end{code}

So we consider four cases. In the first and the last, we have equal
things and so we give an answer in the left-hand side of the sum. In
the middle two, we give an answer in the right-hand side, where we need
functions `₀ ≡ ₁ → 𝟘` and `₁ ≡ ₀ → 𝟘`, which we can take to be `≢-sym
₁-is-not-₀` and `₁-is-not-₀` respectively.

The following is more interesting. We consider the two possible cases
for `n`. The first one assumes a hypothetical function `f : ₀ ≡ ₀ →
𝟘`, from which we get `f (refl ₀) : 𝟘`, and then, using `!𝟘`, we get
an element of any type we like, which we choose to be `₀ ≡ ₁`, and we
are done. Of course, we will never be able to call the function
`not-zero-is-one` with such outrageous inputs. The other case `n = ₁`
doesn't need to use the hypothesis `f : ₁ ≡ ₀ → 𝟘`, because the
desired conclusion holds right away, as it is `₁ ≡ ₁`, which is proved
by `refl ₁`. But notice that there is nothing wrong with the
hypothesis `f : ₁ ≡ ₀ → 𝟘`. For example, we can call `not-zero-is-one`
with `n = ₀` and `f = ₁-is-not-₀`, so that the hypothesis can be
fulfilled in the second equation.

\begin{code}
not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁
\end{code}

The following generalizes `₁-is-not-₀`, both in its statement and its
proof (so we could have formulated it first and then used it to deduce
`₁-is-not-₀`):

\begin{code}
inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 r
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘
  r : 𝟙 ≡ 𝟘
  r = ap f p
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="twinprime"></a> Example: formulation of the twin-prime conjecture

We illustrate the above constructs of `MLTT` to formulate this
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
and proofs, but also conjectures. They are just definitions of
types. Likewise, the univalence axiom, [to be formulated in due course](#univalence),
is a type.

[<sub>Table of contents ⇑</sub>](#contents)
## <a name="uminagda"></a> Univalent Mathematics in Agda

### <a name="axiomaticutt"></a> Our univalent type theory

  * Spartan `MLTT` [as above](#spartanmltt).
  * [Univalence axiom](#univalence).

But, as discussed above, rather than postulating univalence we will
use it as an explicit assumption each time it is needed.

We emphasize that there are univalent type theories in which
univalence is a theorem, for example cubical type theory, which has a
version available in Agda, called [cubical
Agda](https://homotopytypetheory.org/2018/12/06/cubical-agda/).

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="subsingletonsandsets"></a> Subsingletons (or propositions or truth values) and sets

A type is a subsingleton (or a proposition or a truth value) if it has
at most one element, that is, any two of its elements are equal, or identified.

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
is-prop        = is-subsingleton
is-truth-value = is-subsingleton
\end{code}

The terminology `is-subsingleton` is more mathematical and avoids the
clash with the slogan [propositions as
types](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence),
which is based on the interpretation of mathematical propositions as
arbitrary types, rather than just subsingletons.

A type is defined to be a set if there is at most one way for any two of its
elements to be equal:

\begin{code}
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
\end{code}

At this point, with the definition of these notions, we are entering
the realm of univalent mathematics, but not yet needing the univalence
axiom.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="magmasandmonoids"></a> Example: the types of magmas and monoids

A magma is a *set* equipped with a binary operation subject to no laws
(Bourbaki).  We can define the type of Magmas in a universe `𝓤`, which
lives in the successor universe `𝓤⁺`, as follows.

\begin{code}
Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X × (X → X → X)
\end{code}

The type `Magma 𝓤` collects all magmas in a universe `𝓤`.  Thus, this
doesn't define what a magma is as a property. It defines the type of
magmas. A magma is an element of this type.

Given a magma `M = (X , i , _·_)` we denote by `⟨ M ⟩` its underlying set `X` and by `magma-operation M` its multiplication `_·_`:

\begin{code}
⟨_⟩ : Magma 𝓤 → 𝓤 ̇
⟨ X , i , _·_ ⟩ = X

magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
magma-operation ( X , i , _·_ ) = _·_
\end{code}

The following [syntax declaration](https://agda.readthedocs.io/en/latest/language/syntax-declarations.html)
allows us to write `x ·⟨ M ⟩ y` as an abbreviation of `magma-operation M x y`:

\begin{code}
syntax magma-operation M x y = x ·⟨ M ⟩ y
\end{code}

For some reason, Agda has this kind of definition backwards: the
*definiendum* and the *definiens* are swapped with respect to the
normal convention of writing what is defined on the left-hand side of
the equality sign. In any case, the point is that this time we need
such a mechanism because in order to be able to mention arbitrary `x`
and `y`, we first need to know their types, which is `⟨ M ⟩` and hence
`M` has to occur before `x` and `y` in the definition of
`magma-operation`.

A function of the underlying sets of two magmas is a called a
homomorphism when it commutes with the magma operations:

\begin{code}
is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ·⟨ M ⟩ y) ≡ f x ·⟨ N ⟩ f y

id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M id
id-is-magma-hom M = λ (x y : ⟨ M ⟩) → refl (x ·⟨ M ⟩ y)

is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-iso M N f = is-magma-hom M N f
                   × Σ \(g : ⟨ N ⟩ → ⟨ M ⟩) → is-magma-hom N M g
                                            × (g ∘ f ∼ id)
                                            × (f ∘ g ∼ id)

id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M id
id-is-magma-iso M = id-is-magma-hom M ,
                    id ,
                    id-is-magma-hom M ,
                    refl ,
                    refl
\end{code}

Any identification of magmas gives rise to a magma isomorphism by transport:

\begin{code}
⌜_⌝ : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
⌜ p ⌝ = transport ⟨_⟩ p

⌜⌝-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (⌜ p ⌝)
⌜⌝-is-iso (refl M) = id-is-magma-iso M
\end{code}

The isomorphisms can be collected into a type:

\begin{code}
_≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
M ≅ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-iso M N f
\end{code}

The following function [will be](#sip) a bijection in the presence of
univalence, so that the identifications of magmas are in one-to-one
correspondence with the magma isomorphisms:

\begin{code}
magma-≡-to-iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
magma-≡-to-iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )
\end{code}

If we omit the set-hood condition in the definition of the type of
magmas, we get the type of what we could call `∞`-magmas (then the
type of magmas could be called `1-Magma`).

\begin{code}
∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → X → X → X
\end{code}

A monoid is a set equipped with an associative binary operation and
with a two-sided neutral element, and so we get the type of monoids as
follows.

We first define the three laws:

\begin{code}
left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
left-neutral {𝓤} {X} e _·_ = (x : X) → e · x ≡ x

right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
right-neutral {𝓤} {X} e _·_ = (x : X) → x ≡ e · x

associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative {𝓤} {X} _·_ = (x y z : X) → (x · y) · z ≡ x · (y · z)
\end{code}

Then a monoid is a set equipped with such `e` and `_·_` satisfying these
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

*Remark.* People are more likely to use
[records](https://agda.readthedocs.io/en/latest/language/record-types.html)
in Agda rather than iterated `Σ`s as above ([recall](#sigmatypes) that we defined
`Σ` using a record). This is fine, because records amount to iterated
`Σ` types ([recall](#sigmatypes) that also `_×_` is a `Σ` type, by
definition). Here, however, we are being deliberately spartan. Once we
have defined our Agda notation for `MLTT`, we want to stick to
it. This is for teaching purposes (of `MLTT`, encoded in Agda, not of
Agda itself in its full glory).

We could drop the `is-set X` condition, but then we wouldn't get
`∞`-monoids in any reasonable sense. We would instead get "wild
`∞`-monoids" or "incoherent `∞`-monoids". The reason is that in
monoids (with sets as carriers) the neutrality and associativity
equations can hold in at most one way, by definition of set. But if we
drop the set-hood requirement, then the equations can hold in multiple
ways. And then one is forced to consider equations between the
witnesses of the equations (all the way up in the ∞-case), which is
what "[coherence](https://ncatlab.org/nlab/show/coherence+law) data"
means. The wildness or incoherence amounts to the absence of such
data.

Similarly to the situation with magmas, identifications of monoids are
in bijection with monoid isomorphisms, assuming univalence. For this
to be the case, it is absolutely necessary that the carrier of a
monoid is a set rather than an arbitrary type, for otherwise the
monoid equations can hold in many possible ways, and we would need to
consider a notion of monoid isomorphism that in addition to preserving
neutral element and the multiplication, preserves the equations, and
the preservations of the equations, and the preservation of the
preservations of the equations, and so on.

*Exercise.* Define the type of groups (with sets as carriers).

*Exercise.* Write down the various types of categories defined in the
HoTT book in Agda.

*Exercise.* Try to define a type of topological spaces.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="identitytypeuf"></a> The identity type in univalent mathematics

We can view a type `X` as a sort of category with hom-types rather than
hom-sets, with composition defined as follows (and written in
so-called diagramatic order rather than the usual backwards order like
we wrote function composition).

If we wanted to prove the following without pattern matching, this
time we would need the dependent version `J` of induction on `_≡_`.

*Exercise.* Try to do this with `J` and with `H`.

We have that `refl` provides a neutral element for composition of
identifications:

\begin{code}
refl-left : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p
\end{code}

And composition is associative:

\begin{code}
∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)
\end{code}

But all arrows, the identifications, are invertible:

\begin{code}
⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)
\end{code}

A category in which all arrows are invertible is called a
groupoid. The above is the basis for the Hofmann--Streicher groupoid
model of type theory.

But we actually get higher groupoids, because given
identifications

   > `p q : x ≡ y`

we can consider the identity type `p ≡ q`, and given

   > `u v : p ≡ q`

we can consider the type `u ≡ v`, and so on ad infinitum.
See [[van den Berg and Garner](https://arxiv.org/abs/0812.0298)] and
[[Lumsdaine](https://lmcs.episciences.org/1062)].

For some types, such as the natural numbers, we [can
prove](#naturalsset) that this process trivializes after the first
step, because the type `x ≡ y` has at most one element. Such types are
the sets as defined above.

Voevodsky defined the notion of [*hlevel*](#hlevel) to measure how long it takes
for the process to trivialize.

Here are some more constructions with identifications:

\begin{code}
⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)
\end{code}

The application operation on identifications is functorial, in the
sense that is preserves the neutral element and commutes with
composition.:

\begin{code}
ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)
\end{code}

Transport is also functorial with respect to identification
composition and function composition. By construction, it maps the
neutral element to the identity function. The apparent contravarience
takes place because we have defined function composition in the usual
order, but identification composition in diagramatic order (as is
customary in each case).

\begin{code}
transport∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)
\end{code}

When writing `p ∙ q`, we lose information on the lhs and the rhs of the
identification, which makes some definitions hard to read. We now
introduce notation to be able to write e.g.

   > `x ≡⟨ p ⟩`

   > `y ≡⟨ q ⟩`

   > `z ∎`

as a synonym of the expression `p ∙ q` with some of the implicit arguments of `_∙_` made
explicit. We have one ternary *mixfix* operator `_≡⟨_⟩_` and one unary
"postfix" operator _∎.

\begin{code}
_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="dependentequality"></a> Identifications that depend on identifications, and equality in Σ-types

If we have an identification `p : A ≡ B` of two types `A` and `B`, and
elements `a : A` and `b : B`, we cannot ask directly whether `a ≡ b`,
because although the types are identified by `p`, they are not
necessarily the same, in the sense of definitional equality. This is
not merely a syntactical restriction of our formal system, but instead
is a fundamental fact that reflects the philosophy of univalent
mathematics. For instance, consider the type

\begin{code}
data Color : 𝓤₀ ̇  where
 Black White : Color
\end{code}

With univalence, we will have that `Color ≡ 𝟚` where `𝟚` is the
[two-point type](#binarysum) `𝟙 + 𝟙` with points `₀` and `₁`.  But
there will be two identifications `p₀ p₁ : Color ≡ 𝟚`, one that
identifies `Black` with `₀` and `White` with `₁`, and another that
identifies `Black` with `₁` and `White` with `₀`. There is no
preferred coding of binary colors as bits.  And, precisely because of
that, even if univalence does give inhabitants of the type `Colour ≡
𝟚`, it doesn't make sense to ask whether `Black ≡ ₀` holds without
specifying one of the possible inhabitants `p₀` and `p₁`.

What we will have is that `transport id p₀` and `transport id p₁` are
the two possible bijections `Color → 𝟚` that identify colors with
bits. So, it is not enough to have `Color ≡ 𝟚` to be able to compare a
color `c : Color` with a bit `b : 𝟚`. We need to specify which
identification `p : Color ≡ 𝟚` we want to consider for the comparison.
The [same considerations](#notsets) apply when we consider identifications `p
: 𝟚 ≡ 𝟚`.

So the meaningful comparison in the more general situation is

   > `transport id p a ≡ b`

for a specific

   > `p : A ≡ B`,

where `id` is the identity function of the universe where the types `A`
and `B` live, and hence

  > `transport id : A ≡ B → (A → B)`

is the function that transforms identifications into functions, which
has already occurred [above](#negation) in a special case.

More generally, we want to consider the situation in which we replace
the identity function `id` of the universe where `A` and `B` live to
an arbitrary type family, which is what we do now.

If we have a type

   > `X : 𝓤 ̇` ,

and a type family

   > `A : X → 𝓥 ̇`

and points

   > `x y : X`

and an identification

   > `p : x ≡ y`,

then we get the identification

   > `ap A p : A x ≡ A y`.

However, if we have

   > `a : A x`,

   > `b : A y`,

we again cannot write down the identity type

   > ~~`a ≡ b`~~ .

This is again a non-sensical mathematical statement in univalent
foundations, because the types `A x` and `A y` are not the same, but
only identified, and in general there can be many identifications, not
just `ap A p`, and so any identification between elements of `A x` and
`A y` has to be with respect to a specific identification, as in the
above particular case.

So we define a notion of dependent equality between elements `a : A x`
and `b : A y`, where the dependency is on an given identification
`p : x ≡ y`. We write

   > `dId A p a b`

for the type of "identifications of `a` and `b` dependent on the
identification `p : x ≡ y` over the family `A`".

We can define this by

   > `dId A (refl x) a b = (a ≡ b)`.

But, because

   > `transport A (refl x) a = a`,

by definition, we may as well define `dId` as follows in Agda:

\begin{code}
dId : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y) → A x → A y → 𝓥 ̇
dId A p a b = transport A p a ≡ b
\end{code}

We now define special syntax in Agda to be able to write this in the
more symmetrical way

   > `a ≡[ p / A ] b`.

This stands for equality of `a` and `b` dependent on `p` over
`A`. Because we have chosen to say *over*, we may as well use the
symbol `/` to express this. We define this quaternary mix-fix operator
`_≡[_/_]_` with a [syntax
declaration](https://agda.readthedocs.io/en/latest/language/syntax-declarations.html)
as follows in Agda.

\begin{code}
syntax dId A p a b = a ≡[ p / A ] b
\end{code}

We have designed things so that, by construction, we get the
following:

\begin{code}
≡[]-on-refl-is-≡ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
                 → (a ≡[ refl x / A ] b) ≡ (a ≡ b)
≡[]-on-refl-is-≡ A {x} a b = refl (a ≡ b)
\end{code}

Notice the perhaps unfamiliar nested use of equality: the identity
type `transport A (refl x) a ≡ b` is equal to the identity type `a ≡
b`.  The proof is the reflexivity identification of the type `a ≡ b`.
We rewrite the above making the implicit arguments of `refl` explicit
so that it becomes apparent that we are using the identity type former
of a type that happens to be a universe.

\begin{code}
≡[]-on-refl-is-≡' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
                → (a ≡[ refl x / A ] b) ≡ (a ≡ b)

≡[]-on-refl-is-≡' {𝓤} {𝓥} {X} A {x} a b = refl {𝓥 ⁺} {𝓥 ̇ } (a ≡ b)
\end{code}

This says that we are taking the reflexivity proof of the equality type
of the universe `𝓥`, which lives in the next universe `𝓥 ⁺`, for the
element `a ≡ b` (which is a type) of `𝓥`.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="sigmaequality"></a> Equality in Σ types

With the above notion of dependent equality, we can characterize
equality in `Σ` types as follows.

\begin{code}
to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
         → σ ≡ τ
         → Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ
from-Σ-≡ (refl (x , a)) = (refl x , refl a)
\end{code}

If we define *logical equivalence* by

\begin{code}
_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)
\end{code}

then the above gives

   > `(σ ≡ τ) ⇔ Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ`.

But this is a very weak statement when the left- and right-hand
identity types may have multiple elements, which is precisely the
point of univalent mathematics.

What we want is the lhs and the rhs to be isomorphic, or more precisely,
[equivalent in the sense of Voevodsky](#fibersandequivalences).

Once we have defined this notion `_≃_` of type equivalence, this
characterization will become an equivalence

   > `(σ ≡ τ) ≃ Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ`.

But even this is not sufficiently precise, because in general there are
many equivalences between two types. For example, there are precisely
two equivalences

   > `𝟙 + 𝟙 ≃ 𝟙 + 𝟙`,

namely the identity function and the function that flips left and
right.  What we want to say is that a *specific map* is an
equivalence.  In our case, it is the function `from-Σ-≡` defined
above.

Voevodsky came up with a definition of a type "`f` is an equivalence"
which is always a subsingleton: a given function `f` can be an
equivalence in an most one way. But we first discuss *hlevels*.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hlevel"></a> Voevodsky's notion of hlevel

Voevodsky's hlevels `0,1,2,3,...` are shifted by `2` with respect to
the `n`-groupoid numbering convention, and correspond to `-2`-groupoids
(singletons), `-1`-groupoids (subsingletons), `0`-groupoids (sets),...

First Voevodsky defined a notion of *contractible type*, which we
refer to here as *singleton type*.

\begin{code}
is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)
\end{code}

Then the hlevel relation is defined by induction on ℕ, with the
induction step working with the identity types of the elements of the
type in question:

\begin{code}
_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)
\end{code}

It is often convenient in practice to have equivalent formulations of
the levels `1` (as subsingletons) and `2` (as sets), which we now
develop.

When working with singleton types, it will be convenient to have
distinghished names for the two projections:

\begin{code}
center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ
\end{code}

\begin{code}
singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y ⟩
                                             y ∎

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ ) → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="em"></a> The univalent principle of excluded middle

Under excluded middle, the only two subsingletons, up to equivalence,
are `𝟘` and `𝟙`. In fact, excluded middle in univalent mathematics
says precisely that.

\begin{code}
EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM  𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X
\end{code}

Notice that the above don't assert excluded middle, but instead say
what excluded middle is (like when we said what the twin-prime
conjecture is), in two logically equivalence versions:

\begin{code}
EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr x) = inr x

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x
\end{code}

We will not assume or deny excluded middle, which is an independent
statement (it can't be proved or disproved).

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hedberg"></a> Hedberg's Theorem

To characterize sets as the types of hlevel 2, we first need to show
that subsingletons are sets, and this is not easy. We use an argument
due to
[Hedberg](https://homotopytypetheory.org/references/hedberg/). This
argument also shows that [Voevodsky's hlevel are upper
closed](#hlevelsupper).

We choose to present an [alternative formulation of Hedberg's
Theorem](https://link.springer.com/chapter/10.1007/978-3-642-38946-7_14),
but we stress that the method of proof is essentially the same.

We first define a notion of constant map:

\begin{code}
wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'
\end{code}

The prefix "`w`" officially stands for "weakly". Perhaps
*incoherently constant* or *wildly constant* would be better
terminologies, with *coherence* understood in the `∞`-categorical
sense. We prefer to stick to *wildly* rather than *weakly*, and luckily
both start with the letter "`w`". The following is also probably not
very good terminology, but we haven't come up with a better one yet.

\begin{code}
collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ \(f : X → X) → wconstant f

collapser : (X : 𝓤 ̇ ) → collapsible X → X → X
collapser X (f , w) = f

collapser-wconstancy : (X : 𝓤 ̇ ) (c : collapsible X) → wconstant (collapser X c)
collapser-wconstancy X (f , w) = w
\end{code}

The point is that a type is a set if and only if its identity types
all have wconstant endomaps:

\begin{code}
hedberg : {X : 𝓤 ̇ } (x : X)
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

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="setscharacterization"></a> A characterization of sets

The following is immediate from the definitions:

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
\end{code}

And the converse is the contents of Hedberg's Theorem.

\begin{code}
≡-collapsibles-are-sets : (X : 𝓤 ̇ ) → ≡-collapsible X → is-set X
≡-collapsibles-are-sets X c x = hedberg x (λ y → collapser (x ≡ y) (c x y) ,
                                                 collapser-wconstancy (x ≡ y) (c x y))
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="subsingletonsaresets"></a> Subsingletons are sets

In the following definition of the auxiliary function `f`, we ignore
the argument `p`, using the fact that `X` is a subsingleton instead,
to get a `wconstant` function:

\begin{code}
subsingletons-are-≡-collapsible : (X : 𝓤 ̇ ) → is-subsingleton X → ≡-collapsible X
subsingletons-are-≡-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)
\end{code}

And the corollary is that subsingleton types are sets.
\begin{code}
subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = ≡-collapsibles-are-sets X (subsingletons-are-≡-collapsible X s)
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hlevel1subsingleton"></a> The types of hlevel 1 are the subsingletons

Then with the above we get our desired characterization of the types of
hlevel `1` as immediate consequences:

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

This is an "if and only if" characterization, but, under univalence, it becomes an equality [because](#propext) the types under consideration are subsingletons.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hlevel2set"></a> The types of hlevel 2 are the sets

The same comments as for the previous section apply.

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

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hlevelsupper"></a> The hlevels are upper closed

A singleton is a subsingleton, a subsingleton is a set, ... , a type
of hlevel `n` is of hlevel `n+1` too, ...

Again we can conclude this almost immediately from the above development:

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

To be consistent with the above terminology, we have to stipulate that
all types have hlevel `∞`. We don't need a definition for this vacuous
notion. But what may happen (and it does with univalence) is that
there are types which don't have any finite hlevel. We can say that
such types then have minimal hlevel `∞`.

*Exercise.* Formulate and prove the following. The type `𝟙` has
minimal hlevel `0`. The type `𝟘` has minimal hlevel `1`, the type `ℕ`
has minimal hlevel `2`. More ambitiously, when you have
[univalence](#univalence) at your disposal, show that the type of
monoids has minimal hlevel `3`.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="naturalsset"></a> Example: ℕ is a set

We first prove the remaining Peano axioms.

The following is how one proves in `MLTT` that `succ x ≢ 0`. Agda
allows one to prove this rather easily with `()` patterns instead, but
this mechanism is beyond the realm of `MLTT`. For this reason, we are
using this feature only once, to prove `𝟘-induction` as
[above](#emptytype).

\begin{code}
positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred
\end{code}

With this we have proved all the Peano axioms.

*Without* assuming the principle of excluded middle, we can prove that
`ℕ` has decidable equality in the following sense:

\begin{code}
ℕ-has-decidable-equality : (x y : ℕ) → (x ≡ y) + (x ≢ y)
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : (x ≡ y) + x ≢ y → (succ x ≡ succ y) + (succ x ≢ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))
\end{code}

*Exercise.* Students should do this kind of thing at least once in
their academic life: rewrite the above proof of the decidability of
equality of `ℕ` to use `ℕ-induction` instead of pattern matching and
recursion, to understand by themselves that this can be done.

And using the decidability of equality we can define a `wconstant`
function `x ≡ y → x ≡ y` and hence conclude that ℕ is a set. This
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

*Exercise.* Hedberg proved this for any type with decidable
equality. Generalize the above to account for this and hence develop /
practice your Agda skills.

*Exercise.* Prove that the types of magmas, monoids and groups have
hlevel `3` (they are `1`-groupoids) but not hlevel `2` (they are not
sets).  Prove that this is their minimal level. Can you do this with
what we have learned so far?

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="naturaltranformations"></a> Natural transformations

TODO. Explain this section. The main point in these notes is the construction `NatΣ`.

\begin{code}
Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y) → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="retracts"></a> Retracts

We use retracts as a mathematical technique to transfer properties
between types. For instance, retracts of singletons are
singletons. Showing that a particular type `X` is a singleton may be
rather difficult to do directly by applying the definition of
singleton type and the definition of the particular type, but it may
be easy to show that `X` is a retract of `Y` for a type `Y` that is
already known to be a singleton. In these notes, a major application
will be to get a simple proof of the known fact that invertible maps
are equivalences in the sense of Voevodsky.

A *section* of a function is simply a right inverse, by definition:

\begin{code}
has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ \(s : codomain r → domain r) → r ∘ s ∼ id
\end{code}

Notice that `has-section r` is the type of all sections `(s , η)` of `r`,
which may well be empty. So a point of this type is a designated
section `s` of `r`, together with the datum `η`. Unless the domain of `r` is a
set, this datum is not property, and we may well have an element
`(s , η')` of the type `has-section r` with `η'` distinct from `η` for the same `s`.

We say that *`X` is a retract of `Y`*, written `X ◁ Y`, if we
have a function `X → Y` which has a section:

\begin{code}
_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ \(r : Y → X) → has-section r
\end{code}

This type actually collects *all* the ways in which the type `X` can
be a retract of the type `Y`, and so is data or structure on `X` and
`Y`, rather than a property of them.

A function that has a section is called a retraction. We use this
terminology, ambiguously, also for the function that projects out the
retraction:

\begin{code}
retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y) → retraction ρ ∘ section ρ ∼ id
retract-equation (r , s , η) = η
\end{code}

We have an identity retraction:

\begin{code}
◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl X = id , id , refl
\end{code}

*Exercise.* The identity retraction is by no means the only retraction
of a type onto itself in general, of course. Prove that we have (that
is, produce an element of the type) `ℕ ◁ ℕ` with the function
`pred : ℕ → ℕ` defined above as the retraction, to exercise your Agda
skills. Can you produce more inhabitants of this type?

We can define the composition of two retractions as follows:

\begin{code}
_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , p)
 where
  p = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
            r (s x)           ≡⟨ η x ⟩
            x                 ∎
\end{code}

We also define composition with an implicit argument made explicit:

\begin{code}

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ
\end{code}

And we introduce the following postfix notation for the identity
retraction:

\begin{code}
_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = ◁-refl X
\end{code}

These last two definitions are for notational convenience. See
[below](#fibersandequivalences) for examples of their use.

We conclude this section with some facts about retracts of `Σ` types.
The following are technical tools for dealing with equivalences in the
sense of Voevosky in [comparison with invertible
maps](#fibersandequivalences).

A pointwise retraction gives  a retraction of the total spaces:
\begin{code}
Σ-retract : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
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

And we can reindex retracts of Σ types as follows:

\begin{code}
Σ-retract-reindexing : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
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

We have defined [the property of a type being a singleton](#hlevel). The
following defines singleton types, which have the property of being
singletons.

\begin{code}
singleton-type : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type x = Σ \y → y ≡ x

singleton-type-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇ } (x y : X) (p : y ≡ x) → singleton-type-center x ≡ (y , p)
singleton-type-centered x x (refl x) = refl (singleton-type-center x)

singleton-types-are-singletons : {X : 𝓤 ̇ } (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons {𝓤} {X} x = singleton-type-center x , a
 where
  a : (σ : singleton-type x) → singleton-type-center x ≡ σ
  a (y , p) = singleton-type-centered x y p
\end{code}

The following gives a technique to show that some types are singletons:

\begin{code}
retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ : (y : codomain r) → r c ≡ y
  γ y = r c     ≡⟨ ap r (φ (s y)) ⟩
        r (s y) ≡⟨ η y ⟩
        y       ∎
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="fibersandequivalences"></a> Voevodsky's notion of equivalence

The main notions of univalent mathematics conceived by Voevodsky, with
formulations in `MLTT`, are those of [singleton type](#hlevels) (or
contractible type), [hlevel](#hlevels) (including the notions of
subsingleton and set), and of type equivalence, which we define now.
For that purpose, we need to define the notion of fiber of a function
first.

But we begin with a discussion of the notion of *invertible function*,
whose only difference with the notion of equivalence is that it is
data rather than property:

\begin{code}
invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)
\end{code}

The situation is that we will have a logical equivalence between "data
establishing invertibility of a given function" and "the property of
the function being an equivalence". Mathematically, what happens is
that the type "`f` is an equivalence" is a retract of the type "`f` is
invertible". This retraction property is not easy to show, and there
are many approaches. We discuss an approach we came up with while
developing these lecture notes, which is intended to be relatively
simple and direct, but the reader should consult other approaches,
such as that of the HoTT Book, which has a well-established
categorical pedigree.

The problem with the notion of invertibility of `f` is that, while we
can prove that the inverse `g` is unique when it exists, we cannot in
general prove that the identification data `g ∘ f ∼ id` and `f ∘ g ∼
id` are also unique, and, indeed, they are not.

The following is Voevodsky's proposed formulation of the notion of
equivalence in MLTT:

\begin{code}
fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ \(x : domain f) → f x ≡ y
\end{code}

So the type `fiber f y` collects the points `x : X` which are mapped
to a point identified with `y`, *together* with the identification
data. Voevodsky's insight is that a general notion of equivalence can
be formulated in MLTT by requiring the fiber to be a singleton. It is
important here that not only the `y:Y` with `f x ≡ y` is unique, but
also that the identification data `p : f x ≡ y` is unique. This is
similar to, or even essentially the same thing as the categorical
notion of ``uniqueness up to a unique isomorphism``.

\begin{code}
is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)
\end{code}

It is easy to see that equivalences are invertible:

\begin{code}
inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = pr₁ (center (fiber f y) (e y))

inverse-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                   → (y : Y) → f (inverse f e y) ≡ y
inverse-is-section f e y = pr₂ (center (fiber f y) (e y))

inverse-centrality : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f) (y : Y)
                   → (t : fiber f y) → (inverse f e y , inverse-is-section f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverse-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                      → (x : X) → inverse f e (f x) ≡ x
inverse-is-retraction f e x = ap pr₁ (inverse-centrality f e (f x) (x , (refl (f x))))

equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → invertible f
equivs-are-invertible f e = (inverse f e , inverse-is-retraction f e , inverse-is-section f e)
\end{code}

The non-trivial direction is this, for which we use the retraction
techniques explained [above](#retractsofsigma):

\begin{code}
invertibles-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → invertible f → is-equiv f
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

\begin{code}
inverse-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                 → is-equiv (inverse f e)
inverse-is-equiv f e = invertibles-are-equivs
                         (inverse f e)
                         (f , inverse-is-section f e , inverse-is-retraction f e)
\end{code}


To see that the above procedures do exhibit the type "`f` is an
equivalence" as a retract of the type "`f` is invertible", it suffices
to show that it is a subsingleton.

The identity function is invertible:
\begin{code}
id-invertible : (X : 𝓤 ̇ ) → invertible (id {𝓤} {X})
id-invertible X = id , refl , refl
\end{code}

We can compose invertible maps:

\begin{code}
∘-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {f' : Y → Z}
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

There is an identity equivalence, and we get composition of
equivalences by reduction to invertible maps:

\begin{code}
id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (id {𝓤} {X})
id-is-equiv X = singleton-types-are-singletons

∘-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)
∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = invertibles-are-equivs (g ∘ f)
                                                    (∘-invertible (equivs-are-invertible g i)
                                                                  (equivs-are-invertible f j))
\end{code}

The type of equivalences is defined as follows:

\begin{code}
_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq-to-fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq-to-fun (f , e) = f

Eq-to-fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv (f , i) = i
\end{code}

Identity and composition of equivalences:

\begin{code}
≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = id , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_●_ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} (f , d) (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverse-is-equiv f e
\end{code}

We can use the following for equational reasoning with equivalences:

\begin{code}
_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = ≃-refl
\end{code}

We conclude this section with some examples.
The function `transport A p` is an equivalence.

\begin{code}
transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)

transport-≃ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
            → x ≡ y → A x ≃ A y
transport-≃ A p = transport A p , transport-is-equiv A p
\end{code}

A longer proof for the sake of conceptual illustration:

\begin{code}
transport-is-equiv' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                    → is-equiv (transport A p)
transport-is-equiv' A p =
  invertibles-are-equivs
   (transport A p)
   (transport A (p ⁻¹) ,
    (λ a → transport A (p ⁻¹) (transport A p a) ≡⟨ (ap (λ - → - a) (transport∙ A p (p ⁻¹)))⁻¹ ⟩
           transport A (p ∙ p ⁻¹) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-right∙ p) ⟩
           a                                    ∎) ,
     λ a → transport A p (transport A (p ⁻¹) a) ≡⟨ (ap (λ - → - a) (transport∙ A (p ⁻¹) p))⁻¹ ⟩
           transport A (p ⁻¹ ∙ p) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-left∙ p) ⟩
           a                                    ∎)
\end{code}

Characterization of equality in `Σ` types:

\begin{code}
Σ-≡-equivalence : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
                → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
Σ-≡-equivalence  {𝓤} {𝓥} {X} {A}  σ τ = from-Σ-≡ ,
                                        invertibles-are-equivs from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ) → from-Σ-≡ (to-Σ-≡ w) ≡ w
  η (refl p , refl q) = refl (refl p , refl q)
  ε : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε (refl σ) = refl (refl σ)
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="univalence"></a> Voevodsky's univalence axiom

There is a canonical transformation `(X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y` that
sends the identity identification `refl X : X X ≡ X` to the identity
equivalence `≃-refl X` by induction on identifications. The univalence
axiom, for the universe `𝓤`, say that this canonical map is itself an
equivalence.

\begin{code}
Id-to-Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id-to-Eq X X (refl X) = ≃-refl X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id-to-Eq X Y)
\end{code}

We emphasize that this doesn't posit that univalence holds. It says
what univalence is (like the type that says what the twin-prime
conjecture is).

\begin{code}
Eq-to-Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq-to-Id ua X Y = inverse (Id-to-Eq X Y) (ua X Y)
\end{code}

Two equivalent ways to convert a type equality into a function:

\begin{code}
Id-to-fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun {𝓤} {X} {Y} p = Eq-to-fun (Id-to-Eq X Y p)

Id-to-fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun' = transport id

Id-to-funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-fun p ≡ Id-to-fun' p
Id-to-funs-agree (refl X) = refl id
\end{code}

What characterizes univalent mathematics is not the univalence axiom. We have defined and studied the main
concepts of univalent mathematics in a pure, spartan `MLTT`. It is the
concepts of hlevel, including singleton, subsingleton and set, and the
notion of equivalence. Univalence *is* a fundamental ingredient, but
first we need the correct notion of equivalence to be able to
formulate it.

*Remark*. If we formulate univalence with invertible maps instead of
equivalences, we get a statement that is provable false, and this is
why Voevodsky's notion of equivalence is important. This is Exercise
4.6 of the HoTT book. There is a [solution in
Coq](https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v)
by [Mike Shulman](https://home.sandiego.edu/~shulman/).

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="notsets"></a> Example of a type that is not a set under univalence

We have two automorphisms of `𝟚`, namely the identity function and the
function that swaps ₀ and ₁:

\begin{code}

swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs swap₂ (swap₂ , swap₂-involutive , swap₂-involutive)
\end{code}

Hence we have two distinct equivalences:

\begin{code}
e₀ e₁ : 𝟚 ≃ 𝟚
e₀ = ≃-refl 𝟚
e₁ = swap₂ , swap₂-is-equiv

e₀-is-not-e₁ : e₀ ≢ e₁
e₀-is-not-e₁ p = ₁-is-not-₀ r
 where
  q : id ≡ swap₂
  q = ap pr₁ p
  r : ₁ ≡ ₀
  r = ap (λ - → - ₁) q
\end{code}

We now use an [anonymous
module](https://agda.readthedocs.io/en/latest/language/module-system.html#anonymous-modules)
to assume univalence in the next few constructions:

\begin{code}
module _ (ua : is-univalent 𝓤₀) where
\end{code}

With this assumption, we get two different identifications of the type `𝟚` with itself:

\begin{code}
  p₀ p₁ : 𝟚 ≡ 𝟚
  p₀ = Eq-to-Id ua 𝟚 𝟚 e₀
  p₁ = Eq-to-Id ua 𝟚 𝟚 e₁

  p₀-is-not-p₁ : p₀ ≢ p₁
  p₀-is-not-p₁ q = e₀-is-not-e₁ r
   where
    r = e₀              ≡⟨ (inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
        Id-to-Eq 𝟚 𝟚 p₀ ≡⟨ ap (Id-to-Eq 𝟚 𝟚) q ⟩
        Id-to-Eq 𝟚 𝟚 p₁ ≡⟨ inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁ ⟩
        e₁              ∎
\end{code}

Therefore if the universe `𝓤₀` were a set, then the identifications
`p₀` and `p₁` defined above would be equal:

\begin{code}
  𝓤₀-is-not-a-set :  ¬(is-set (𝓤₀ ̇ ))
  𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
   where
    q : p₀ ≡ p₁
    q = s 𝟚 𝟚 p₀ p₁
\end{code}

For more examples, see [[Kraus and Sattler](https://arxiv.org/abs/1311.4002)].

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="lefttothereader"></a> Facts left to the reader but needed now

Here are some facts whose proofs are left to the reader but we will
need from the next section onwards. Sample solutions are given
[below](#solutions).

Define functions for the following type declarations. As a matter of
procedure, we suggest to import this file and add another declaration
with the same type and new name e.g. `section-are-lc-solution`,
because we already have solutions in this file.

We start with the notion of left cancellability.

\begin{code}
left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ≡ f x' → x ≡ x'

lc-maps-reflect-subsingletonness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-subsingleton Y
                                 → is-subsingleton X

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ \(r : codomain s → domain s) → r ∘ s ∼ id

sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A) → has-retraction s → left-cancellable s

equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f

equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f

equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → is-subsingleton Y
                      → is-subsingleton X

equiv-to-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → is-subsingleton X
                      → is-subsingleton Y

sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                        → has-retraction f
                        → g ∼ f
                        → has-retraction g

retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g
\end{code}

An alternative notion of equivalence, equivalent to Voevodsky's, has
been given by Andre Joyal:

\begin{code}
is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f
\end{code}

Provide definitions for the following type declarations:

\begin{code}
joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-joyal-equiv f → invertible f

joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-joyal-equiv f → is-equiv f

invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f

equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g

equivs-closed-under-∼' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                       → is-equiv f
                       → f ∼ g
                       → is-equiv g

≃-gives-◁ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → X ◁ Y

≃-gives-▷ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → Y ◁ X

equiv-to-singleton : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                   → X ≃ Y → is-singleton Y → is-singleton X

equiv-to-singleton' : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                   → X ≃ Y → is-singleton X → is-singleton Y

pr₁-equivalence : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                → ((x : X) → is-singleton (A x))
                → is-equiv (λ (t : Σ A) → pr₁ t)

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))

Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ≡ y) ≃ (y ≡ x)

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' x = Σ \y → x ≡ y

singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x

singleton-types-are-singletons' : {X : 𝓤 ̇ } (x : X) → is-singleton (singleton-type' x)

singletons-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                      → is-singleton X → is-singleton Y → X ≃ Y

maps-of-singletons-are-equivs : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                 → (x : X) (b : B x) → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                                 → is-equiv (NatΣ φ) → ((x : X) → is-equiv (φ x))
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="funextfromua"></a> Function extensionality from univalence

Function extensionality says that any two pointwise equal functions
are equal. This is known to be not provable or disprovable in
`MLTT`. It is an independent statement, which we abbreviate `funext`.

\begin{code}
funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
\end{code}

There [will be](#hfunext) two stronger statements, namely
the generalization to dependent functions, and the requirement that
the canonical map `(f ≡ g) → (f ∼ g) ` is an equivalence.

*Exercise.* Assuming `funext`, prove that, if `f : X → Y` is an equivalence
then so is the function `(-) ∘ f : (Y → Z) → (X → Z)`.

The crucial step in [Voevodsky's proof](http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf) that univalence implies funext
is to establish the conclusion of the above exercise assuming
univalence instead.  This relies on the following lemma, which
describes pre-composition of equivalences in terms of `transport`.

\begin{code}
transport-is-pre-comp : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (e : X ≃ Y) (g : Y → Z)
                      → transport (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹) g ≡ g ∘ Eq-to-fun e
\end{code}

We will use this with `e = (f , i)` and `i : is-equiv f`, in which
case `Eq-to-fun e` is `f`, as the function `Eq-to-fun : X ≃ Y → X → Y`
is defined to be the first projection.

In order to be able to proceed by `≡-induction` on an identification
`p : X ≡ Y`, we define the auxiliary function `α`, and then take `p`
to be `Eq-to-Id ua X Y e`.

\begin{code}
transport-is-pre-comp ua {X} {Y} {Z} e g = α e (Eq-to-Id ua X Y e) (refl (Eq-to-Id ua X Y e))
 where
  α : (e : X ≃ Y) (p : X ≡ Y)
    → p ≡ Eq-to-Id ua X Y e
    → transport (λ - → - → Z) (p ⁻¹) g ≡ g ∘ Eq-to-fun e
  α e (refl X) = γ
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
\end{code}

The following is then an immediate consequence of the above lemma,
using the facts that transports are equivalences and that equivalences
are closed under pointwise equality.

\begin{code}
pre-comp-is-equiv : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (f : X → Y)
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

A cryptic version of the above proof is the following:

\begin{code}
pre-comp-is-equiv' : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f
                   → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv' ua {X} {Y} {Z} f i = equivs-closed-under-∼'
                                          (transport (λ - → - → Z) ((Eq-to-Id ua X Y (f , i))⁻¹))
                                          (_∘ f)
                                          (transport-is-equiv (λ - → - → Z) ((Eq-to-Id ua X Y (f , i))⁻¹))
                                          (transport-is-pre-comp ua (f , i))
\end{code}

With this we can prove the desired result as follows.

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

This definition of `γ` is probably too quick. Here are all the steps
performed silently by Agda, by expanding judgmental equalities,
indicated with `refl` here:

\begin{code}
  γ' = f₀                              ≡⟨ refl _ ⟩
       (λ x → f₀ x)                    ≡⟨ refl _ ⟩
       (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
       (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl _ ⟩
       (λ x → f₁ x)                    ≡⟨ refl _ ⟩
       f₁                              ∎
\end{code}

So notice that this relies on the so-called η-rule for judgmental
equality of functions, namely `f = λ x → f x`. Without it, we would
only get that `f₀ ∼ f₁ → (λ x → f₀ x) ≡ (λ x → f₁ x)` instead.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hfunext"></a> Variations of function extensionality and their equivalence

Dependent function extensionality:

\begin{code}
dfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g
\end{code}

The above says that there is some map `f ~ g → f ≡ g`. The following
instead says that the canonical map in the other direction is an
equivalence:

\begin{code}
happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)
\end{code}

Voevodsky showed that all notions of function extensionaliry are
equivalent to saying that products of singletons are singletons:

\begin{code}
vvfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-singleton (A x)) → is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe i = (λ x → pr₁ (i x)) , (λ f → fe (λ x → pr₂ (i x) (f x)))
\end{code}

We need some lemmas to get `hfunext` from `vvfunext`:

\begin{code}
post-comp-is-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
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

post-comp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → funext 𝓦 𝓤 → funext 𝓦 𝓥
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

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="univalencesubsingleton"></a> The univalence axiom is a (sub)singleton type

If we use a type as an axiom, it should have at most one element. We
prove some generally useful lemmas first.

\begin{code}
Π-is-subsingleton : dfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → ((x : X) → is-subsingleton (A x)) → is-subsingleton (Π A)
Π-is-subsingleton fe i f g = fe (λ x → i x (f x) (g x))

being-a-singleton-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-singleton X)
being-a-singleton-is-a-subsingleton fe {X} (x , φ) (y , γ) = to-Σ-≡ (φ y , fe (λ z → s y z _ _))
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)
  s : is-set X
  s = subsingletons-are-sets X i

being-an-equiv-is-a-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
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
univalence cannot be expressed in our `MLTT` that only has countably
many universes, because global univalence would have to live in the
first universe after them. Agda does have such a universe 𝓤ω, and so
we can formulate it this. There would be no problem in extending our
`MLTT` to have such a universe if we so wished, in which case we would
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

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="hfunextsubsingleton"></a> `hfunext` and `vvfunext` are subsingletons

This is left as an exercise. Like univalence, the proof that these two
forms of function extensional extensionality require assumptions of
function extensionality at higher universes. So perhaps it is more
convenient to just assume global univalence. An inconvinience is that
the natural tool to use, Π-is-subsingleton, needs products with
explicit arguments, but we made some of the arguments of hfunext and
vvfunext implicit. One way around this problem is to define equivalent
versions with the arguments explicit, and establish an equivalence
between the new version and the original version.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="morefunextuses"></a> More applications of function extensionality

\begin{code}
being-a-subsingleton-is-a-subsingleton : {X : 𝓤 ̇ } → dfunext 𝓤 𝓤 → is-subsingleton (is-subsingleton X)
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
Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))
  b : is-subsingleton(f ≡ g)
  b = equiv-to-subsingleton (happly f g) (hfe f g) a

being-set-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-set X)
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

*Exercise.*
\begin{code}
𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
𝟚-has-𝟚-automorphisms fe =
\end{code}
<!--- Exercise.
\begin{code}
 (f , invertibles-are-equivs f (g , η , ε))
 where
  f : (𝟚 ≃ 𝟚) → 𝟚
  f (h , e) = h ₀
  g : 𝟚 → (𝟚 ≃ 𝟚)
  g ₀ = id , id-is-equiv 𝟚
  g ₁ = swap₂ , swap₂-is-equiv
  η : (e : 𝟚 ≃ 𝟚) → g (f e) ≡ e
  η (h , e) = γ (h ₀) (h ₁) (refl (h ₀)) (refl (h ₁))
   where
    γ : (m n : 𝟚) → h ₀ ≡ m → h ₁ ≡ n → g (h ₀) ≡ (h , e)
    γ ₀ ₀ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₀   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))
    γ ₀ ₁ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₀) ₀     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₀) ₁     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)) ,
                being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₀ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₁) ₀     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₁) ₁     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)) ,
                being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₁ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₁   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))

  ε : (n : 𝟚) → f (g n) ≡ n
  ε ₀ = refl ₀
  ε ₁ = refl ₁
\end{code}
-->

\begin{code}
●-assoc : dfunext 𝓣 (𝓤 ⊔ 𝓣) → dfunext (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣) →
         {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
          (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
        → α ● (β ● γ) ≡ (α ● β) ● γ
●-assoc fe fe' (f , a) (g , b) (h , c) = to-Σ-≡ (p , q)
 where
  p : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
  p = refl (h ∘ g ∘ f)

  d e : is-equiv (h ∘ g ∘ f)
  d = ∘-is-equiv (∘-is-equiv c b) a
  e = ∘-is-equiv c (∘-is-equiv b a)

  q : transport is-equiv p d ≡ e
  q = being-an-equiv-is-a-subsingleton fe fe' (h ∘ g ∘ f) _ _

inversion-involutive : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                     → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inversion-involutive f e = refl f

≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓥 ⊔ 𝓤) (𝓥 ⊔ 𝓤) →
                   {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                 → ≃-sym (≃-sym α) ≡ α
≃-sym-involutive fe fe' (f , a) = to-Σ-≡ (inversion-involutive f a ,
                                          being-an-equiv-is-a-subsingleton fe fe' f _ _)
\end{code}


*Exercise.* The hlevels are closed under `Σ` and, using `hfunext`, also
under Π. Univalence is not needed, but makes the proof easier.  (If
you don't use univalence, you will need to show that hlevels are
closed under equivalence.)

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="axiomsofchoice"></a> The univalent axiom of choice

TODO. We don't assume or reject it.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="truncation"></a> Subsingleton truncation

The following is Voevosky's approach to saying that a type is
inhabited in such a way that the statement of inhabitation is a
subsingleton (using funext or univalence if needed).

\begin{code}
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P
\end{code}

This says that if we have a function from `X` to a subsingleton `P`, then
`P` must have a point. So this fails when `X=𝟘`. Considering `P=𝟘`, we conclude
that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty. However,
in the absence of excluded middle, inhabitation is stronger than
excluded middle.

For simplicity in the formulation of the theorems, we assume global
dfunext.

\begin{code}
global-dfunext : 𝓤ω
global-dfunext = ∀ 𝓤 𝓥 → dfunext 𝓤 𝓥

inhabitation-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ ) → is-subsingleton (is-inhabited X)
inhabitation-is-a-subsingleton {𝓤} fe X =
  Π-is-subsingleton (fe (𝓤 ⁺) 𝓤)
    λ P → Π-is-subsingleton (fe 𝓤 𝓤)
           (λ (s : is-subsingleton P)
                 → Π-is-subsingleton (fe 𝓤 𝓤) (λ (f : X → P) → s))

pointed-is-inhabited : (X : 𝓤 ̇ ) → X → is-inhabited X
pointed-is-inhabited X x = λ P s f → f x

inhabited-recursion : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion X P s f φ = φ P s f

inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ ) → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s id
\end{code}

With this notion, we can define the image of a function as follows:

\begin{code}
∃ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥)⁺ ̇
∃ {𝓤} {𝓥} {X} A = is-inhabited (Σ \(x : X) → A x)

image : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image f = Σ \(y : codomain f) → ∃ \(x : domain f) → f x ≡ y
\end{code}

*Exercise.* An attempt to define the image of `f` without the
inhabitation predicate would be to take it to be ` `Σ \(y : codomain
f) → Σ \(x : domain f) → f x ≡ y`. Show that this type is equivalent
to `X`. This is similar to what happens in set theory: the graph of
any function is isomorphic to its domain.


We can define the restriction and corestriction of a function to its
image as follows:

\begin{code}
restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇} (f : X → Y)
            → image f → Y
restriction f (y , _) = y

corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇} (f : X → Y)
            → X → image f
corestriction f x = f x , pointed-is-inhabited (fiber f (f x)) (x , refl (f x))
\end{code}

And we can define the notion of surjection as follows:
\begin{code}
is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection f = (y : codomain f) → ∃ \(x : domain f) → f x ≡ y
\end{code}

*Exercise.* The type `(y : codomain f) → Σ \(x : domain f) → f x ≡ y`
 is equivalent to the type `has-section f`, which is stronger than
 saying that `f` is a surjection.

There are two problems with this definition of inhabitation:

  * Inhabitation has values in the next universe.

  * We can eliminate into propositions of the same universe only.

In particular, it is not possible to show that the map `X →
is-inhabited X` is a surjection, or that `X → Y` gives `is-inhabited X
→ is-inhabited Y`.

There are two proposed ways to solve this:

  * Voevodsky works with certain [resizing
    rules](http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf) for
    subsingletons. At the time of writing, the (relative) consistency
    of the system with such rules is an open question.

  * The HoTT book works with certain higher inductive types (HIT's).
    This is the same approach of taken by cubical Agda.

A third possibility is to work with propositional truncations
[axiomatially](https://lmcs.episciences.org/3217), which is compatible
with the above two proposals. We write this axiom as a record type
rather than as an iterated `Σ-type` for simplicity, where we use the
HoTT-book notation `∥ X ∥` for the inhabitation of `X`,
called the propositional truncation of `X`:

\begin{code}
record propositional-truncations-exist : 𝓤ω where
 field
  ∥_∥ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-prop : {𝓤 : Universe} {X : 𝓤 ̇ } → is-prop ∥ X ∥
  ∣_∣ : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇} → is-prop P → (X → P) → ∥ X ∥ → P
\end{code}

This is the approach we adopt in our [personal Agda
development](http://www.cs.bham.ac.uk/~mhe/agda-new/).

*Exercise*. If `X` and `Y` are types obtained by summing `x` and
  `y`-many copies of the type `𝟙`, as in `𝟙 + 𝟙 + ... + 𝟙` , where `x`
  and `y` are natural numbers, then `∥ X = Y ∥ = (x ≡ y)` and the type
  `X ≡ X` has `x!` elements.

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="choice"></a> The axiom of choice

For the moment see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-Choice.html).

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="sip"></a> Structure of identity principle

For the moment, see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-StructureIdentityPrinciple.html).

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="solutions"></a> Solutions to the facts needed above but left to the reader

\begin{code}
lc-maps-reflect-subsingletonness f l s x x' = l (s (f x) (f x'))

sections-are-lc s (r , ε) {x} {y} p = x       ≡⟨ (ε x)⁻¹ ⟩
                                      r (s x) ≡⟨ ap r p ⟩
                                      r (s y) ≡⟨ ε y ⟩
                                      y       ∎

equivs-have-retractions f e = (inverse f e , inverse-is-retraction f e)

equivs-have-sections f e = (inverse f e , inverse-is-section f e)

equivs-are-lc f e = sections-are-lc f (equivs-have-retractions f e)

equiv-to-subsingleton f e = lc-maps-reflect-subsingletonness f (equivs-are-lc f e)

equiv-to-subsingleton' f e = lc-maps-reflect-subsingletonness
                               (inverse f e)
                               (equivs-are-lc (inverse f e) (inverse-is-equiv f e))

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

joyal-equivs-are-equivs f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)

invertibles-are-joyal-equivs f (g , gf , fg) = ((g , fg) , (g , gf))

equivs-are-joyal-equivs f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)

equivs-closed-under-∼ f g e h = joyal-equivs-are-equivs g
                                 (retractions-closed-under-∼ f g (equivs-have-sections f e) h ,
                                  sections-closed-under-∼ f g (equivs-have-retractions f e) h)

equivs-closed-under-∼' f g e h = equivs-closed-under-∼ f g e (λ x → (h x)⁻¹)

≃-gives-◁ X Y (f , e) = (inverse f e , f , inverse-is-retraction f e)

≃-gives-▷ X Y (f , e) = (f , inverse f e , inverse-is-section f e)

equiv-to-singleton X Y e = retract-of-singleton (≃-gives-◁ X Y e)

equiv-to-singleton' X Y e = retract-of-singleton (≃-gives-▷ X Y e)

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

Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ = (NatΣ f , invertibles-are-equivs (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε))
 where
  f : (x : X) → A x → B x
  f x = Eq-to-fun (φ x)
  g : (x : X) → B x → A x
  g x = inverse (f x) (Eq-to-fun-is-equiv (φ x))
  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inverse-is-retraction (f x) (Eq-to-fun-is-equiv (φ x))
  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inverse-is-section (f x) (Eq-to-fun-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a) = x , g x (f x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
                   x , a           ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  NatΣ-ε (x , b) = x , f x (g x b) ≡⟨ ap (λ - → x , -) (ε x b) ⟩
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

## <a name="appendix"></a> Appendix

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="moreexercises"></a> Additional exercises

Solutions are available [at the end](#mlttexercisessol).

*Exercise.* A sequence of elements of a type `X` is just a function `ℕ → X`. Use [Cantor's diagonal argument] to show in Agda that the type of sequences of natural numbers is uncountable. A positive formulation is the following, where `ε` is an enumeration of sequences.

\begin{code}
succ-no-fixed-point : (n : ℕ) → succ n ≢ n

positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)
\end{code}

Universes as not cumulative in Agda, in the sense that from `X : 𝓤` we would get `X : 𝓤⁺` or `X : 𝓤 ⊔ 𝓥`.
The usual approach is to consider an embeddings of universes into larger universes:

\begin{code}
data Up {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 up : X → Up 𝓥 X

Up-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇) (A : Up 𝓥 X → 𝓦 ̇)
             → ((x : X) → A (up x))
             → ((l : Up 𝓥 X) → A l)

Up-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇} {B : 𝓦 ̇}
             → (X → B) → Up 𝓥 X → B

down : {X : 𝓤 ̇} → Up 𝓥 X → X

down-up : {X : 𝓤 ̇} (x : X) → down {𝓤} {𝓥} (up x) ≡ x

up-down : {X : 𝓤 ̇} (l : Up 𝓥 X) → up (down l) ≡ l

Up-≃ : (X : 𝓤 ̇) → Up 𝓥 X ≃ X
Up-≃ {𝓤} {𝓥} X = down {𝓤} {𝓥} , invertibles-are-equivs down (up , up-down , down-up {𝓤} {𝓥})

Up-left-≃ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → X ≃ Y → Up 𝓦 X ≃ Y

ap-Up-≃ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → X ≃ Y → Up 𝓦 X ≃ Up 𝓣 Y
\end{code}

We now discuss alternative formulations of the principle of excluded middle.

\begin{code}
DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇) → is-subsingleton P → ¬¬ P → P

neg-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇) → is-subsingleton (¬ X)

emsanity : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇) → is-subsingleton P → is-subsingleton (P + ¬ P)

ne : (X : 𝓤 ̇) → ¬¬(X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤

SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇) → is-subsingleton P → Σ \(X : 𝓤 ̇) → P ⇔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="infix"></a> Operator fixities and precedences

Without the following the following list of operator precedence and
associativity (left or right), this agda file doesn't parse and is
rejected by Agda.

\begin{code}
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infixl 2 _∙_
infix  3  _⁻¹
infixr 0 _≡⟨_⟩_
infix  1 _∎
infix  4  _∼_
infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_
infix  0 _≃_
infixl 2 _●_
infixr 0 _≃⟨_⟩_
infix  1 _■
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
### <a name="howtogen"></a> How to generate the html file from the Agda source of these notes

> $ agda --html --html-highlight=code HoTT-UF-Agda.lagda

> $ mv html/HoTT-UF-Agda.tex HoTT-UF-Agda.md

> $ mv html/Universes.tex Universes.md

Then we use [jekyll](https://jekyllrb.com/) to convert the markdown
files into html.

Because this file takes a long time to type check with Agda, during
development we instead first run

> $ jekill serve

and then run the bash script `fastscript`, which uses `inotifywait` to
detect changes on this file and run a Haskell program `agdatomd.hs` to
replace code environments by markdown triple back quotes. The program
`jekyll` itself detects changes in the markdown file and automatically
regenerates the html page, so that we can preview while we develop the
notes. You will need to reload the page in your web browser.  We could
use `sed` instead of Haskell, but in practice we spent more time
figuring out how character escaping works in `sed` than writing a
Haskell program.

I wrote this mainly to myself in case I forget in the future how I
developed and generated things automatically, and in the hope that it
may be useful to other authors trying to write dissemination notes or
documentation using Agda. Or maybe a reader can tell me that there is
a better way to proceed during development.

[<sub>Table of contents ⇑</sub>](#contents)

### <a name="mlttexercisessol"></a> Solution to additional exercises

\begin{code}

succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≢ n
  IH = succ-no-fixed-point n
  γ : succ (succ n) ≢ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal e = (α , φ)
 where
  α : ℕ → ℕ
  α n = succ(e n n)
  φ : (n : ℕ) → α ≢ e n
  φ n p = succ-no-fixed-point (e n n) q
   where
    q = succ (e n n)  ≡⟨ refl (α n) ⟩
        α n           ≡⟨ ap (λ - → - n) p ⟩
        e n n         ∎

cantors-diagonal (e , γ) = c
 where
  α :  ℕ → ℕ
  α = pr₁ (positive-cantors-diagonal e)
  φ : (n : ℕ) → α ≢ e n
  φ = pr₂ (positive-cantors-diagonal e)
  b : Σ \(n : ℕ) → α ≡ e n
  b = γ α
  c : 𝟘
  c = φ (pr₁ b) (pr₂ b)

Up-induction 𝓥 X A φ (up x) = φ x

Up-recursion 𝓥 {X} {B} = Up-induction 𝓥 X (λ _ → B)

down = Up-recursion _ id

down-up = refl

up-down {𝓤} {𝓥} {X} = Up-induction 𝓥 X
                        (λ l → up (down l) ≡ l)
                        (λ x → up (down {𝓤} {𝓥} (up x)) ≡⟨ ap up (down-up {𝓤} {𝓥}x) ⟩
                               up x                      ∎)

Up-left-≃ {𝓤} {𝓥} {𝓦} X Y e = Up 𝓦 X ≃⟨ Up-≃ X ⟩
                                X    ≃⟨ e ⟩
                                Y    ■

ap-Up-≃ {𝓤} {𝓥} {𝓦} {𝓣} X Y e = Up 𝓦 X  ≃⟨ Up-left-≃ X Y e ⟩
                                 Y      ≃⟨ ≃-sym (Up-≃ Y) ⟩
                                 Up 𝓣 Y ■

neg-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

emsanity fe P i (inl p) (inl q) = ap inl (i p q)
emsanity fe P i (inl p) (inr n) = !𝟘 (inl p ≡ inr n) (n p)
emsanity fe P i (inr m) (inl q) = !𝟘 (inr m ≡ inl q) (m q)
emsanity fe P i (inr m) (inr n) = ap inr (neg-is-subsingleton fe P m n)

ne X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM fe dne P i = dne (P + ¬ P) (emsanity fe P i) (ne P)

EM-gives-DNE em P i = γ (em P i)
 where
  γ : P + ¬ P → ¬¬ P → P
  γ (inl p) φ = p
  γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE {𝓤} sn P i = h
 where
  X : 𝓤 ̇
  X = pr₁ (sn P i)
  f : P → ¬ X
  f = pr₁ (pr₂ (sn P i))
  g : ¬ X → P
  g = pr₂ (pr₂ (sn P i))
  f' : ¬¬ P → ¬(¬¬ X)
  f' = contrapositive (contrapositive f)
  h : ¬¬ P → P
  h = g ∘ tno ∘ f'
  h' : ¬¬ P → P
  h' φ = g (λ (x : X) → φ (λ (p : P) → f p x))

DNE-gives-SN dne P i = (¬ P) , dni , dne P i
\end{code}

[<sub>Table of contents ⇑</sub>](#contents)
