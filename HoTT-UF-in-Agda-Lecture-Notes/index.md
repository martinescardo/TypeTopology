---
layout: default
title : Introduction to Univalent Foundations of Mathematics with Agda
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

4th March 2019, draft version of {{ "now" | date: "%d %B %Y, %H:%M" }}.

[Martín Hötzel Escardó](http://www.cs.bham.ac.uk/~mhe/), University of Birmingham, UK.

[<sub>Table of contents ⇓</sub>](toc.html#contents)

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
tools. [Github](https://github.com/martinescardo/TypeTopology) pull
requests by students to fix typos or mistakes and clarify ambiguities
are welcome.

These notes were originally developed for the
[Midlands Graduate School 2019](http://events.cs.bham.ac.uk/mgs2019/).

[<sub>Table of contents ⇓</sub>](toc.html#contents)
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
univalence as an explicit assumption each time it is needed. We will
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

[<sub>Table of contents ⇓</sub>](toc.html#contents)
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

A common compromise is to refer to the subject as [HoTT/UF](https://cas.oslo.no/hott-uf/).

[<sub>Table of contents ⇓</sub>](toc.html#contents)
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
   - Agda [further references](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation).
   - [Cubical Agda blog post](https://homotopytypetheory.org/2018/12/06/cubical-agda/).
   - [Cubical Agda documentation](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical).

We have based these lecture notes
on the slides of our talk [*logic in univalent type theory*](https://www.newton.ac.uk/seminar/20170711100011001).

[<sub>Table of contents ⇓</sub>](toc.html#contents)
### <a name="plan"></a> Choice of material

This is intended as an introductory graduate course. We include what
we regard as the essence of univalent foundations and univalent
mathematics, but we are certainly ommiting important material that is
needed to do univalent mathematics in practice, and the readers who wish
to practice univalent mathematics should consult the above references.

[<sub>Table of contents ⇓</sub>](toc.html#contents) [<sub>MLTT in Agda ⇓</sub>](MLTT-Agda.html)
