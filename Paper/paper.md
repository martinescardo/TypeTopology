---
title: 'TypeTopology: a blackboard for research in constructive univalent mathematics'
tags:
  - Agda
  - univalent foundations
  - homotopy type theory
  - constructive mathematics
  - formalization of mathematics
authors:
  - name: Martín Hötzel Escardó
    orcid: 0000-0002-4091-6334
    affiliation: 1
    corresponding: true
  - given-names: Tom
    non-dropping-particle: de
    surname: Jong
    orcid: 0000-0003-1585-3172
    affiliation: 2
  - name: Ayberk Tosun
    orcid: 0000-0002-0190-3020
    affiliation: 3
  - name: Chuangjie Xu
    orcid: 0000-0001-6838-4221
    affiliation: 4
  - given-names: Todd
    surname: Waugh Ambridge
    orcid: 0009-0000-1796-6707
    affiliation: 1
affiliations:
  - name: School of Computer Science, University of Birmingham, United Kingdom
    index: 1
  - name: Institute for Computing and Information Sciences, Radboud University, The Netherlands
    index: 2
  - name: Zeroth Research, United Kingdom (affiliated with **1** for the work described here)
    index: 3
  - name: Independent researcher
    index: 4
date: 13 November 2026
bibliography: paper.bib
---

# Summary

`TypeTopology` is a constructive development of univalent mathematics
and homotopy type theory [@hottbook] written in Agda [@agda], started
in 2010 and public since 2018. It currently has 1017 Agda files with
306K lines of code and comments, organized in about sixty subject
directories, and it is checked with Agda 2.8.0 and 2.9.0. Among the
mathematics it develops are the intrinsic topology of types [@Escardo2013;
@EscardoStreicher2016; @Escardo2026compact], injective types and their
algebraic structure [@Escardo2021injective;
@deJongEscardo2026injective], domain theory, [@deJongEscardo2021domains;
@deJongEscardo2025domains], ordinals and their arithmetic
[@deJongKrausNordvallForsbergXu2023;
@deJongKrausNordvallForsbergXu2026], locale theory
[@ArrietaEscardoTosun2025], the Dedekind reals, models of set theory,
higher-order games [@EscardoOliva2023], and effectful forcing
[@EscardoRochaPaivaRahliTosun2025]. Four doctoral theses were written
on material developed here, and their formalizations are part of
`TypeTopology`, namely Chuangjie Xu's continuous computational
interpretation of type theories [@Xu2015thesis], Tom de Jong's domain
theory in constructive and predicative univalent foundations
[@deJong2023thesis], Todd Waugh Ambridge's exact real search, with
optimization and regression over exact real numbers
[@Ambridge2024thesis], and Ayberk Tosun's constructive and predicative
locale theory [@Tosun2025thesis]. The name `TypeTopology` was chosen
both because of the well-known connection of topology with constructive
mathematics [@Smyth1992] and because homotopy theory is a branch of
topology. The version described here is archived at
[@TypeTopologyArchive].

# Statement of need

We wrote `TypeTopology` for mathematicians, logicians and computer
scientists working in homotopy type theory and univalent foundations,
with three goals in mind.

The first is a place to do new mathematics rather than to record
mathematics already done. We use the development as a blackboard in
which results appear and are discussed by the community before they are
submitted for publication. Currently 35 publications and preprints have
resulted from `TypeTopology`. A library organized as an encyclopedia of
settled mathematics cannot play this role, because an encyclopedia
records mathematics after it is understood, whereas a blackboard is
where this understanding is developed. The blackboard material
nevertheless evolves into a body of mathematics that others build on,
organized by subject.

The second is mathematical exposition. The code is accompanied by
extensive prose that explains the mathematics, discusses the choices
made, and records what is known and what is open, so that a module can
be read as a mathematical text. This is something readers and users of
`TypeTopology` most often tell us they value.

The third is precision about assumptions. Postulates are not allowed in
`TypeTopology`, with the exception of a small experimental fragment,
briefly discussed under _Software design_ below. Function
extensionality, propositional extensionality, the existence of
propositional truncations, univalence, propositional resizing, and the
principles of classical mathematics such as excluded middle, choice,
global choice, LPO and WLPO, are all stated as explicit
hypotheses of the theorems, or of the modules, that need them. A reader
can therefore tell from the statement of a result exactly which
assumptions it depends on, and we can tell which of our theorems are
constructive and which are classical. Resizing is of particular
interest, since its avoidance is what keeps the development predicative
[@deJongEscardo2023small].

# State of the field

Five actively maintained libraries of univalent mathematics are
comparable in scope.

The `UniMath` library [@UniMath] is written in `Rocq` [@rocq],
formerly `Coq`, and goes back to Voevodsky [@Voevodsky2015]. It is
built with the `-type-in-type` option, which makes the system
inconsistent, and it assumes propositional resizing. Their own
documentation records a succession of attempts to introduce resizing
rules in order to avoid that option. We avoid propositional
resizing to remain predicative.

The `HoTT` library [@Coq-HoTT-CPP] is also written in Rocq, goes back
to 2011, and has homotopy theory as its main subject. It is the closest
to `TypeTopology` in its treatment of assumptions, since function
extensionality, univalence and propositional resizing are axioms that a
definition can use only by taking them as explicit hypotheses, so that
their use is tracked. Higher inductive types, including propositional
truncation, are built into the library with private inductive types
and axioms (postulates). The use of the latter in theorems can be
tracked using Rocq's `Print Assumptions` command.

The `agda-unimath` library [@agdaunimath] is written in Agda, as
`TypeTopology` is, and is organized as an encyclopedia by mathematical
subject. Its design principles record that it postulates function
extensionality, univalence, the replacement axiom, the truncation
operations, the interval, the circle, pushouts, extensionality of
globular types, and the flat modality with propositional computation
rules. Mathematics that needs excluded middle or choice is, by their
own account, not yet developed there. `TypeTopology`, on the other
hand, does not allow postulates, and studies classical principles
deliberately, including the Cantor-Schröder-Bernstein theorem for
arbitrary homotopy types under excluded middle, Zorn's lemma, the
well-ordering principle, and a collection of taboos that measure how
much classical logic a statement needs.

The `Cubical` library [@CubicalLibrary] is the standard library for
Cubical Agda [@VezzosiMortbergAbel2021], an implementation of cubical
type theory. In this library, univalence, function extensionality and
the existence of higher inductive types all hold by construction. In
`TypeTopology`, these are hypotheses of the theorems that use them.

The `1Lab` [@onelab] is a cross-linked reference resource for
mathematics done in homotopy type theory, with category theory as its
largest part. It is written in Mikan [@Mikan], a fork of Agda made by
its developers to support cubical type theory alone. The above remarks
about the `Cubical` library also apply.

# Software design

We deliberately work in a minimal version of intensional Martin-Löf
type theory, which we call Spartan MLTT, and in a correspondingly
minimal subset of Agda, which means that, in particular, we do not use
Cubical Agda. The flags in `typetopology.agda-lib` fix the type theory
as far as Agda at present allows, and they include, among others,
`--without-K` to make the development compatible with homotopy type
theory and univalent foundations. The development is indexed by
`source/index.lagda`, which hereditarily imports every module that
Agda can check as safe, and `source/AllModulesIndex.lagda` adds a few
experimental modules that go beyond Martin-Löf type theory and
univalent foundations. We define everything starting from Spartan MLTT
rather than build on the Agda standard library [@agdastdlib], which
serves the different purpose of supporting programming and proving in
Agda at large, so Agda alone is needed to check the development.

The axioms required by a construction are hypotheses of its
definition, or parameters of the module that collects them. We adopt
the univalent point of view even in modules that assume no axioms,
taking seriously the distinction between types that are singletons,
propositions, sets, 1-groupoids, etc., and a large part of the
development needs no axioms. We prefer Σ types to records, because
univalent foundations supplies constructions and theorems for Σ types
that we constantly apply.

# Research impact statement

Currently 35 publications and preprints have arisen from `TypeTopology`,
in the *Journal of Symbolic Logic*, *Mathematical Structures in Computer
Science*, the *Annals of Pure and Applied Logic*, the *Journal of Pure
and Applied Algebra*, *Logical Methods in Computer Science*, the
*Journal of Homotopy and Related Structures*, and the proceedings of
LICS, CSL, FSCD, TLCA and MFPS, by the authors and `TypeTopology`
contributors, and the four doctoral theses named in the summary were
written on material developed here. `TypeTopology` also has an entry in
zbMATH Open [-@zbmathTypeTopology], which records the publications that
cite it. Material from `TypeTopology` is also being reproduced in other
developments, for example the theory of compact and searchable types in
the `HoTT` library. `TypeTopology` is also used for teaching,
incorporating the material of our Midlands Graduate School lecture
notes [@Escardo2019notes].

# Testing

Running `agda AllModulesIndex.lagda` from the directory `source`
type-checks every module, and the `Makefile` at the root does this with
the released or the development version of Agda. A GitHub action runs
the same check on every push and pull request. All safe modules are
hereditarily imported by `source/index.lagda` and carry the option
`--safe`, which rules out postulates, so a successful check is a
computer verification that every theorem in them follows from the
assumptions its statement declares. The safe fragment of
`TypeTopology` is additionally checked with Mikan (ignoring its cubical
features), as a double check.

# AI usage disclosure

`TypeTopology`'s file `AI-Policy.md` states that *"TypeTopology
consists of literate Agda files that contain Agda code as well as
accompanying prose. We will not consider AI generated Agda code or
prose."* Regarding this paper, we wrote it from prose already
available in `TypeTopology`, using AI assistance to bring it to the
markdown format required by this journal.

# Acknowledgements

`TypeTopology` has around forty contributors, listed in the README at
GitHub. The authors of this paper are listed by amount of contribution
to the development.

While working on `TypeTopology`, Tom de Jong received funding through
the *Homotopy Type Theory Dissertation Fellowship*, funded by
Cambridge Quantum Computing and Ilyas Khan, as well as the Royal
Society \[URF\\R1\\191055, URF\\R\\241007\].

# References
