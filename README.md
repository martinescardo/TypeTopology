# TypeTopology

## Various new theorems in constructive univalent mathematics written in Agda

This development was started by [Martin Escardo](https://www.cs.bham.ac.uk/~mhe/) at around 2010 as an `svn` project, and
transferred to `github` Monday 5th February 2018.

## Table of contents

 1. [About](#about)
 1. [Official html rendering of the Agda code](http://www.cs.bham.ac.uk/~mhe/TypeTopology/index.html)
 1. [Alternative html rendering](https://pdmosses.github.io/TypeTopology) by [Peter Mosses](https://pdmosses.github.io/)
 1. [Search](https://www.cs.bham.ac.uk/~mhe/TypeTopologySearch.html) for a name, a fragment of one, a concept, a definition, or a contributor, including wildcards
 1. [Emacs search command](https://github.com/martinescardo/TypeTopologySearch/blob/main/README.md) for TypeTopology
 1. [Module descriptions](https://github.com/martinescardo/TypeTopologyModuleDescriptions)
 1. [How to cite this repository](https://github.com/martinescardo/TypeTopology/blob/master/README.md#how-to-cite)
 1. [Root Agda files](https://github.com/martinescardo/TypeTopology/blob/master/README.md#root-agda-files)
 1. [Installation](https://github.com/martinescardo/TypeTopology/blob/master/README.md#installation)
 1. [Checking the development](https://github.com/martinescardo/TypeTopology/blob/master/README.md#checking-the-development)
 1. [Academic publications and preprints resulting from TypeTopology](https://github.com/martinescardo/TypeTopology#academic-publications-and-preprints-resulting-from-typetopology)
 1. [Current contributors](https://github.com/martinescardo/TypeTopology/blob/master/README.md#current-typetopology-contributors-in-alphabetical-order-of-first-name)
 1. [Statement of inclusion](https://github.com/martinescardo/TypeTopology/blob/master/STATEMENT-OF-INCLUSION.md)
 1. [Code of conduct](https://github.com/martinescardo/TypeTopology/blob/master/CODE-OF-CONDUCT.md)
 1. [Contributing](https://github.com/martinescardo/TypeTopology/blob/master/CONTRIBUTING.md)
 1. [Your contribution is your own](https://github.com/martinescardo/TypeTopology/blob/master/AI-Policy.md)

## About

TypeTopology is a blackboard, for working on new mathematics, rather than being an encyclopedia of existing mathematics. As a result, its organization differs considerably from other formalization developments, both in Agda and in other proof assistants.

The purpose of TypeTopology is to be a playground to work on new ideas we want to submit for publication, and to explain mathematics to people, not only to computers.

This leads to a fundamentally different organization of our ideas, as recorded in our Agda files here, compared to other existing developments that record mathematical knowledge.

But, of course, we are also happy for already-existing mathematical ideas to be recorded here. In fact, they may be very useful for developing our own new ideas. Or your own. We are happy for you to join us using TypeTopology as either a blackboard or as record of already-existing mathematical ideas.

The name TypeTopology was chosen both because of the well-known [connection of topology with constructive mathematics](https://doi.org/10.1093/oso/9780198537359.003.0005) and because homotopy theory is a branch of topology.

TypeTopology is distributed under the [GPL-3](LICENSE) license.

## How to cite

You can use the following BibTeX entry to cite `TypeTopology`:

```bibtex
@misc{type-topology,
  title    = {{TypeTopology}},
  author   = {Escard\'{o}, Mart\'{i}n H. and {contributors}},
  url      = {https://github.com/martinescardo/TypeTopology},
  note     = {{Agda} development},
}
```

If you are citing only files written by particular contributors, then use a
different BibTeX entry, with them as the authors and the url field pointing to
those files.

TypeTopology is indexed by [zbMATH Open](https://zbmath.org/software/53728),
which also lists the publications that cite it.

## Root Agda files

 * [source/index.lagda](source/index.lagda) hereditarily imports all [`--safe`](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-safe) modules.
 * [source/AllModulesIndex.lagda](source/AllModulesIndex.lagda) hereditarily imports all modules, including the unsafe ones.
 * Each subdirectory in [source/](source/) has its own index file.

The adopted Agda [flags](https://agda.readthedocs.io/en/latest/tools/command-line-options.html) are listed in [typetopology.agda-lib](typetopology.agda-lib), and the adopted [Mikan](https://codeberg.org/1lab/mikan) flags in [typetopology.mikan-lib](typetopology.mikan-lib).

## Installation

The only dependency is [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html),
version 2.8.0 or 2.9.0. The [Agda standard library](https://github.com/agda/agda-stdlib) is not needed.

## Checking the development

To type-check every module, run

```
agda AllModulesIndex.lagda
```

from the directory [source](source), or use the [Makefile](Makefile) at
the root, whose targets are explained by `make help`. The
[GitHub action](.github/workflows/main.yml) does this on every push and
pull request. The safe part of the development can also be checked with
[Mikan](https://codeberg.org/1lab/mikan), by running

```
mikan index.lagda
```

from the directory [source](source), in which case the flags listed in
[typetopology.mikan-lib](typetopology.mikan-lib) are used instead. A
[second GitHub action](.github/workflows/mikan.yml) does this on every
push and pull request too. At present, the use of Mikan is a double
check.

## Academic publications and preprints resulting from TypeTopology

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Infinite sets that satisfy the principle of
   omniscience in any variety of constructive mathematics.* [The
   Journal of Symbolic
   Logic](https://www.cambridge.org/core/journals/journal-of-symbolic-logic),
   Volume 78 , Issue 3 , 2013 , pp. 764 - 784.

   https://doi.org/10.2178/jsl.7803040

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Continuity of Gödel's system T definable functionals via
   effectful forcing.* [Electronic Notes in Theoretical Computer
   Science](https://www.sciencedirect.com/journal/electronic-notes-in-theoretical-computer-science),
   Volume 298, 2013, Pages 119-141. [MFPS XXIX](https://www.cs.cornell.edu/Conferences/MFPS29/)

   https://doi.org/10.1016/j.entcs.2013.09.010

1. [Nicolai Kraus](https://nicolaikraus.github.io/), [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/), [T. Coquand](https://www.chalmers.se/en/persons/coquand/),
   [T. Altenkirch](https://people.cs.nott.ac.uk/psztxa/). *Generalizations of Hedberg's Theorem.* In: Hasegawa,
   M. (eds) Typed Lambda Calculi and Applications. [TLCA
   2013](https://www.kurims.kyoto-u.ac.jp/tlca2013/). Lecture Notes in
   Computer Science, vol 7941. Springer.

   https://doi.org/10.1007/978-3-642-38946-7_14

1. [Chuangjie Xu](https://cj-xu.github.io/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *A constructive model of uniform continuity.* TLCA 2013.

   https://doi.org/10.1007/978-3-642-38946-7_18

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Constructive decidability of classical continuity.*
   [Mathematical Structures in Computer Science][MSCS], Volume 25, Special
   Issue 7: Computing with Infinite Data: Topological and Logical Foundations
   Part 1, October 2015, pp. 1578 - 1589 DOI:

   https://doi.org/10.1017/S096012951300042X

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and [Chuangjie Xu](https://cj-xu.github.io/). *A constructive manifestation of
   the Kleene-Kreisel continuous functionals.* Annals of Pure and
   Applied Logic 167(9), 2016.

   https://doi.org/10.1016/j.apal.2016.04.011


1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and [Chuangjie Xu](https://cj-xu.github.io/). *The inconsistency of a
   Brouwerian continuity principle with the Curry-Howard
   interpretation.* [13th International Conference on Typed Lambda
   Calculi and Applications (TLCA 2015)](https://drops.dagstuhl.de/opus/portals/lipics/index.php?semnr=15006).

   https://doi.org/10.4230/LIPIcs.TLCA.2015.153


1. [Chuangjie Xu](https://cj-xu.github.io/). *A Continuous Computational Interpretation of Type Theories*.
   PhD thesis, School of Computer Science, University of
   Birmingham, UK, 2015.

   https://etheses.bham.ac.uk/id/eprint/5967/ \
   https://cj-xu.github.io/ContinuityType/xu-thesis.pdf

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and [T. Streicher](https://www2.mathematik.tu-darmstadt.de/~streicher/). *The intrinsic topology of
   Martin-Löf universes.* [Annals of Pure and Applied
   Logic](https://www.sciencedirect.com/journal/annals-of-pure-and-applied-logic),
   Volume 167, Issue 9, 2016, Pages 794-805.

   https://doi.org/10.1016/j.apal.2016.04.010

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and Cory Knapp. *Partial elements and recursion via
   dominances in univalent type theory.* [Leibniz International Proceedings in
   Informatics
   (LIPIcs)][LIPICS],
   Proceedings of [CSL
   2017](https://www.math-stockholm.se/konferenser-och-akti/logic-in-stockholm-2/26th-eacsl-annual-co/computer-science-logic-2017-august-20-24-1.717663).

   https://doi.org/10.4230/LIPIcs.CSL.2017.21

1. [Nicolai Kraus](https://nicolaikraus.github.io/), [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/), [T. Coquand](https://www.chalmers.se/en/persons/coquand/), [T. Altenkirch](https://people.cs.nott.ac.uk/psztxa/). *Notions of
   Anonymous Existence in Martin-Löf Type Theory.*  [Logical Methods in
   Computer Science][LMCS], March 24, 2017, Volume 13, Issue 1.

   https://doi.org/10.23638/LMCS-13(1:15)2017

1. [Brendan Hart](https://github.com/BrendanHart). *Investigating properties of PCF in Agda.* MSci dissertation, School of Computer Science, University of Birmingham, UK, 2020.

   https://github.com/BrendanHart/Investigating-Properties-of-PCF/blob/master/InvestigatingPropertiesOfPCFInAgda.pdf \
   https://github.com/BrendanHart/Investigating-Properties-of-PCF \
   https://www.cs.bham.ac.uk/~mhe/TypeTopology/PCF.Lambda.index.html

1. [Tom de Jong](https://tdejong.com/). *The Scott model of PCF in univalent type theory.*
   [Mathematical Structures in Computer
   Science](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science),
   Volume 31, Issue 10 - Homotopy Type Theory 2019, July 2021.

   https://doi.org/10.1017/S0960129521000153

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *The Cantor-Schröder-Bernstein Theorem for
   ∞-groupoids.*  [Journal of Homotopy and Related
   Structures](https://tcms.org.ge/Journals/JHRS/), 16(3), 363-366,
   2021.

   https://doi.org/10.1007/s40062-021-00284-6

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/).  *Injective types in univalent
   mathematics.* [Mathematical Structures in Computer
   Science](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science),
   Volume 31 , Issue 1 , 2021 , pp. 89 - 111.

   https://doi.org/10.1017/S0960129520000225

1. [Tom de Jong](https://tdejong.com/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Domain Theory in Constructive
   and Predicative Univalent Foundations.* [Leibniz International
   Proceedings in Informatics
   (LIPIcs)](https://www.dagstuhl.de/en/publishing/series/details/LIPIcs),
   Volume 183 - Proceedings of [CSL 2021][CSL21], January
   2021.

   https://doi.org/10.4230/LIPIcs.CSL.2021.28

1. [Dan R. Ghica](https://www.birmingham.ac.uk/staff/profiles/computer-science/academic-staff/ghica-dan) and [Todd Waugh Ambridge](https://www.cs.bham.ac.uk/~txw467/). *Global Optimisation with
   Constructive Reals.*
   [Logic in Computer Science (LICS)](https://dl.acm.org/conference/lics),
   Proceedings of [LICS 2021][LICS21], June 2021.

   https://doi.org/10.1109/LICS52264.2021.9470549

1. [Tom de Jong](https://tdejong.com/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Predicative Aspects of Order
   Theory in Univalent Foundations.* [Leibniz International Proceedings
   in Informatics
   (LIPIcs)](https://www.dagstuhl.de/en/publishing/series/details/LIPIcs),
   Volume 195 - Proceedings of [FSCD 2021][FSCD21], July 2021.

   https://doi.org/10.4230/LIPIcs.FSCD.2021.8

1. [Tom de Jong](https://tdejong.com/). *Domain Theory in Constructive and Predicative Univalent
   Foundations*. PhD thesis. School of Computer Science, University of
   Birmingham, UK. Submitted: 30 September 2022; accepted: 1 February 2023.

   https://etheses.bham.ac.uk/id/eprint/13401/ \
   Updated versions: \
   https://arxiv.org/abs/2301.12405 \
   https://tdejong.com/writings/phd-thesis.pdf

1. [Ayberk Tosun](https://ayberkt.xyz/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Patch Locale of a Spectral
   Locale in Univalent Type Theory.* [Electronic Notes in Theoretical
   Informatics and Computer Science](https://entics.episciences.org/),
   Volume 1 - Proceedings of [MFPS XXXVIII][MFPS38], February
   2023.

   https://doi.org/10.46298/entics.10808

1. [Tom de Jong](https://tdejong.com/), [Nicolai Kraus](https://nicolaikraus.github.io/), [Fredrik Nordvall Forsberg](https://fredriknf.com/) and
   [Chuangjie Xu](https://cj-xu.github.io/). *Set-Theoretic and Type-Theoretic Ordinals Coincide.*
   [Logic in Computer Science (LICS)](https://dl.acm.org/conference/lics),
   Proceedings of [LICS 2023][LICS23]. June 2023.

   https://doi.org/10.1109/LICS56636.2023.10175762 \
   https://arxiv.org/abs/2301.10696

1. [Tom de Jong](https://tdejong.com/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *On Small Types in Univalent
   Foundations.* [Logical Methods in Computer
   Science](https://lmcs.episciences.org/), Volume 19, Issue 2, May
   2023.

   https://doi.org/10.46298/lmcs-19(2:8)2023

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and [Paulo Oliva](https://paulooliva.github.io/). *Higher-order Games with
   Dependent Types*. [Theoretical Computer
   Science](https://www.sciencedirect.com/journal/theoretical-computer-science),
   Special issue "Continuity, Computability, Constructivity: From
   Logic to Algorithms", dedicated to Ulrich Berger's 65th birthday,
   volume 974, 29 September 2023, available online 2 August 2023.

   https://doi.org/10.1016/j.tcs.2023.114111

1. [Ian Ray](https://ianray11.github.io/). *Tarski's least fixed point theorem: A predicative type theoretic
   formulation*. January 2024.

   https://doi.org/10.48550/arXiv.2401.00841

1. [Todd Waugh Ambridge](https://www.cs.bham.ac.uk/~txw467/). *Exact Real Search: Formalised Optimisation and
   Regression in Constructive Univalent Mathematics.* January 2024. University
   of Birmingham. PhD thesis.

   https://etheses.bham.ac.uk/id/eprint/14662/ \
   https://doi.org/10.48550/arXiv.2401.09270

1. [Tom de Jong](https://tdejong.com/). *Domain theory in univalent foundations I: Directed complete
   posets and Scott's D∞*. July 2024.

   https://doi.org/10.48550/arxiv.2407.06952

1. [Tom de Jong](https://tdejong.com/), [Nicolai Kraus](https://nicolaikraus.github.io/), [Fredrik Nordvall Forsberg](https://fredriknf.com/) and [Chuangjie Xu](https://cj-xu.github.io/).
   *Ordinal Exponentiation in Homotopy Type Theory*.
   [Logic in Computer Science (LICS)](https://dl.acm.org/conference/lics),
   Proceedings of [LICS 2025][LICS25]. October 2025.

   https://doi.org/10.1109/LICS65433.2025.00027 \
   https://arxiv.org/abs/2501.14542v4

1. [Martin H. Escardo](https://www.cs.bham.ac.uk/~mhe/), [Bruno da Rocha Paiva](https://brunorochapaiva.github.io/), [Vincent Rahli](https://www.cs.bham.ac.uk/~rahliv/) and [Ayberk Tosun](https://ayberkt.xyz/).
   *Internal Effectful Forcing in System T*. [FSCD'2025](https://fscd2025.github.io/).

   https://doi.org/10.48550/arXiv.2505.11055

1. [Ayberk Tosun](https://ayberkt.xyz/). *Constructive and Predicative Locale Theory in Univalent
   Foundations*. PhD thesis. School of Computer Science, University of
   Birmingham, UK. Submitted: 30 November 2024; accepted: 3 June 2025.

   https://etheses.bham.ac.uk/id/eprint/16416/
   Updated versions: \
   https://arxiv.org/abs/2603.01308

1. [Igor Arrieta](https://sites.google.com/view/igorarrieta), [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/) and [Ayberk Tosun](https://ayberkt.xyz/). *The Patch Topology in
   Univalent Foundations*. [Mathematical Structures in Computer Science][MSCS],
   Volume 35, Special Issue: Advances in Homotopy Type Theory.
   August 2025.

   https://doi.org/10.1017/S0960129525000088

1. [Tom de Jong](https://tdejong.com/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Continuous and algebraic domains in
   univalent foundations*. [Journal of Pure and Applied Algebra][JPAA], Volume
   229, Issue 10. August 2025. \
   As requested by the journal, this publication
   includes an abridged version of the paper *Domain theory in univalent
   foundations I*.

   https://doi.org/10.1016/j.jpaa.2025.108072

1. [Tom de Jong](https://tdejong.com/) and [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Examples and counterexamples of
   injective types*. January 2026, accepted for publication in
   Ann. Pure Appl. Logic 30th August 2026.

   https://doi.org/10.48550/arxiv.2601.12536
   https://doi.org/10.1016/j.apal.2026.103829

1. [Anna Williams](https://anna-maths.xyz/). *Formalising Displayed Categories with Univalent Foundations*.
   MSci project, School of Computer Science, University of Birmingham, UK, 2026.

   https://anna-maths.xyz/assets/papers/disp-categories.pdf

1. [Martín H. Escardó](https://www.cs.bham.ac.uk/~mhe/). *Compact totally separated types*, preprint, 9th September 2026.

   https://arxiv.org/abs/2609.10447

   Agda companion.
   https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.CompactTotallySeparatedTypesArticle.html

1. [Tom de Jong](https://tdejong.com/), [Nicolai Kraus](https://nicolaikraus.github.io/), [Fredrik Nordvall Forsberg](https://fredriknf.com/) and
   [Chuangjie Xu](https://cj-xu.github.io/). *Construtive Ordinal Exponentiation*. September 2025, accepted for
   publication in the [Journal of the ACM][JACM] 2nd October 2026. \
   This is an invited, expanded journal version of the LICS paper *Ordinal
   Exponentiation in Homotopy Type Theory*.

   https://arxiv.org/abs/2501.14542v6

[CSL21]:  https://csl2021.fmf.uni-lj.si/
[FSCD21]: https://fscd2021.dc.uba.ar/
[LICS21]: https://easyconferences.eu/lics2021/
[LICS23]: https://lics.siglog.org/lics23/
[LICS25]: https://lics.siglog.org/lics25/
[MFPS38]: https://www.cs.cornell.edu/mfps-2022/
[LMCS]: https://lmcs.episciences.org/
[MSCS]: https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science
[LIPICS]: https://www.dagstuhl.de/en/publishing/series/details/LIPIcs
[JPAA]: https://www.sciencedirect.com/journal/journal-of-pure-and-applied-algebra
[JACM]: https://dl.acm.org/journal/jacm/

## Current TypeTopology contributors in alphabetical order of first name

Please add yourself the first time you contribute. Use your adopted name, and not necessarily your given name, at your discretion.

* [Alex Rice](https://alexarice.github.io/)
* [Alice Laroche](https://github.com/alicelaroche)
* [Andrew Sneap](https://github.com/adsneap)
* [Andrew Swan](https://awswan.github.io/)
* [Anna Williams](https://anna-maths.xyz/)
* [Ayberk Tosun](https://ayberkt.xyz/)
* [Brendan Hart](https://github.com/BrendanHart)
* [Bruno Paiva](https://brunorochapaiva.github.io/)
* [Carlo Angiuli](https://carloangiuli.com/)
* [Chuangjie Xu](https://cj-xu.github.io/)
* [Cory Knapp](https://github.com/cmknapp)
* [Ettore Aldrovandi](https://www.math.fsu.edu/~ealdrov/)
* [Evan Cavallo](https://ecavallo.net/)
* [Fredrik Bakke](https://fredrik-bakke.github.io/forest/)
* [Fredrik Nordvall Forsberg](https://fredriknf.com/)
* [Ian Ray](https://ianray11.github.io/)
* [Igor Arrieta](https://sites.google.com/view/igorarrieta) (ii)
* [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/)
* [J. A. Carr](https://github.com/jasoncarr0)
* [Jakub Opršal](https://jakub-oprsal.info/)
* [Jon Sterling](https://www.jonmsterling.com/)
* [Kelton OBrien](https://keltono.net/)
* [Keri D'Angelo](https://github.com/keridangelo)
* [Lane Biocini](https://github.com/biocini)
* [Marc Bezem](https://www4.uib.no/en/find-employees/marc.bezem)
* [Martin Escardo](https://www.cs.bham.ac.uk/~mhe/)
* [Mike Shulman](https://home.sandiego.edu/~shulman/)
* [Nicolai Kraus](https://nicolaikraus.github.io/)
* [Ohad Kammar](https://denotational.co.uk/)
* [Paul Levy](https://pblevy.github.io/) (i)
* [Paulo Oliva](https://paulooliva.github.io/)
* [Peter Dybjer](https://www.chalmers.se/en/persons/peterd/)
* [Simcha van Collem](https://simchavc.github.io/)
* [Thierry Coquand](https://www.chalmers.se/en/persons/coquand/)
* [Todd Waugh Ambridge](https://www.cs.bham.ac.uk/~txw467/)
* [Tom de Jong](https://tdejong.com/)
* [Ulrik Buchholtz](https://ulrikbuchholtz.dk/)
* [Vincent Rahli](https://www.cs.bham.ac.uk/~rahliv/)

(i) These authors didn't write any single line of Agda code here, but
they contributed to constructions, theorems and proofs via the hands
of [Martin Escardo](https://www.cs.bham.ac.uk/~mhe/).

(ii) These authors didn't write single line of Agda code here, but they
contributed to constructions, theorems and proofs via the hands of
[Ayberk Tosun](https://ayberkt.xyz/).
