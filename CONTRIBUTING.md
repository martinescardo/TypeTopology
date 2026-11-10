# Contributing to TypeTopology

TypeTopology is a blackboard for doing new mathematics in [univalent
foundations](https://homotopytypetheory.org/book/), written in [Agda](https://agda.readthedocs.io/en/latest/), and we welcome contributions to it, from
academics and non-academics alike. The best guide to our conventions
is the development itself, so read a few files in the directory you
are contributing to before you write your own.

## Table of contents

 1. [Before you start](#before-you-start)
 1. [What we ask of every contribution](#what-we-ask-of-every-contribution)
 1. [Keep every proof](#keep-every-proof)
 1. [Explain the mathematics to people](#explain-the-mathematics-to-people)
 1. [Markdown in the prose](#markdown-in-the-prose)
 1. [The preamble of a module](#the-preamble-of-a-module)
 1. [Names](#names)
 1. [Suggested Emacs input sequences](#suggested-emacs-input-sequences)
 1. [Type theory and notation](#type-theory-and-notation)
 1. [Proofs](#proofs)
 1. [Layout](#layout)
 1. [Checking your work](#checking-your-work)
 1. [Module descriptions](#module-descriptions)
 1. [Pull requests](#pull-requests)
 1. [Reporting problems and asking for help](#reporting-problems-and-asking-for-help)
 1. [Code of conduct, inclusion, AI policy and license](#code-of-conduct-inclusion-ai-policy-and-license)

## Before you start

 1. A first contribution goes to the directory [source/gist](https://www.cs.bham.ac.uk/~mhe/TypeTopology/gist.index.html),
    and once it is accepted we allocate it an appropriate place in the
    development, together with you. This holds both for new mathematics
    and for existing mathematics that the development lacks, which we
    need plenty of in order to do the new things we want to do.

 1. Ask before changing anything in a file written by somebody else,
    and before making a pull request that touches it. The material may
    be part of a paper in preparation.

 1. Search the development before defining a notion or proving a lemma.
    The [search page](https://www.cs.bham.ac.uk/~mhe/TypeTopologySearch.html)
    finds names, fragments of names, concepts and definitions, there is
    an [Emacs command](https://github.com/martinescardo/TypeTopologySearch)
    that does the same, the
    [module descriptions](https://github.com/martinescardo/TypeTopologyModuleDescriptions)
    say what each module is about, and the index file of each
    directory gives an overview of its contents. A notion often has a
    name here that differs from the one in the literature, so search
    for the shape of a type as well as for a name.

## What we ask of every contribution

 1. Your name, which can be your given name or your adopted name, at
    your discretion, and the date go at the place of contribution. A
    new file starts with them, on its first line. An addition in the
    middle of somebody else's file is marked with "Added by name on
    date" before it and "End of addition" after it, as in
    [UF.Logic](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Logic.html). The first time you
    contribute, add yourself to the list of contributors in the
    [README](README.md). We want everybody who contributes to get
    explicit credit, and we want a visible historical record, in
    addition to the github commit history.

 1. Every new file is imported by the index file of its directory, and
    every new directory has an index file imported by the index of its
    parent, as in [DomainTheory.index](https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.index.html). This makes sure that the [GitHub action](.github/workflows/main.yml) checks every file,
    and that a reader of the
    [html rendering](https://www.cs.bham.ac.uk/~mhe/TypeTopology/index.html)
    can reach every file from the root index.

 1. Use the import check script
    [utilities/imports.sh](utilities/imports.sh) to make sure you
    don't have any unused imports before you do a pull request.

 1. Every module hereditarily imported from [source/index.lagda](https://www.cs.bham.ac.uk/~mhe/TypeTopology/index.html)
    must include

    ```agda
    {-# OPTIONS --safe --without-K #-}
    ```
    The option [--without-K](https://agda.readthedocs.io/en/latest/language/without-k.html) is for emphasis only,
    as it is on by default in
    [typetopology.agda-lib](typetopology.agda-lib), but
    [--safe](https://agda.readthedocs.io/en/latest/language/safe-agda.html) is mandatory
    because it is
    [coinfective](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#checking-options-for-consistency).

    A module that needs an unsafe feature goes to the directory
    [source/Unsafe](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Unsafe.index.html)
    and must be imported from its index, and should still list
    `--without-K`.

 1. [Postulates](https://agda.readthedocs.io/en/latest/language/postulates.html)
    are not allowed, other than in unsafe modules as discussed above.
    Every axiom that a result needs, whether of univalent foundations,
    of classical mathematics, or of any other kind, such as the axioms
    of synthetic topology or synthetic geometry, is a hypothesis of
    the result, or a parameter of the module that collects such
    results, so that the statement of a theorem says what it depends
    on.

 1. Everything you contribute is written by you. Our
    [AI policy](AI-Policy.md) says that we will not consider AI
    generated Agda code or prose.

    (Nevertheless, you may use TypeTopology as a library in your own
    development that uses AI, as for example the separate repository
    [DialogueTreesHeight](https://github.com/martinescardo/DialogueTreesHeight)
    does.)

 1. By contributing you agree that your contribution is released under
    the [license](LICENSE) of the development, which is [GPL-3](https://www.gnu.org/licenses/gpl-3.0.html).

## Keep every proof

We want all known proofs of a result, and not only one of them. If you
add a new proof of something already proved here, keep the previous
proof, and say in the prose how your proof differs from it or improves
on it. The same goes for a new definition of a notion that already has
one, which is added alongside the old one together with a proof that
the two agree.

## Explain the mathematics to people

The purpose of TypeTopology is to explain mathematics to people, and
not only to computers. Every file is a
[literate Agda file](https://agda.readthedocs.io/en/latest/tools/literate-programming.html),
with the extension `.lagda`, and the prose in it is written as the
prose of a paper is. Write plenty of prose, explaining the mathematics
and the choices made in the code.

 1. Say what the idea of a construction is and what the intention
    behind a definition is. "The idea is that list concatenation will
    be the group operation after suitable quotienting", in
    [Groups.Free](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Groups.Free.html), tells the reader what to expect from the next
    page of code.

 1. Say what a hypothesis is for, and, when we know, why it cannot be
    dropped.

 1. Compare the notion you define with the ones in the literature and
    in the rest of the development, and give the attributions, with
    links to the papers, as in
    [UF.Size](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html):

    > The following notion of local smallness is due to Egbert Rijke, in his
    > join-construction paper https://arxiv.org/abs/1701.07538.

    A list of references cited in the prose by number is also fine, as
    in [TypeTopology.DecidabilityOfNonContinuity](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.DecidabilityOfNonContinuity.html):

    > It is shown in [3] that negative consistent axioms can be postulated
    > in MLTT without loss of canonicity, and Andreas Abel filled important
    > gaps and formalized this in Agda [4] using a logical-relations
    > technique.
    >
    > ...
    >
    > [3] T. Coquand, N.A. Danielsson, M.H. Escardo, U. Norell and Chuangjie Xu.
    > Negative consistent axioms can be postulated without loss of canonicity.
    > https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf
    >
    > [4] Andreas Abel. Negative Axioms.
    >     https://github.com/andreasabel/logrel-mltt/tree/master/Application/NegativeAxioms

 1. Routine facts need no prose. Experts know them and others will
    find the formal proof easy enough.

 1. Adjectives that rate the mathematics, such as striking, surprising
    or beautiful, are for the reader to supply. To point at something
    worth emphasizing, say that it is noteworthy, and say why.

 1. No explanation is better than an obscure one.

 1. A variable in running prose is qualified, as in "the point a"
    rather than a bare "a". A binary operation or relation is named in
    prose with its underscores, as in "confluence modulo `_≈_`", and
    written bare when applied to arguments.

## Markdown in the prose

A minimal amount of markdown is allowed in the prose, namely
`` `code` ``, `*emphasis*`, `**bold**`, `[text](url)` and fenced code
blocks. Agda's own html backend renders the prose as plain text, and
the markdown is rendered by our own post-processing of the html
rendering, the script
[admin-utilities/agda-html.py](admin-utilities/agda-html.py), which
also turns urls, DOIs, arXiv identifiers and references to modules
into links. In the html rendering, the markdown symbols and the urls
of links are hidden, and so a line of prose is shorter there than in
the source file. The limit of 80 characters applies to the rendered
line, the one the reader sees. A source line that holds a url may
therefore be longer than 80 characters, and the text of a link may
start on one line and end on the next.

## The preamble of a module

Every module starts with prose before its first code block, which
gives the author or authors and the date on the first line, with the
dates of major later additions, says in a few sentences what the
module defines or proves, points to the index of its directory for an
overview of the development it belongs to, and lists the references it
relies on, with links. The module
[DomainTheory.Basics.Dcpo](https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.Basics.Dcpo.html)
is an example. The title line after the date may be a noun phrase,
and everything else in the prose is written in full sentences.

## Names

 1. A property is `is-` followed by its name, as in
    [`is-embedding`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Embeddings.html#is-embedding), and a map between two types is named by its source
    and target, as in [`ℕ-to-ℕ∞`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.GenericConvergentSequence.html#ℕ-to-ℕ∞).

 1. A fact about things is named so that it reads like a sentence, as
    in [`ℕ-is-set`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.DiscreteAndSeparated.html#ℕ-is-set), [`props-are-sets`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Subsingletons-Properties.html#props-are-sets),
    [`equivs-are-embeddings`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Embeddings.html#equivs-are-embeddings), [`ℕ-to-ℕ∞-is-embedding`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.GenericConvergentSequence.html#ℕ-to-ℕ∞-is-embedding),
    [`EM-gives-WEM`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.ClassicalLogic.html#EM-gives-WEM), [`𝟚-retract-of-ℕ∞`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.GenericConvergentSequence.html#𝟚-retract-of-ℕ∞) and
    [`being-embedding-is-prop`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Embeddings.html#being-embedding-is-prop).

 1. Functions and lemmas are written in lower case and kebab style, as
    in [`idtoeq-eqtoid`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Univalence.html), and types start with a capital, as in
    [`Perfect-Nucleus`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Locales.PatchLocale.html#PatchConstruction.Perfect-Nucleus). A lemma about a particular type carries the type
    as a prefix, as in [`𝟚-is-discrete`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.DiscreteAndSeparated.html#𝟚-is-discrete), while an operation on a type is
    named without it, as in [`pred`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Fin.html#pred) and [`suc-lc`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Fin.html#suc-lc) in
    [MLTT.Fin](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Fin.html), since its type says what it acts on.

 1. A variant of an existing definition or lemma takes the same name
    with a prime or a subscript, and a family of related facts about
    one object is numbered with subscripts.

 1. The hypotheses of univalent foundations have standard variable
    names across the development, namely [`fe`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.FunExt.html) for function extensionality,
    [`pt`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html) for the existence of propositional truncations, [`ua`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Univalence.html) for
    univalence, [`pe`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Subsingletons.html) for propositional extensionality, [`em`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.ClassicalLogic.html) for
    excluded middle and [`sr`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html) for set replacement. An identification
    [`x ＝ y`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Identity-Type.html#_＝_) is a path and is named like one, as `p`, and a hypothesis
    of type [`x ≠ y`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Negation.html#_≠_) is named for what it is, as `ne`.

## Suggested Emacs input sequences

The following input sequences for [Emacs Agda mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input)
type the symbols and the text that the conventions below adopt.
Each of them is explained below. Add

```
'(agda-input-user-translations
  '(("UU" "𝓤") ("VV" "𝓥") ("WW" "𝓦") ("TT" "𝓣")
    ("Ud" "𝓤 ̇ ") ("Vd" "𝓥 ̇ ") ("Wd" "𝓦 ̇ ") ("Td" "𝓣 ̇ ")
    ("=" "＝")
    ("beg" "\\begin{code}\n\n") ("end" "\\end{code}\n\n")
    ("code" "\\begin{code}\n\n\n\n\\end{code}\n\n")))
```

to your Emacs configuration.

## Type theory and notation

 1. We work in a minimal version of intensional Martin-Löf type theory
    that we call Spartan MLTT, with a minimal subset of Agda. We define
    everything from [MLTT.Spartan](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Spartan.html). The flag
    [`exact-split`](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-exact-split) is on, so that a definition by pattern matching holds
    definitionally.

 1. We adopt the univalent point of view even in modules that assume
    no axioms, taking seriously the distinction between types that are
    singletons, propositions, sets, 1-groupoids, etc., even where none of
    univalence, function extensionality or propositional
    extensionality is needed to reason about them, as in
    [UF.Subsingletons](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Subsingletons.html).

 1. Higher inductive types are available as hypotheses, in the same
    way as the axioms above, rather than as primitives. Propositional
    truncations are given by the record
    [`propositional-truncations-exist`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist),
    with the truncation `∥ X ∥`, its proof of being a proposition, the
    map `∣_∣` and the recursion principle `∥∥-rec` as fields, and a
    module that needs them takes a parameter
    `pt : propositional-truncations-exist`. Set quotients are given by
    the record
    [`set-quotients-exist`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Quotient.Type.html#set-quotients-exist)
    in the same way. Such a record can also be constructed, under
    assumptions: [Quotient.Large](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Quotient.Large.html)
    builds set quotients, one universe up, from propositional
    truncations, function extensionality and propositional
    extensionality, and
    [Quotient.FromSetReplacement](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Quotient.FromSetReplacement.html)
    brings them down to the same universe with set replacement.

 1. Universes are written [`𝓤 ̇`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html#_̇) for the universe at level `𝓤`, with
    the variables [`𝓤 𝓥 𝓦 𝓣`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html), as defined in [MLTT.Universes](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html), and never
    with Agda's own `Set ℓ` or `Type ℓ`. The superscript dot is a
    postfix operator, typed as `\^.` in [Emacs Agda mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input), and so
    there is a space between `𝓤` and the dot, although it is not
    visible, because the dot is displayed on top of it. The universe
    variables are typed as `\MCU`, `\MCV`, `\MCW` and `\MCT`, or as
    `\UU`, `\VV`, `\WW` and `\TT`, and a universe `𝓤 ̇ ` with its dot
    and the spaces around it as `\Ud`, `\Vd`, `\Wd` and `\Td`, with the
    [input sequences above](#suggested-emacs-input-sequences). There is
    exactly one space after the dot, even before a closing bracket `)`
    or `}`, as in
    [UF.Equiv](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Equiv.html):

    ```agda
    is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
    ```

    Our [html rendering](https://www.cs.bham.ac.uk/~mhe/TypeTopology/index.html) is tidied for the reader by
    [assets/Agda.css](assets/Agda.css), which hides the dot and the
    spaces before and after it, so that we see `(X : 𝓤)` as the HoTT
    book writes it while the source keeps what Agda needs.

 1. The identity type is [`＝`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Identity-Type.html#_＝_), typed as `\=` with the
    input sequences above.

 1. [Σ types](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Sigma.html) are written [`Σ x ꞉ A , B x`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Sigma.html#Sigma), where the colon is the Unicode
    character MODIFIER LETTER COLON, typed as `\:4`, and not the
    character RATIO that `\:` gives. The same applies to
    [`∃ x ꞉ A , B x`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#PropositionalTruncation.Exists), the propositional truncation of the Σ type, defined
    in [UF.PropTrunc](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html). We prefer Σ types to records,
    as in the definition of [`Ordinal`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Type.html#Ordinal), because univalent foundations supplies constructions and theorems
    for Σ types that we apply all the time. Records are allowed in
    some cases, as they are equivalent to iterated Σ types, in
    particular when their fields quantify over universes, which a Σ
    type cannot do, as in the record [`propositional-truncations-exist`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist)
    of [UF.PropTrunc](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html), whose type is `𝓤ω`.

 1. Propositional truncation is neither built in nor postulated. A
    module that needs it takes the hypothesis
    [`pt : propositional-truncations-exist`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist) as a parameter, and
    brings the notation into scope with
    [`open PropositionalTruncation pt`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#PropositionalTruncation), as
    [UF.ImageAndSurjection](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.ImageAndSurjection.html) does. This gives the truncation
    [`∥ X ∥`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist.∥_∥) of a type `X`, the proof [`∥∥-is-prop`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist.∥∥-is-prop) that it is a
    proposition, the inclusion [`∣ x ∣`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist.∣_∣) of a point `x : X`, the
    eliminator [`∥∥-rec`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#propositional-truncations-exist.∥∥-rec), and [`∃`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#PropositionalTruncation.∃) and [`∨`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.PropTrunc.html#PropositionalTruncation._∨_) defined
    from them.

 1. Use the named accessors of a structure rather than [`pr₁`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Sigma-Type.html#Σ.pr₁) and
    [`pr₂`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Sigma-Type.html#Σ.pr₂), as in [`resized X s`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html#resized) rather than `pr₁ s` for
    [`s : X is 𝓥 small`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html#_is_small), and as in [`underlying-order α`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Underlying.html#Underlying.underlying-order) and
    [`is-well-ordered α`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Type.html#is-well-ordered) for an ordinal `α` in [Ordinals.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Type.html).
    When you define your own type as a Σ type, name its projections
    in the same way, as [Ordinals.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Type.html) does for [`Ordinal`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Type.html#Ordinal).
    Name the properties of a projection once, next to it, as
    [`clopens-of-is-embedding`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.StoneTypes.html#clopens-of-is-embedding) does, rather than proving them
    inline at each use.

## Proofs

 1. We prefer proofs broken into small steps that each make sense on
    their own, with a fact the code relies on silently, such as a
    definitional equality that makes a clause type-check, stated as a
    step rather than left implicit. Saving lines is not one of our
    goals. For example, [`cons-decreases-modulus`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.CantorSearch.html#cons-decreases-modulus) in
    [TypeTopology.CantorSearch](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.CantorSearch.html) could be written in one line, but instead
    states each step with its type:

    ```agda
    cons-decreases-modulus : (p : 𝟚ᴺ → 𝟚)
                             (n : ℕ)
                             (b : 𝟚)
                           → (succ n) is-a-modulus-of-uc-of p
                           → n is-a-modulus-of-uc-of (p ∘ cons b)
    cons-decreases-modulus p n b u α β = III
     where
      I : α ＝⟦ n ⟧ β → cons b α ＝⟦ succ n ⟧ cons b β
      I e = refl , e

      II : cons b α ＝⟦ succ n ⟧ cons b β → p (cons b α) ＝ p (cons b β)
      II = u (cons b α) (cons b β)

      III : α ＝⟦ n ⟧ β → p (cons b α) ＝ p (cons b β)
      III = II ∘ I
    ```

 1. We prefer to prove equalities with chains [`＝⟨ ⟩`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html#_＝⟨_⟩_), as in
    [Integers.Multiplication](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Integers.Multiplication.html), so that every intermediate term is
    on the page, although occasionally composing them with [`∙`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html#_∙_) may be
    preferable.

 1. Keep an argument explicit when it helps the reader, even when Agda
    could infer it.

 1. Implicit arguments are passed positionally, with the implicit
    arguments before the one we need supplied as well, as in
    [`inl {𝓤} {𝓥} {X} {Y} x`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Plus-Properties.html) in
    [MLTT.Plus-Properties](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Plus-Properties.html), and bound positionally on the left-hand
    side of a definition, as in [`lhs {𝓤} {X} {x} {y} p = x`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html#lhs) in
    [MLTT.Id](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html), and never by [name](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html), as in `inl {Y = Y} x` or
    `lhs {X = X}`.

 1. The flag [`--no-infer-absurd-clauses`](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-no-infer-absurd-clauses) is on, so that
    Agda does not silently omit the clauses for impossible cases when
    it checks a definition for coverage, and each such clause is
    written out, which matches MLTT more closely. We write it without
    absurd patterns `()` or dot patterns. A hypothesis whose type
    computes to [`𝟘`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Empty-Type.html#𝟘) is eliminated with [`𝟘-elim`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Empty.html#𝟘-elim), or with
    [`𝟘-induction`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Empty.html#𝟘-induction) when the result type depends on it, an equation
    between distinct constructors is refuted with a lemma such as
    [`zero-is-not-one`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Two-Properties.html#zero-is-not-one) or [`succ-lc`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Naturals.Properties.html#succ-lc), and an inductive family at an
    empty index is mapped into a code family that computes to
    [`𝟘`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Empty-Type.html#𝟘)
    there, as [`Fin-0-is-empty`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Fin.html#Fin-0-is-empty) does.

 1. We avoid [`with`](https://agda.readthedocs.io/en/latest/language/with-abstraction.html).

 1. A helper that is useful beyond the proof it was written for is
    public and global, with a name of its own, and not a local
    definition in a `where` block. An anonymous declaration `_ : A`
    followed by `_ = e` is for a claim worth emphasizing but not worth
    naming, as in [UF.TruncationLevels](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.TruncationLevels.html).

## Layout

 1. Lines have at most 80 characters, in code and prose alike.

 1. Indentation is a single space, which is nonstandard, so please pay
    attention to it.

 1. A type signature that does not fit on one line is broken with the
    name on its own line and the colon and arrows aligned under each
    other, as in [Locales.StoneImpliesSpectral](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Locales.StoneImpliesSpectral.html). A
    definition whose right-hand side does not fit on the line of its
    left-hand side is broken in the same way, with the equals sign
    under the colon, as in
    [TypeTopology.WeaklyCompactTypes](https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.WeaklyCompactTypes.html#Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain):

    ```agda
    Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain
     : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
     → X
     → is-Π-compact (X → Y)
     → is-Π-compact Y
    Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain x
     = retract-is-Π-compact
        (codomain-is-retract-of-function-space-with-pointed-domain x)
    ```

 1. In an equality chain, the terms are left aligned, and every [`＝⟨`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html#_＝⟨_⟩_)
    and the final [`∎`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Id.html#_∎) sit in one column, one space after the widest
    term, as in [Naturals.Addition](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Naturals.Addition.html):

    ```agda
    trivial-addition-rearrangement x y z =
      (x + y) + z ＝⟨ addition-associativity x y z ⟩
      x + (y + z) ＝⟨ ap (x +_) (addition-commutativity y z) ⟩
      x + (z + y) ＝⟨ (addition-associativity x z y)⁻¹ ⟩
      (x + z) + y ∎
    ```

    When the justifications would push the lines past the limit, they
    are named in a `where` clause, as in
    [CoNaturals.Type2Properties](https://www.cs.bham.ac.uk/~mhe/TypeTopology/CoNaturals.Type2Properties.html):

    ```agda
    finite'-preservation n =
     ℕ∞'-to-ℕ∞ (ι n)             ＝⟨ I ⟩
     ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' (ι n)) ＝⟨ II ⟩
     ι n                         ∎
      where
       I  = (ap ℕ∞'-to-ℕ∞ (finite-preservation n))⁻¹
       II = inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ (ι n)
    ```

    Alignment is counted in characters. After a rename, realign every
    chain the name touches, including the ones that became narrower.

 1. Prose is wrapped per paragraph, at any width up to 80, without
    breaking hyphenated words or short formulas such as [`¬ WLPO`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Taboos.WLPO.html#WLPO) across
    lines.

 1. Code blocks have a blank line before and after `\begin{code}`, and
    before and after `\end{code}`, as in [UF.Size](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html):

    ```
    A more standard notion of impredicativity is that the type Ω 𝓤 of
    truth-values in the universe 𝓤 itself lives in 𝓤.

    \begin{code}

    Ω-resizing : (𝓤 : Universe) → 𝓤 ⁺ ̇
    Ω-resizing 𝓤 = (Ω 𝓤) is 𝓤 small

    \end{code}

    Propositional resizing doesn't imply that the first universe 𝓤₀ is
    impredicative, but it does imply that all other, successor, universes
    𝓤 ⁺ are.
    ```

    In Emacs, `\beg`, `\end` and `\code` type `\begin{code}`,
    `\end{code}` and an empty code block, each followed by its blank
    line, with the input sequences above.

    We use [`.lagda` files](https://agda.readthedocs.io/en/latest/tools/literate-programming.html).

## Checking your work

 1. Check the whole development by running

    ```
    agda AllModulesIndex.lagda
    ```

    from `source`, since [AllModulesIndex.lagda](source/AllModulesIndex.lagda) imports every
    module. Additionally, there is a [Makefile](Makefile) at the root,
    whose targets do this with the released or the development
    version of Agda, sequentially or in parallel, as `make help`
    explains. The GitHub action checks the whole development in the
    same way on every pull request, other than draft pull requests. A
    second GitHub action checks the safe fragment of the development,
    which is what [index.lagda](source/index.lagda) imports, with
    [Mikan](https://codeberg.org/1lab/mikan).

    Checking with Agda is all we ask of a pull request. If you like,
    you can run the Mikan check yourself with

    ```
    mikan index.lagda
    ```

    from `source`, which uses the flags listed in
    [typetopology.mikan-lib](typetopology.mikan-lib) instead.

 1. Check for unused imports with

    ```
    ../utilities/imports.sh <file>.lagda
    ```

    from `source`, and remove the ones it reports, after confirming
    by type-checking that each one is unused. The script runs in bash
    and uses GNU `sed`, which Linux has, macOS gets as [`gsed`](https://formulae.brew.sh/formula/gnu-sed)
    from [Homebrew](https://brew.sh/), and Windows gets together with bash from
    [WSL](https://learn.microsoft.com/en-us/windows/wsl/install) or
    [Git for Windows](https://gitforwindows.org/).

 1. Check the line length with

    ```
    awk 'length > 80' <file>.lagda
    ```

    in a UTF-8 locale.

## Module descriptions

The repository
[TypeTopologyModuleDescriptions](https://github.com/martinescardo/TypeTopologyModuleDescriptions)
has an entry for each directory of TypeTopology, which says what its
modules do and lists its authors and the publications that resulted
from it. Please make a pull request there too to explain your contribution.

## Pull requests

We prefer small pull requests, but discuss with the maintainers if you
feel that a particular case would benefit from a larger pull request.
Small pull requests get reviewed sooner. Before submitting a pull
request, go through this quick checklist, where each point is
explained in the sections above, particularly
[What we ask of every contribution](#what-we-ask-of-every-contribution)
and [Checking your work](#checking-your-work).

 - [ ] A first contribution goes to the directory `source/gist`.
 - [ ] Your name and the date are at the place of contribution, and
       your name is in the list of contributors in the
       [README](README.md).
 - [ ] Everything taken or inspired from elsewhere is attributed, with
       citations or links.
 - [ ] Every new file is imported by the index file of its directory,
       and every new directory has an index file imported by the index
       of its parent.
 - [ ] Your new modules and directories are described in the
       [module descriptions](https://github.com/martinescardo/TypeTopologyModuleDescriptions),
       by a pull request to that repository.
 - [ ] Every module in the safe fragment includes the pragma
       `{-# OPTIONS --safe --without-K #-}`.
 - [ ] Every axiom is a hypothesis of a result or a parameter of a
       module, with no postulates.
 - [ ] A new proof or definition of something the development already
       has is added alongside the existing one.
 - [ ] Implicit arguments are passed positionally.
 - [ ] `with` is not used.
 - [ ] The required code layout is obeyed.
 - [ ] Indentation is by 1 space.
 - [ ] The whole development type-checks with Agda.
 - [ ] All imports are used.
 - [ ] Every line has at most 80 characters.
 - [ ] Everything you contribute is written by you.

## Reporting problems and asking for help

To report a problem with the development, or to ask for help, including
about where a contribution belongs, open an
[issue](https://github.com/martinescardo/TypeTopology/issues).

## Code of conduct, inclusion, AI policy and license

By contributing, with pull requests, issues or discussion, you agree to
abide by our [code of conduct](CODE-OF-CONDUCT.md) and
[statement of inclusion](STATEMENT-OF-INCLUSION.md). So far we have had
no problem whatsoever, and we want to keep it that way. If you are
aware of a violation of these policies that affects you or somebody
else, please report it to
[Martin Escardo](mailto:m.escardo@cs.bham.ac.uk) or
[Tom de Jong](mailto:tdejong.ac@gmail.com). Our
[AI policy](AI-Policy.md) applies to every contribution, and the
[license](LICENSE) is [GPL-3](https://www.gnu.org/licenses/gpl-3.0.html).
