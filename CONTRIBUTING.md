# Contribution Guidelines

Welcome to TypeTopology!

We always appreciate contributions in the form of pull requests.

1. However, if you have something to add or modify, please in the first
instance ask Martin Escardo and Tom de Jong, in a joint email message
to their academic email addresses, where to add your contribution or
modifications, before you make a pull request.

1. Because the objective of TypeTopology is not to merely record existing
mathematics, but to create new mathematics (read [the index
file](source/index.lagda), and also [Papers
resulting from
TypeTopology](README.md#publications-resulting-from-typetopology)), it
is not OK to attempt to modify somebody else's files without their explicit
permission given in advance, before any pull request is made. These people may be working on a paper for publication, and it is not OK to jump in without their consent.

1. By default, if you have a new original contribution, it should first
go to the [gist](source/gist) folder, in a new subfolder there, and
once we are fully done with your pull request and merged it, we may find a better
home for it (and we are open for your suggestions to where to place it).

1. But you may also be just adding already existing mathematics, and this
is rather welcome (we need lots of missing things in order to carry out the new things we want to do!). You should discuss with Martin Escardo and Tom de
Jong where to add it.

1. An important point is that we don't want to
have just **one** proof, e.g. the "best proof". We want to have all
known proofs. So, if you add a new, better (in your opinion) proof,
don't delete the previous one (but you are invited to write in a
comment how your new proof improves the old ones).

1. Below, we try to explain the style we adopt in TypeTopology. But we are not comprehensive enough. So first study how we write and typeset code in practice, to avoid unnecessary interactions during pull-request reviews.

1. Most importantly, the objective of `TypeTopology` is to explain mathematics to *people* and not just *computers*. So write *plenty* of comments in your contributions, just as you would in your papers submitted for publication.

1. We recognize, in view of the previous remark, that non-academics would like to contribute too, and they are most welcome to do so. In fact, a number of non-academics have already contributed, and we are very happy they did, and we would like to encourage everyone to join and contribute.

1. And, please, do abide by the [code of conduct](CODE-OF-CONDUCT.md). So far we haven't had any problem whatsoever, and we want to keep it that way.

1. **Important rule.** Everybody who contributes must add their given or adopted name to the file or place of contribution, together with the date of contribution. If in doubt, see how we do it in practice. If your contribution is in the middle of a file, then add "Contribution by `name` at `date`", then your contribution, then "end of co. nion" (not necessarily exactly this form - see how we do it in practice). We want everybody who contributes to get explicit credit. We also want to have an explicitly visible historical record.

# TODO

The following is very old and should be rewritten when we have time. But for the moment please stick to it. You will learn further unwritten guidelines when you submit a pull request - apologies.

# Conventions

In this
document, we provide a list of conventions and practices that we expect
`TypeTopology` contributors to follow.

- Developments are organised using subdirectories inside the `source` folder.
  For example, the domain theory development lives in `source/DomainTheory`.
- The file `index.lagda` contains a global index for `TypeTopology`, importing
  the index for each development in each directory (e.g. `DomainTheory.index`).
  If you are starting a new development, make sure that it has an `index.lagda`
  file and that it is imported in the global `index.lagda` file.
- The indentation length used in `TypeTopology` is **a single space**. Please be
  careful about this as it is a nonstandard convention.
- `TypeTopology` does not use the level notation of Agda (i.e. `Type ℓ`) and
  instead provides a wrapper (in module [`MLTT.Universes`][1]) around this to
  keep the notation close to pen-and-paper conventions. We use the variables `𝓤
  𝓥 𝓦` for universe levels and use the notation `𝓤  ̇` to denote the universe at
  level `𝓤`. Please make sure that your code uses this and avoids the level
  notation.

  * To type `𝓤  ̇`, you can add the symbol `\^.` just after a space using Agda
    mode in Emacs.

  * Always leave a single space character between the universe dot superscript
    and the following bracket. This is needed in order for the dot not to show
    on top of the closing bracket in some browsers in its HTML rendering,
    including Firefox.

- We use the symbol `＝` for the identity type. The Emacs Agda mode does not
  provide a built-in abbreviation to type this so it's a good idea to insert
  this binding to your `agda-input-user-translations` i.e.
  ```
  '(agda-input-user-translations '(("=" "＝")))
  ```
  so that you can type it as `\=`.
- Each module should contain a preamble that includes:

  * the author(s) of the module,
  * a brief summary of contents,
  * starting date of the development and dates of major additions.

  See [`DomainTheory.Basics.Dcpo`][2] for an example.
- We adhere to a limit of _80 characters per line_. Please make sure to use
  `where` and `let` bindings to avoid lines exceeding this limit.
- The casing convention we use is as follows:

  * all function names should lower case and should use [_kebab casing_][3]
    e.g. `idtoeq-eqtoid`;
  * all type names should be upper case and should still use kebab casing if
    involves multiple words e.g. `Perfect-Nucleus`.
- We use [`.lagda` files][4] with `\begin{code}` and `\end{code}` blocks. There
  are some plans to migrate all files to `.lagda.md`, but until this happens,
  we'll continue to use `.lagda` for the sake of consistency.
- Our convention is to leave blank lines after `\begin{code}` and before
  `\end{code}`. In other words, your code should look like
  ```text
  \begin{code}

  <code goes here>

  \end{code}
  ```
- Comments and discussions in files are encouraged. Ideally, files should follow
  a literate programming in style.
- All modules should use the flags `--safe` and `--without-K`. Any modules that
  use unsafe features should be placed under the directory `Unsafe` and should
  be imported from `Unsafe/index.lagda`.
- For `Σ` types, we use the notation `Σ x ꞉ A , B x`. Note that the colon
  character here is `꞉` (the Unicode symbol `MODIFIER LETTER COLON`) and **not**
  `∶` (i.e. the Unicode symbol `RATIO`), which is what you get by typing `\:` in
  Agda mode. To get the former, you have to type `\:4`
- Avoid `with` clauses when defining functions.
- In the index files, whose purposes are to import modules in subdirectories,
  make sure to _alphabetically sort_ the `import` lines. This is preferable in
  all modules but it is a rule only for index files.
- When the type signature for a function `foo : A → B → C → D` goes over the
  character limit of 80 characters, break and indent it as:
  ```
  foo
   : A
   → B
   → C
   → D
  ```

[1]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html
[2]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.Basics.Dcpo.html
[3]: https://en.wikipedia.org/wiki/Letter_case#Kebab_case
[4]: https://agda.readthedocs.io/en/v2.6.3/tools/literate-programming.html
