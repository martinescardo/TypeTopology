# Contribution Guidelines

We always appreciate contributions in the form of pull requests. In this
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
- Comments and discussions in files are encouraged. Ideally, files should follow
  a literate programming in style.
- All modules should use the flags `--safe` and `--without-K`, and if possible,
  `--exact-split` and `--auto-inline.` Any modules that use unsafe features
  should be placed under the directory `Unsafe` and should be imported from
  `Unsafe/index.lagda`.
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
