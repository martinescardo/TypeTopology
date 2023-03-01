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
- `TypeTopology` does not use the level notation of Agda and instead provides a
  wrapper (in module [`MLTT.Universes`][1]) around this to keep the notation
  close to pen-and-paper conventions. We use the variables `𝓤 𝓥 𝓦` for universe
  levels and use the notation `𝓤  ̇` to denote the universe at level `𝓤`. Please
  make sure that your code uses this and avoids the level notation.
- We use the symbol `＝` for the identity type. The Emacs Agda mode does not
  provide a built-in abbreviation to type this so it's a good idea to insert
  this binding to your `agda-input-user-translations` i.e.
  ```
  '(agda-input-user-translations '(("=" "＝")))
  ```
- Always leave a single space character between the universe dot superscript and
  the following bracket. This is needed in order for the dot not to show on top
  of the closing bracket in some browsers in its HTMl rendering, including
  Firefox.
- Each module should contain a preamble that includes:

  * the author(s) of the module,
  * a brief summary of contents,
  * starting date of the development and dates of major additions.

  See [`DomainTheory.Basics.Dcpo`][2] for an example.

[1]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html
[2]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.Basics.Dcpo.html
