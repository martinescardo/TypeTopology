   [T y p e T o p o l o g y](https://github.com/martinescardo/TypeTopology)

   2010--2026--∞ continuously evolving.

   Various new theorems in constructive univalent mathematics written in Agda
   --------------------------------------------------------------------------

   [Martin Escardo](https://www.cs.bham.ac.uk/~mhe/) and [collaborators](https://github.com/martinescardo/TypeTopology#current-typetopology-contributors-in-alphabetical-order-of-first-name).

   Tested with Agda 2.8.0 and 2.9.0 (unreleased development version).
   This HTML rendering was automatically generated from commit to-be-filled-automatically.

This file hereditarily imports all TypeTopology files. Most of them
are `--safe`. All of them are `--without-K`. See discussion below for
details, and also the following Agda manual entries.

 * [Safe Agda](https://agda.readthedocs.io/en/latest/language/safe-agda.html)

 * [without-K](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K)

 * [Consistency checking options](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#consistency-checking-options)

See the module (1) below for an explanation of the philosophy of
TypeTopology, and in particular which type theory is adopted.

\begin{code}

{-# OPTIONS --without-K --guardedness --rewriting #-}

module AllModulesIndex where

import index                                -- (1)
import Unsafe.index                         -- (2)
import InfinitePigeon.index                 -- (3)

\end{code}

(1) Index of `--safe` modules using `--without-K` and `--level-universe`.
(2) Index of unsafe modules. Requires `--guardedness` and `--rewriting`
    for some modules.
(3) Index of modules that disable termination check for bar recursion.
    These modules *should* be safe in some sense, but Agda can't tell this,
    and so the checking needs to be done by mathematicians and/or logicians.

Notice that, currently, all modules use `--without-K`.

The default options for all modules are listed in [typetopology.agda-lib](https://github.com/martinescardo/TypeTopology/blob/master/typetopology.agda-lib).

But all modules should add the option `--without-K`, to emphasize an
essential point in the [philosophy of TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/), which is to be
compatible with univalent type theory.

An option is *coinfective* if whenever it is used in a module, it must
be used in all modules imported by that module. The following options
are coinfective:

  `--safe`
  `--without-K`
  `--no-universe-polymorphism`
  `--no-sized-types`
  `--no-guardedness`
  `--level-universe`

An option is *infective* if whenever it is used in one module, it must
be used in all modules that import module. At the moment, TypeTopology
infective options are:

  `--no-termination-check`
  `--guardednes`
  `--rewriting`

Navigate to the corresponding files to see which (infective or
coinfective) options they use.
