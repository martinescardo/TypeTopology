3   TypeTopology

   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Martin Escardo and collaborators, 2010--2025--∞
   Continuously evolving.

   https://www.cs.bham.ac.uk/~mhe/TypeTopology/
   https://github.com/martinescardo/TypeTopology/

   Tested with Agda 2.8.0
   (it will probably work with Agda 2.7.0.1, and it may still work with Agda 2.6.4.3).

This file hereditarily imports all TypeTopology files. Most of them
are --safe. All of them are --without-K. See discussion below for
details, and also the following Agda manual entries.

https://agda.readthedocs.io/en/latest/language/safe-agda.html

https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-without-K

https://agda.readthedocs.io/en/latest/tools/command-line-options.html#consistency-checking-options

See the module (1) below for an explanation of the philosophy of
TypeTopology, and in particular which type theory is adopted.

\begin{code}

{-# OPTIONS --without-K --guardedness #-}

import index                                -- (1)
import Unsafe.index                         -- (2)
import InfinitePigeon.index                 -- (3)

\end{code}

(1) Index of --safe modules using --without-K and --level-universe.
(2) Index of unsafe modules. Requires --guardedness for some modules.
(3) Index of modules that disable termination check for bar recursion.
    These modules *should* be safe in some sense, but Agda can't tell this,
    and so the checking needs to be done by mathematicians and/or logicians.

Notice that, currently, all modules use --without-K.

The default options for all modules are (as listed in
typetopology.agda-lib, which should be taken as the authoritative
source of information if this list gets obsolete):

  --auto-inline
  --exact-split
  --keep-pattern-variables
  --level-universe
  --no-cohesion
  --no-cumulativity
  --no-erasure
  --no-guardedness
  --no-print-pattern-synonyms
  --no-prop
  --no-rewriting
  --no-save-metas
  --no-sized-types
  --no-two-level
  --without-K

But all modules should add the option --without-K, to emphasize an
essential point in the philosophy of TypeTopology, which is to be
compatible with univalent type theory.

An option is *coinfective* if whenever it is used in a module, it must
be used in all modules imported by that module. The following options
are coinfective:

  --safe
  --without-K
  --no-universe-polymorphism
  --no-sized-types
  --no-guardedness
  --level-universe

An option is *infective* if whenever it is used in one module, it must
be used in all modules that import module. At the moment, TypeTopology
infective options are:

  --no-termination-check
  --guardedness

Navigate to the corresponding files to see which (infective or
coinfective) options they use.
