Chuangjie Xu 2026

Entry point for the Agda development of C-spaces in TypeTopology.

The mathematical material originates in the PhD thesis of Chuangjie Xu (2015),
**A Continuous Computational Interpretation of Type Theories**, available at

  https://cj-xu.github.io/ContinuityType/xu-thesis.pdf

The modules imported below are intended to mirror the main mathematical stages
of the thesis and can be read as a guide to where the corresponding arguments
appear in Agda.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.index where

\end{code}

The first group of imports corresponds to the core categorical development of
C-spaces from Chapter 3 of the thesis.

At a high level, a C-space is a set equipped with a suitable notion of
continuity based on probes from Cantor space. The resulting category of
C-spaces is cartesian closed, in fact locally cartesian closed, and has a
natural numbers object. A central outcome is the construction of a fan
functional that continuously computes least moduli of uniform continuity for
maps from Cantor space to the natural numbers.

\begin{code}

-- § 3.2.1  The uniform-continuity site
import C-Spaces.Coverage

-- § 3.3.1  Concrete sheaves as a variation of quasi-topological spaces
import C-Spaces.UsingFunExt.Space

-- § 3.3.2  The (local) cartesian closed structure of C-Spaces
import C-Spaces.UsingFunExt.CartesianClosedness
import C-Spaces.UsingFunExt.Coproduct
import C-Spaces.UsingFunExt.LocalCartesianClosedness

-- § 3.3.3  Discrete C-spaces and natural numbers object
import C-Spaces.UsingFunExt.DiscreteSpace

-- § 3.4  The representable sheaf is the Cantor space
import C-Spaces.UsingFunExt.YonedaLemma

-- § 3.5  The fan functional in the category of C-spaces
import C-Spaces.UsingFunExt.Fan

\end{code}

The next group of imports corresponds to Chapter 4, where the full type
hierarchy, developed in Agda `Set`/types, is compared with the
Kleene-Kreisel continuous hierarchy developed inside C-spaces. Assuming the
Brouwerian axiom that all set-theoretic functions `₂ℕ → ℕ` are uniformly
continuous, these two hierarchies agree.

\begin{code}

-- § 4.3  The Kleene-Kreisel and full-type hierarchies
import C-Spaces.UsingFunExt.IndiscreteSpace
import C-Spaces.UsingFunExt.Hierarchy

\end{code}

The next group of imports corresponds to Chapters 5 and 6, where C-spaces are
used to interpret Gödel's System T with a Skolemization of `(UC)`, to realize
`(UC)` in the finite-type arithmetic `HAω`, and to validate the Curry-Howard
interpretation of `(UC)` in the locally cartesian closed category of C-spaces.
The fan functional is the central computational ingredient throughout this part
of the development.

\begin{code}

-- § 5.1  A continuous model of Gödel's System T
import C-Spaces.UsingFunExt.TdefinableFunctionsAreUC
import C-Spaces.UsingFunExt.UCinT

-- § 5.2  A continuous realizability semantics of HAω
import C-Spaces.UsingFunExt.UCinHAOmega

-- § 6.2  Modelling UC via the LCCC of C-spaces
import C-Spaces.UsingFunExt.ValidatingUCviaLCCC

\end{code}

The above development is closest to the mathematical presentation in the thesis,
but it relies on the full function extensionality axiom, which is not available
in Spartan MLTT. This does not affect the mathematical correctness of the
constructions, but it does affect their computational meaning: because no
computable instance of function extensionality is available, the resulting
closed Agda terms need not retain normalization behaviour strong enough for
extracted moduli to compute to numerals.

In particular, when a modulus of uniform continuity is obtained from the
interpretation of a System T-definable function in C-spaces, that modulus is
mathematically correct, but the corresponding closed Agda term cannot in
general be expected to normalize to a numeral. The following experiment
illustrates this loss of computational content.

\begin{code}

-- Overview of the branch developed under full function extensionality.
import C-Spaces.UsingFunExt.index
-- Example showing that, in this branch, a mathematically correct extracted
-- modulus need not normalize to a numeral as a closed Agda term.
import C-Spaces.UsingFunExt.ComputationExperiments

\end{code}

The final group of imports corresponds to one of the approaches developed in
Chapter 7 for recovering computational content from the C-space model. The
approach formalized below is the one from § 7.2.4 of the thesis: the probe
axioms are strengthened so that only the double negation of function
extensionality is needed. This modified development is somewhat less direct
than the `UsingFunExt` branch, but it has the crucial advantage that the
extensionality assumption appears only in the negative form `¬¬ FunExt`.

Because `¬¬ FunExt` is itself a negative statement, it carries no computational
content and does not obstruct normalization of closed Agda terms. As a result,
moduli extracted in this version of the model can normalize to numerals.

\begin{code}

-- § 7.2.4  Construction by postulating ¬¬ FunExt
-- Overview of the branch developed under ¬¬ FunExt.
import C-Spaces.UsingNotNotFunExt.index
-- Examples showing that the extracted moduli in this branch do normalize to
-- numerals as closed Agda terms.
import C-Spaces.UsingNotNotFunExt.ComputationExperiments

\end{code}
