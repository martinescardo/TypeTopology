Brendan Hart 2019-2020

Ported from https://github.com/BrendanHart/Investigating-Properties-of-PCF/
by Martin Escardo, 17-18 May 2023. This is Brendan's final-year UG
project at the School of Computer Science, University of Birmingham,
UK, jointly supervised by Martin Escardo and Tom de Jong.

Tom de Jong, in work reported in this repository, defines the Scott
model of PCF in the combinary version of PCF. This extends the work to
the usual λ-calculus version of PCF.  Moreover, Tom proved, in
Unimath, that the Scott model of (combinatory) PCF is fully
abstract. Brendan's work also proves this, in Agda, here, for the
λ-calculus version. In order to do all this, Brendan also had to
extend Tom's work on domain theory.

A full report in pdf is available in the above link.

\begin{code}

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module PCF.index where

import PCF.AbstractSyntax
import PCF.Adequacy
import PCF.ApplicativeApproximation
import PCF.BigStep
import PCF.Correctness
import PCF.Dcpo-Contexts
import PCF.Dcpo-FunctionComposition
import PCF.Dcpo-IfZero
import PCF.DcpoProducts
import PCF.DcpoProducts-Continuity
import PCF.DcpoProducts-Curry
import PCF.ScottModelTerms
import PCF.ScottModelTypes
import PCF.Substitution
import PCF.SubstitutionDenotational

\end{code}
