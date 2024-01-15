Brendan Hart 2019-2020

Ported from https://github.com/BrendanHart/Investigating-Properties-of-PCF/
by Martin Escardo, 17-18 May 2023. This is Brendan's final-year UG
project at the School of Computer Science, University of Birmingham,
UK, jointly supervised by Martin Escardo and Tom de Jong.

Tom de Jong, in work reported in this repository, defines the Scott
model of PCF in the combinary version of PCF. Brendan extends the
work to the usual λ-calculus version of PCF.  Moreover, Tom proved, in
Unimath, that the Scott model of (combinatory) PCF is computationally
adequate.  Brendan's work also proves this, in Agda, here, for the
λ-calculus version. In order to do all this, Brendan also had to
extend Tom's work on domain theory.

A full report in pdf is available in the above link.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module PCF.Lambda.index where

import DomainTheory.Basics.Curry
import DomainTheory.Basics.FunctionComposition
import DomainTheory.Basics.Products
import DomainTheory.Basics.ProductsContinuity
import PCF.Lambda.AbstractSyntax
import PCF.Lambda.Adequacy
import PCF.Lambda.ApplicativeApproximation
import PCF.Lambda.BigStep
import PCF.Lambda.Correctness
import PCF.Lambda.ScottModelOfContexts
import PCF.Lambda.ScottModelOfIfZero
import PCF.Lambda.ScottModelOfTerms
import PCF.Lambda.ScottModelOfTypes
import PCF.Lambda.Substitution
import PCF.Lambda.SubstitutionDenotational

\end{code}
