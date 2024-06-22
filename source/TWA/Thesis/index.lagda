Todd Waugh Ambridge, January 2024

Exact Real Search: Formalised Optimisation and Regression in
Constructive Univalent Mathematics

A thesis submitted to the University of Birmingham for the degree of
Doctor of Philosophy.

https://arxiv.org/abs/2401.09270

\begin{code}
{-# OPTIONS --without-K --safe #-}

module TWA.Thesis.index where
\end{code}

ABSTRACT

The real numbers are important in both mathematics and computation
theory. Computationally, real numbers can be represented in several
ways; most commonly using inexact floating-point data-types, but also
using exact arbitrary-precision data-types which satisfy the expected
mathematical properties of the reals. This thesis is concerned with
formalising properties of certain types for exact real arithmetic,
as well as utilising them computationally for the purposes of search,
optimisation and regression.

We develop, in a constructive and univalent type-theoretic foundation
of mathematics, a formalised framework for performing search,
optimisation and regression on a wide class of types. This framework
utilises Martin Escardo's prior work on searchable types, along with a
convenient version of ultrametric spaces --- which we call closeness
spaces --- in order to consistently search certain infinite types using
the functional programming language and proof assistant Agda.

We formally define and prove the convergence properties of
type-theoretic variants of global optimisation and parametric
regression, problems related to search from the literature of analysis.
As we work in a constructive setting, these convergence theorems yield
computational algorithms for correct optimisation and regression on the
types of our framework.

Importantly, we can instantiate our framework on data-types from the
literature of exact real arithmetic. The types for representing real
numbers that we use are the ternary signed-digit encodings and a
simplified version of Hans-J. Boehm's functional encodings.
Furthermore, we contribute to the extensive work on ternary
signed-digits by formally verifying the definition of certain exact
real arithmetic operations using the Escardo-Simpson interval object
specification of compact intervals.

With this instantiation, we are able to perform our variants of search,
optimisation and regression on representations of the real numbers.
These three processes comprise our framework of exact real search; we
close the thesis by providing some computational examples of this
framework in practice.

CHAPTER ONE: Introduction

In Chapter 1, we motivate the work of using searchable types in order
to construct algorithms for global optimisation and parametric
regression on the ternary-signed digits.

https://arxiv.org/pdf/2401.09270.pdf#chapter.1

CHAPTER TWO: Constructive Univalent Type Theory in Agda

In Chapter 2, we introduce the key concepts of our constructive and
univalent type-theoretic foundation of mathematics in which we build
our formal framework for search, optimisation and regression.

https://arxiv.org/pdf/2401.09270.pdf#chapter.2

\begin{code}
open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter2.Sequences
\end{code}

CHAPTER THREE: Searchability and Continuity

In Chapter 3, we review and define the two key mathematical concepts
of the thesis: searchability and uniform continuity.

We build on the previous work of Martin Escardo, contributing a method
of searching certain infinite types in Agda by using explicit
information about uniform continuity of the predicate being searched.
This notion of uniform continuity is defined on a convenient version of
ultrametric spaces that we call closeness spaces.

We also give a version of the totally bounded property for closeness
spaces, and show that a variety of types yield closeness spaces. The
key technical contribution of this section is the formalised result
which shows these uniformly continuously searchable types are closed
under countable products.

https://arxiv.org/pdf/2401.09270.pdf#chapter.3

\begin{code}
open import TWA.Thesis.Chapter3.ClosenessSpaces
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples
open import TWA.Thesis.Chapter3.SearchableTypes
open import TWA.Thesis.Chapter3.SearchableTypes-Examples
open import TWA.Thesis.Chapter3.PredicateEquality
\end{code}

CHAPTER FOUR: Generalised Optimisation and Regression

In Chapter 4, we use uniformly continuously searchable closeness spaces
to define our formal convergence properties of global optimisation and
parametric regression on a wide class of types. For this purpose, we
introduce approximate linear preorders, which approximately order
elements of closeness spaces. The key contribution of this section ---
the statement of the type-theoretic variants of global optimisation and
parametric regression --- is methodological rather than technical, as
the proofs of their convergence follow naturally from the concepts we
have introduced.

https://arxiv.org/pdf/2401.09270.pdf#chapter.4

\begin{code}
open import TWA.Thesis.Chapter4.ApproxOrder
open import TWA.Thesis.Chapter4.ApproxOrder-Examples
open import TWA.Thesis.Chapter4.GlobalOptimisation
open import TWA.Thesis.Chapter4.ParametricRegression
\end{code}

CHAPTER FIVE: Real Numbers

In Chapter 5, we define two types for representing real numbers:
ternary signed-digit encodings and ternary Boehm encodings.

On the former, we formally verify exact real arithmetic operations
(namely: negation, binary midpoint, infinitary midpoint and
multiplication) using the Escardo-Simpson interval object specification
of closed intervals --- which we also review and formalise in this
section.

On the latter, we define the type in Agda, prove the correctness of its
structure and show how it yields representations of compact intervals
that we can then use for search.

\begin{code}
open import TWA.Thesis.Chapter5.IntervalObject
open import TWA.Thesis.Chapter5.IntervalObjectApproximation
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter5.SignedDigitIntervalObject
open import TWA.Thesis.Chapter5.BoehmStructure
open import TWA.Thesis.Chapter5.BoehmVerification
open import TWA.Thesis.Chapter5.Integers
\end{code}

CHAPTER SIX: Exact Real Search

In Chapter 6, we bring our formal framework full-circle by
instantiating it on these two types for representing real numbers. 
Example evaluations of algorithms for search, optimisation and
regression --- either extracted from Agda or implemented in Java ---
are then given to show the use of the framework in practice.

\begin{code}
open import TWA.Thesis.Chapter6.SequenceContinuity
open import TWA.Thesis.Chapter6.SignedDigitSearch
open import TWA.Thesis.Chapter6.SignedDigitOrder
open import TWA.Thesis.Chapter6.SignedDigitContinuity
open import TWA.Thesis.Chapter6.SignedDigitExamples
\end{code}

CHAPTER SEVEN: Conclusion

Finally, in Chapter 7, by way of conclusion we discuss some further
avenues for this line of work. 

SPECIAL THANKS

A special thanks goes to Andrew Sneap, who wrote the following two
files specifically for the use of the Boehm verification in Chapter 5.

\begin{code}
open import TWA.Thesis.AndrewSneap.DyadicRationals
open import TWA.Thesis.AndrewSneap.DyadicReals
\end{code}

