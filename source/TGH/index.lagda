Theo Hepburn, started September 2024

We develop a model of computation that can be used to calculate the running
time of a program written in a simple Lambda calculus-like language.

I show that this language is expressive by providing an implementation
of insertion sort and proving its correctness.

We provide a formalisation of time complexity and prove that several simple
algorithms, including the first and last elements of lists, have linear
time complexity.

Then, we formalise the complexity classes P and NP for decision problems on
binary strings and provide some simple problems that are members of these
classes, as well as proofs that P is closed for negation, conjunction and
disjunction.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.index where

\end{code}

An Agda formalisation of the definition of Big O.

\begin{code}

import TGH.BigO

\end{code}

The Thunk monad, which we use to track the number of steps to produce a value.

\begin{code}

import TGH.Thunk

\end{code}

A prototype of our language, where natural numbers are the only basic type.
Includes normal semantics, for evaluating the result of a program, and
intermediate semantics, which also provide the number of steps to reach the
resulting value.

We define programs for doubling a number and checking that a number is
even, and prove that they are correct and that they are O(n).

\begin{code}

import TGH.PrototypeLanguage

\end{code}

Contains a type that identifies the evaluation strategy that we will use
for running programs written in the full language - either lazy or eager.

\begin{code}

import TGH.Strategy

\end{code}

We extend our language to include lists as a basic type, and allow a
lazy or eager evaluation strategy to be specified, which affects
how the program running time is computed.

\begin{code}

import TGH.Language

\end{code}

We define some useful functions and lemmas for reasoning about the running time
of programs in our language.

\begin{code}

import TGH.ComplexityDefinitionsResults

\end{code}

Provides a program that finds the head of a list in our language.
We prove the correctness of `head` and show that it is constant
time when using a lazy evaluation strategy but linear time,
and not constant time, when using an eager evaluation strategy.

\begin{code}

import TGH.HeadExample

\end{code}

We define a program that gets the last element of a list, and provide
a proof that it is correct.

\begin{code}

import TGH.LastCorrectness

\end{code}

A proof that the value output of the last program does not depend on the
time component of the input when the eager evaluation strategy is used.

\begin{code}

import TGH.LastTimeListValueIndependent

\end{code}

A proof that the last program, when eager evaluation is used,
is linear time.

\begin{code}

import TGH.LastLinearTimeEager

\end{code}

Taken from the Advanced Functional Programming module lecture notes 2023-24.

Provides a formalisation of isomorphisms in Agda, and an implementation of
insertion sort, together with a proof of correctness.

\begin{code}

import TGH.AFP2024.index

\end{code}

We write an implementation of insertion sort in our language,
and prove that it is correct by showing that it always
produces the same output as the above Agda implementation
for a given input.

\begin{code}

import TGH.InsertionSortCorrectness

\end{code}

A formalisation of the complexity class P, with proof of closure properties of
P.

\begin{code}

import TGH.P

\end{code}

Examples of some decision problems that are in the complexity class P.

\begin{code}

import TGH.PExamples

\end{code}

Provides a formalisation of the the complexity class NP, with a proof that P⊆NP.

\begin{code}

import TGH.NP


\end{code}
