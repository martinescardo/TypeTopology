Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
November 2023 — January 2025
With additions in April 2025, notably (9) below.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Exponentiation.index where

\end{code}

OVERVIEW
========

1.  Specification of ordinal exponentiation.
2.  An abstract construction of ordinal exponentiation using suprema of
    ordinals.
3.  A concrete construction of ordinal exponentiation using decreasing lists.
4.  Direct proofs of a few properties of the concrete construction of
    exponentiation, including that the construction meets the specification.
5.  Relating the abstract and concrete constructions with an equivalence for
    base ordinals with a trichotomous least element.
6.  Properties of both the abstract and concrete constructions (via transport
    and the above equivalence).
7.  Auxiliary result that an ordinal α has a trichotomous least element if and
    only if it can be decomposed as 𝟙ₒ +ₒ α' for a necessarily unique ordinal α'.
8.  Constructive taboos involving ordinal exponentiation.
9.  An implementation of Robin Grayson's variant of the decreasing list
    construction of exponentials and a proof that it is not, in general, an
    ordinal.
10. Miscellaneous properties of exponentiation.

\begin{code}

import Ordinals.Exponentiation.Specification                     -- (1)
import Ordinals.Exponentiation.Supremum                          -- (2)
import Ordinals.Exponentiation.DecreasingList                    -- (3)
import Ordinals.Exponentiation.DecreasingListProperties-Concrete -- (4)
import Ordinals.Exponentiation.RelatingConstructions             -- (5)
import Ordinals.Exponentiation.PropertiesViaTransport            -- (6)
import Ordinals.Exponentiation.TrichotomousLeastElement          -- (7)
import Ordinals.Exponentiation.Taboos                            -- (8)
import Ordinals.Exponentiation.Grayson                           -- (9)
import Ordinals.Exponentiation.Miscellaneous                     -- (10)

\end{code}

The following file acts as an index for the paper "Ordinal Exponentiation in
Homotopy Type Theory".

\begin{code}

import Ordinals.Exponentiation.Paper

\end{code}

And the following file acts as an index for the paper "Constructive Ordinal
Exponentiation".

\begin{code}

import Ordinals.Exponentiation.PaperJournal

\end{code}
