Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
November 2023 — December 2024

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Ordinals.Exponentiation.index where

-- Specification of ordinal exponentiation.
import Ordinals.Exponentiation.Specification

-- An abstract construction of ordinal exponentation using suprema of ordinals.
import Ordinals.Exponentiation.Supremum

-- A concrete construction of ordinal exponentation using decreasing lists, as
-- well as direct proofs of a few properties, including that the construction
-- meets the specification.
import Ordinals.Exponentiation.DecreasingList
import Ordinals.Exponentiation.DecreasingListProperties-Concrete

-- Relating the abtract and concrete constructions with an equivalence for base
-- ordinals with a trichotomous least element.
import Ordinals.Exponentiation.RelatingConstructions

-- Properties of both the abstract and concrete constructions (via transport).
import Ordinals.Exponentiation.PropertiesViaTransport

-- Auxiliary result that an ordinal α has a trichotomous least element if and
-- only if it can be decomposed (necessarily uniquely) as 𝟙ₒ +ₒ α' for some
-- ordinal α'.
import Ordinals.Exponentiation.TrichotomousLeastElement

-- Constructive taboos involving ordinal exponentiation.
import Ordinals.Exponentiation.Taboos

\end{code}
