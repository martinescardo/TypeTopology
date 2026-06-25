Tom de Jong, 2 April 2021

The following modules construct the circle 𝕊¹ as the type of ℤ-torsors,
following "Construction of the circle in UniMath" by Bezem, Buchholtz, Grayson
and Shulman (doi:10.1016/j.jpaa.2021.106687).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module SyntheticHomotopyTheory.Circle.index where

import SyntheticHomotopyTheory.Circle.Integers
import SyntheticHomotopyTheory.Circle.Integers-Properties
import SyntheticHomotopyTheory.Circle.Integers-SymmetricInduction

import SyntheticHomotopyTheory.Circle.Construction
import SyntheticHomotopyTheory.Circle.Induction

\end{code}

Updated in June 2026.

The following files use --rewriting and can therefore not be imported with
--safe. They are obviously still related to the circle so we list them here as
commented imports.

\begin{code}

-- import SyntheticHomotopyTheory.Circle.WithRewriting
-- import SyntheticHomotopyTheory.Circle.FundamentalGroup

\end{code}
