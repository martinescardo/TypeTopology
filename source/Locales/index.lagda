Ayberk Tosun.

─────────────────────────────────────────────────────────────────────
This formalization accompanies Ayberk Tosun's PhD thesis:
  Constructive and Predicative Locale Theory in Univalent Foundations
  Ayberk Tosun
  School of Computer Science, University of Birmingham
  https://etheses.bham.ac.uk/id/eprint/16416/

  Updated versions:
  https://arxiv.org/abs/2603.01308

  Submitted: 30 November 2024
  Defended:  27 February 2025
  Accepted:   3 June     2025
─────────────────────────────────────────────────────────────────────

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Locales.index where

\end{code}

\section{Basic point-free topology}

The code under this section corresponds roughly to Chapter 3 of the thesis.

The `Locales.Frame` module contains the preliminary definitions related to
the theory of frames.

\begin{code}

import Locales.Frame

\end{code}

The `ContinuousMap` subdirectory contains:

  1. Definition of the notion of frame homomorphism.
  2. Properties of frame homomorphisms.
  3. Definition of continuous maps of locales
  4. Properties of continuous maps.
  5. Definition of locale homeomorphisms.
  6. Properties of homeomorphisms, including the characterization of the
     identity type for locales.

\begin{code}

import Locales.ContinuousMap.FrameHomomorphism-Definition -- (1)
import Locales.ContinuousMap.FrameHomomorphism-Properties -- (2)
import Locales.ContinuousMap.Definition                   -- (3)
import Locales.ContinuousMap.Properties                   -- (4)
import Locales.ContinuousMap.Homeomorphism-Definition     -- (5)
import Locales.ContinuousMap.Homeomorphism-Properties     -- (6)

\end{code}

Compact opens.

\begin{code}

import Locales.Compactness.Definition
import Locales.Compactness.Properties
import Locales.Compactness.CharacterizationOfCompactLocales

\end{code}

The way-below relation.

\begin{code}

import Locales.WayBelowRelation.Definition
import Locales.WayBelowRelation.Properties

\end{code}

\section{The discrete locale}

The `DiscreteLocale` directory contains

  1. Definition of the discrete locale over a set.
  2. Construction of a directed basis for the discrete locale.
  3. The discrete locale on the type of Booleans.
  4. Properties of the discrete locale on the type of Booleans.

\begin{code}

import Locales.DiscreteLocale.Basis
import Locales.DiscreteLocale.Definition
import Locales.DiscreteLocale.Two
import Locales.DiscreteLocale.Two-Properties

\end{code}

\begin{code}

import Locales.AdjointFunctorTheoremForFrames
import Locales.Adjunctions.Properties
import Locales.Adjunctions.Properties-DistributiveLattice

import Locales.BooleanAlgebra

import Locales.CharacterisationOfContinuity

import Locales.ClassificationOfScottOpens

import Locales.Clopen

-- ↓ DEPRECATED DO NOT USE ↓ --
import Locales.CompactRegular
-- ↑ DEPRECATED DO NOT USE ↑ --

import Locales.Compactness.Definition

import Locales.Complements

-- Distributive lattices
import Locales.DistributiveLattice.Definition
import Locales.DistributiveLattice.Definition-SigmaBased
import Locales.DistributiveLattice.Homomorphism
import Locales.DistributiveLattice.Ideal
import Locales.DistributiveLattice.Isomorphism
import Locales.DistributiveLattice.Isomorphism-Properties
import Locales.DistributiveLattice.Properties
import Locales.DistributiveLattice.Resizing
import Locales.DistributiveLattice.Spectrum
import Locales.DistributiveLattice.Spectrum-Properties


import Locales.GaloisConnection

import Locales.HeytingComplementation

import Locales.HeytingImplication

import Locales.InitialFrame

import Locales.NotationalConventions

import Locales.Nucleus
import Locales.NucleusImage

import Locales.PatchLocale

import Locales.PatchOfOmega

import Locales.PatchProperties

import Locales.PerfectMaps

import Locales.Regular

import Locales.ScottContinuity

import Locales.ScottLocale.Definition

import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
import Locales.ScottLocale.ScottLocalesOfScottDomains
import Locales.ScottLocale.Properties

import Locales.Sierpinski
import Locales.Sierpinski.Definition
import Locales.Sierpinski.Patch
import Locales.Sierpinski.Properties
import Locales.Sierpinski.UniversalProperty

import Locales.SmallBasis

import Locales.Stone

import Locales.StoneImpliesSpectral

import Locales.WellInside

import Locales.ZeroDimensionality

import Locales.Spectrality.SpectralLocale

import Locales.Spectrality.SpectralMap

import Locales.Spectrality.SpectralityOfOmega

-- with contribution by Igor Arrieta
import Locales.UniversalPropertyOfPatch

import Locales.Spectrality.BasisDirectification

import Locales.Spectrality.LatticeOfCompactOpens
import Locales.Spectrality.LatticeOfCompactOpens-Duality
import Locales.Spectrality.SpectralMapToLatticeHomomorphism

import Locales.Point.Definition
import Locales.Point.Properties
import Locales.Point.SpectralPoint-Definition

import Locales.TerminalLocale.Properties

import Locales.SIP.FrameSIP
import Locales.SIP.DistributiveLatticeSIP

import Locales.DirectedFamily-Poset

import Locales.StoneDuality.ForSpectralLocales

import Locales.LawsonLocale.CompactElementsOfPoint
import Locales.LawsonLocale.SharpElementsCoincideWithSpectralPoints
import Locales.LawsonLocale.PointsOfPatch

\end{code}
