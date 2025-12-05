Ayberk Tosun.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Locales.index where

\end{code}

There is a separate index file for the thesis:

\begin{code}

import Locales.ThesisIndex

\end{code}

\section{Basics}

Basics of frames and quite a bit of order theory.

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

import Locales.AdjointFunctorTheoremForFrames    -- (1)
import Locales.Adjunctions.Properties
import Locales.Adjunctions.Properties-DistributiveLattice

import Locales.BooleanAlgebra                    -- (2)

import Locales.CharacterisationOfContinuity      -- (3)

import Locales.ClassificationOfScottOpens        -- (4)

import Locales.Clopen                            -- (5)

-- ↓ DEPRECATED DO NOT USE ↓ --
import Locales.CompactRegular                    -- (6)
-- ↑ DEPRECATED DO NOT USE ↑ --

import Locales.Compactness.Definition            -- (7)

import Locales.Complements                       -- (8)

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


import Locales.GaloisConnection                  -- (10)

import Locales.HeytingComplementation            -- (11)

import Locales.HeytingImplication                -- (12)

import Locales.InitialFrame                      -- (13)

import Locales.NotationalConventions             -- (14)

import Locales.Nucleus                           -- (15)
import Locales.NucleusImage

import Locales.PatchLocale                       -- (16)

import Locales.PatchOfOmega                      -- (17)

import Locales.PatchProperties                   -- (18)

import Locales.PerfectMaps                       -- (19)

import Locales.Regular                           -- (20)

import Locales.ScottContinuity                   -- (21)

import Locales.ScottLocale.Definition            -- (22)

import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
import Locales.ScottLocale.ScottLocalesOfScottDomains
import Locales.ScottLocale.Properties

import Locales.Sierpinski                        -- (23)
import Locales.Sierpinski.Definition
import Locales.Sierpinski.Patch
import Locales.Sierpinski.Properties
import Locales.Sierpinski.UniversalProperty

import Locales.SmallBasis

import Locales.Stone                             -- (25)

import Locales.StoneImpliesSpectral              -- (26)

import Locales.WellInside                        -- (27)

import Locales.ZeroDimensionality                -- (28)

import Locales.Spectrality.SpectralLocale        -- (29)

import Locales.Spectrality.SpectralMap           -- (30)

import Locales.Spectrality.SpectralityOfOmega    -- (31)

import Locales.WayBelowRelation.Definition       -- (32)

import Locales.WayBelowRelation.Properties       -- (33)

-- with contribution by Igor Arrieta
import Locales.UniversalPropertyOfPatch          -- (34)

import Locales.Spectrality.BasisDirectification  -- (35)

import Locales.Spectrality.LatticeOfCompactOpens
import Locales.Spectrality.LatticeOfCompactOpens-Duality
import Locales.Spectrality.SpectralMapToLatticeHomomorphism

import Locales.Point.Definition                  -- (36)
import Locales.Point.Properties                  -- (37)
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
