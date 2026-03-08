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
import Locales.SIP.FrameSIP

\end{code}

\subsection{Basic examples of locales}

\begin{code}

import Locales.InitialFrame
import Locales.TerminalLocale.Properties

\end{code}

The `ContinuousMap` subdirectory contains:

  1. Definition of the notion of frame homomorphism
  2. Properties of frame homomorphisms
  3. Definition of continuous maps of locales
  4. Properties of continuous maps
  5. Definition of locale homeomorphisms
  6. Properties of homeomorphisms, including the characterization of the
     identity type for locales

\begin{code}

import Locales.ContinuousMap.FrameHomomorphism-Definition -- (1)
import Locales.ContinuousMap.FrameHomomorphism-Properties -- (2)
import Locales.ContinuousMap.Definition                   -- (3)
import Locales.ContinuousMap.Properties                   -- (4)
import Locales.ContinuousMap.Homeomorphism-Definition     -- (5)
import Locales.ContinuousMap.Homeomorphism-Properties     -- (6)

\end{code}

The `Sublocale` subdirectory contains:

  1. Definition of the notion of nucleus along with some properties
  2. Properties of the image of a nucleus

\begin{code}

import Locales.Sublocale.Nucleus      -- (1)
import Locales.Sublocale.NucleusImage -- (2)

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

Clopens and the well-inside relation.

\begin{code}

import Locales.Clopen
import Locales.Complements
import Locales.WellInside

\end{code}

\subsection{The discrete locale}

The modules below contain:

  1. Definition of the discrete locale over a set
  2. Construction of a directed basis for the discrete locale
  3. The discrete locale on the type of Booleans
  4. Properties of the discrete locale on the type of Booleans

\begin{code}

import Locales.DiscreteLocale.Definition     -- (1)
import Locales.DiscreteLocale.Basis          -- (2)
import Locales.DiscreteLocale.Two            -- (3)
import Locales.DiscreteLocale.Two-Properties -- (4)

\end{code}

\subsection{Bases}

Notions of base for locales

\begin{code}

import Locales.SmallBasis

\end{code}

\subsection{Adjoint functor theorem for frames}

The modules below contain:

  1. The adjoint functor theorem for frames
  2. General properties of adjunctions
  3. Adjunction properties specialized to distributive lattices
  4. Heyting implication
  5. Heyting complementation
  6. Posetal adjunctions

\begin{code}

import Locales.AdjointFunctorTheoremForFrames             -- (1)
import Locales.Adjunctions.Properties                     -- (2)
import Locales.Adjunctions.Properties-DistributiveLattice -- (3)
import Locales.HeytingImplication                         -- (4)
import Locales.HeytingComplementation                     -- (5)
import Locales.PosetalAdjunction                           -- (6)

\end{code}

\subsection{The Sierpinski locale}

The modules below contain:

  1. The Sierpinski locale
  2. Definition of the Sierpinski locale
  3. Properties of the Sierpinski locale
  4. Universal property of the Sierpinski locale

\begin{code}

import Locales.Sierpinski                    -- (1)
import Locales.Sierpinski.Definition         -- (2)
import Locales.Sierpinski.Properties         -- (3)
import Locales.Sierpinski.UniversalProperty  -- (4)

\end{code}

\section{Spectral and Stone locales}

This section corresponds roughly to Chapter 4 of the thesis.

\subsection{Spectral locales}

The modules below contain:

  1. Definition of spectral locales
  2. Definition of spectral maps
  3. Spectrality of the locale of opens of a discrete space
  4. Directification of bases
  5. The lattice of compact opens

\begin{code}

import Locales.Spectrality.SpectralLocale         -- (1)
import Locales.Spectrality.SpectralMap            -- (2)
import Locales.Spectrality.SpectralityOfOmega     -- (3)
import Locales.Spectrality.BasisDirectification   -- (4)
import Locales.Spectrality.LatticeOfCompactOpens  -- (5)

\end{code}

\subsection{Distributive lattices}

The modules below contain:

  1. Definition of distributive lattices
  2. Σ-type-based definition of distributive lattices
  3. Homomorphisms of distributive lattices
  4. Ideals of distributive lattices
  5. Isomorphisms of distributive lattices
  6. Properties of distributive lattice isomorphisms
  7. Basic properties of distributive lattices
  8. Resizing for distributive lattices
  9. Spectrum of a distributive lattice
  10. Properties of the distributive-lattice spectrum
  11. Structure identity principle for distributive lattices

\begin{code}

import Locales.DistributiveLattice.Definition             -- (1)
import Locales.DistributiveLattice.Definition-SigmaBased  -- (2)
import Locales.DistributiveLattice.Homomorphism           -- (3)
import Locales.DistributiveLattice.Ideal                  -- (4)
import Locales.DistributiveLattice.Isomorphism            -- (5)
import Locales.DistributiveLattice.Isomorphism-Properties -- (6)
import Locales.DistributiveLattice.Properties             -- (7)
import Locales.DistributiveLattice.Resizing               -- (8)
import Locales.DistributiveLattice.Spectrum               -- (9)
import Locales.DistributiveLattice.Spectrum-Properties    -- (10)
import Locales.SIP.DistributiveLatticeSIP                 -- (11)

\end{code}

\subsection{Zero-dimensional and regular locales}

The modules below contain:

  1. Regular locales
  2. Zero-dimensional locales

\begin{code}

import Locales.Regular            -- (1)
import Locales.ZeroDimensionality -- (2)

\end{code}

\subsection{Stone locales}

The modules below contain:

  1. Stone locales
  2. Boolean algebras
  3. Inclusion of Stone locales into spectral locales

\begin{code}

import Locales.Stone                -- (1)
import Locales.BooleanAlgebra       -- (2)
import Locales.StoneImpliesSpectral -- (3)

\end{code}

\subsection{Stone duality}

The modules below contain:

  1. Lattice-duality results for compact opens
  2. The map from spectral maps to lattice homomorphisms
  3. Perfect maps in the spectral setting
  4. Stone duality for spectral locales

\begin{code}

import Locales.Spectrality.LatticeOfCompactOpens-Duality     -- (1)
import Locales.Spectrality.SpectralMapToLatticeHomomorphism  -- (2)
import Locales.PerfectMaps                                   -- (3)
import Locales.StoneDuality.ForSpectralLocales               -- (4)

\end{code}

\section{The patch locale}

The modules below contain:

  1. Construction of the patch locale
  2. Properties of the patch locale
  3. The universal property of the patch locale (with contributions by
     Igor Arrieta)

\begin{code}

import Locales.PatchLocale              -- (1)
import Locales.PatchProperties          -- (2)
import Locales.UniversalPropertyOfPatch -- (3)

\end{code}

\subsection{Examples of patch}

The modules below contain:

  1. Patch locale of the terminal locale
  2. Patch locale of the Sierpiński locale

\begin{code}

import Locales.PatchOfOmega     -- (1)
import Locales.Sierpinski.Patch -- (2)

\end{code}

\section{Point-free topology of domains}

\subsection{Construction of the Scott locale}

The modules below contain:

  1. Definition of the Scott locale
  2. Properties of the Scott locale
  3. Scott locales of algebraic dcpos
  4. Scott locales of Scott domains

\begin{code}

import Locales.ScottLocale.Definition                    -- (1)
import Locales.ScottLocale.Properties                    -- (2)
import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos  -- (3)
import Locales.ScottLocale.ScottLocalesOfScottDomains    -- (4)

\end{code}

\subsection{Scott continuity}

The modules below contain:

  1. Scott continuity
  2. Characterization of continuity
  3. Classification of Scott opens

\begin{code}

import Locales.ScottContinuity               -- (1)
import Locales.CharacterisationOfContinuity  -- (2)
import Locales.ClassificationOfScottOpens    -- (3)

\end{code}

\subsection{Spectral points of the Scott locale}

The modules below contain:

  1. Definition of points of a locale
  2. Properties of points
  3. Definition of spectral points

\begin{code}

import Locales.Point.Definition                -- (1)
import Locales.Point.Properties                -- (2)
import Locales.Point.SpectralPoint-Definition  -- (3)

\end{code}

\subsection{Spectral points coincide with the points of patch}

The modules below contain:

  1. Compact elements of a point
  2. Sharp elements coincide with spectral points
  3. Points of the patch locale

\begin{code}

import Locales.LawsonLocale.CompactElementsOfPoint                  -- (1)
import Locales.LawsonLocale.SharpElementsCoincideWithSpectralPoints -- (2)
import Locales.LawsonLocale.PointsOfPatch                           -- (3)

\end{code}

\section{Miscellaneous}

The modules below contain:

  1. Notational conventions for spectral locales
  2. Directed families on posets

\begin{code}

import Locales.NotationalConventions  -- (1)
import Locales.DirectedFamily-Poset   -- (2)

\end{code}

The module `Locales.CompactRegular` is legacy code that will soon be removed
once I untangle the dependency graph. Please DO NOT use these modules for new
developments.

\begin{code}

-- ↓ DEPRECATED DO NOT USE ↓ --
import Locales.CompactRegular
-- ↑ DEPRECATED DO NOT USE ↑ --

\end{code}
