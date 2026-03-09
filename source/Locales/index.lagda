---
author: Ayberk Tosun
---

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

The `Locales.Frame` module contains preliminary definitions of locale theory.

\begin{code}

import Locales.Frame
import Locales.SIP.FrameSIP

\end{code}

\subsection{Terminal locale}

The modules below contain:

  1. Definition of the initial frame (i.e. the terminal locale)
  2. Properties of the terminal locale.

\begin{code}

import Locales.InitialFrame              -- (1)
import Locales.TerminalLocale.Properties -- (2)

\end{code}

\subsection{Sierpiński locale}

The modules below contain:

  1. Definition of the Sierpinski locale
  2. Properties of the Sierpinski locale
  3. Universal property of the Sierpinski locale

\begin{code}

import Locales.Sierpinski.Definition         -- (1)
import Locales.Sierpinski.Properties         -- (2)
import Locales.Sierpinski.UniversalProperty  -- (3)

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

\subsection{Continuous maps and frame homomorphisms}

The `ContinuousMap` subdirectory contains:

  1. Definition of the notion of frame homomorphism
  2. Properties of frame homomorphisms
  3. Definition of continuous maps of locales
  4. Properties of continuous maps
  5. Definition of frame isomorphisms
  6. Definition of locale homeomorphisms
  7. Properties of homeomorphisms, including the characterization of the
     identity type for locales

\begin{code}

import Locales.ContinuousMap.FrameHomomorphism-Definition  -- (1)
import Locales.ContinuousMap.FrameHomomorphism-Properties  -- (2)
import Locales.ContinuousMap.Definition                    -- (3)
import Locales.ContinuousMap.Properties                    -- (4)
import Locales.ContinuousMap.FrameIsomorphism-Definition   -- (5)
import Locales.ContinuousMap.Homeomorphism-Definition      -- (6)
import Locales.ContinuousMap.Homeomorphism-Properties      -- (7)

\end{code}

\subsection{Sublocales and nuclei}

The `Sublocale` subdirectory contains:

  1. Definition of the notion of nucleus along with some properties
  2. Properties of the image of a nucleus

\begin{code}

import Locales.Sublocale.Nucleus      -- (1)
import Locales.Sublocale.NucleusImage -- (2)

\end{code}

\subsection{Compactness and the way-below relation}

Compact opens.

The modules below contain:

  1. Definition of compact opens
  2. Properties of compact opens
  3. Characterization of compact locales

\begin{code}

import Locales.Compactness.Definition                        -- (1)
import Locales.Compactness.Properties                        -- (2)
import Locales.Compactness.CharacterizationOfCompactLocales  -- (3)

\end{code}

The way-below relation.

The modules below contain:

  1. Definition of the way-below relation
  2. Properties of the way-below relation

\begin{code}

import Locales.WayBelowRelation.Definition  -- (1)
import Locales.WayBelowRelation.Properties  -- (2)

\end{code}

\subsection{Clopens and the well-inside relation}

The modules below contain:

  1. Definition of clopens via Boolean complements, and basic closure properties
  2. Boolean complementation in frames, including preservation by frame
     homomorphisms
  3. Definition of the well-inside relation and basic order-theoretic properties

\begin{code}

import Locales.Clopen        -- (1)
import Locales.Complements   -- (2)
import Locales.WellInside    -- (3)

\end{code}

\subsection{Bases}

Notions of base for locales

\begin{code}

import Locales.SmallBasis

\end{code}

\subsection{Adjoint functor theorem for frames}

The modules below contain:

  1. Definition of posetal adjunctions
  2. General properties of adjunctions in the posetal setting
  3. Posetal adjoint functor theorem for frames
  4. Adjunction properties specialized to distributive lattices
  5. Heyting implication
  6. Heyting complementation

\begin{code}

import Locales.PosetalAdjunction                          -- (1)
import Locales.Adjunctions.Properties                     -- (2)
import Locales.AdjointFunctorTheoremForFrames             -- (3)
import Locales.Adjunctions.Properties-DistributiveLattice -- (4)
import Locales.HeytingImplication                         -- (5)
import Locales.HeytingComplementation                     -- (6)

\end{code}

\section{Spectral and Stone locales}

his section corresponds roughly to Chapter 4 of the thesis.

\subsection{Spectral locales}

The modules below contain:

  1. Definition of spectral locales
  2. Properties of spectral locales
  3. Definition of spectral maps
  4. Spectrality of the terminal locale
  5. Directification of bases
  6. Lattice of compact opens

\begin{code}

import Locales.Spectrality.SpectralLocale         -- (1)
import Locales.Spectrality.Properties             -- (2)
import Locales.Spectrality.SpectralMap            -- (3)
import Locales.Spectrality.SpectralityOfOmega     -- (4)
import Locales.Spectrality.BasisDirectification   -- (5)
import Locales.Spectrality.LatticeOfCompactOpens  -- (6)

\end{code}

\subsection{Distributive lattices}

The modules below contain:

  1.  Definition of distributive lattices
  2.  Σ-type-based definition of distributive lattices
  3.  Basic properties of distributive lattices
  4.  Homomorphisms of distributive lattices
  5.  Isomorphisms of distributive lattices
  6.  Properties of distributive lattice isomorphisms
  7.  Ideals of distributive lattices
  8.  Properties of ideals of distributive lattices
  9.  Resizing for distributive lattices
  10. Spectrum of a distributive lattice
  11. Properties of the frame of ideals over a distributive lattice
  12. Structure identity principle for distributive lattices

\begin{code}

import Locales.DistributiveLattice.Definition             -- (1)
import Locales.DistributiveLattice.Definition-SigmaBased  -- (2)
import Locales.DistributiveLattice.Properties             -- (3)
import Locales.DistributiveLattice.Homomorphism           -- (4)
import Locales.DistributiveLattice.Isomorphism            -- (5)
import Locales.DistributiveLattice.Isomorphism-Properties -- (6)
import Locales.DistributiveLattice.Ideal                  -- (7)
import Locales.DistributiveLattice.Ideal-Properties       -- (8)
import Locales.DistributiveLattice.Resizing               -- (9)
import Locales.DistributiveLattice.Spectrum               -- (10)
import Locales.DistributiveLattice.Spectrum-Properties    -- (11)
import Locales.SIP.DistributiveLatticeSIP                 -- (12)

\end{code}

\subsection{Zero-dimensional and regular locales}

The modules below contain:

  1. Definition of regular locales and some properties
  2. Definition of zero-dimensional locale and some properties

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

  1. Lattice duality for compact opens
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

  1. Construction of the patch locale (following Escardó's construction from
     previous work)
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

  1. Definition of the notion of point of a locale
  2. Properties of points
  3. Definition of spectral point

\begin{code}

import Locales.Point.Definition                -- (1)
import Locales.Point.Properties                -- (2)
import Locales.Point.SpectralPoint-Definition  -- (3)

\end{code}

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
  2. Directed families
  3. Directed families on posets

\begin{code}

import Locales.NotationalConventions  -- (1)
import Locales.DirectedFamily         -- (2)
import Locales.DirectedFamily-Poset   -- (3)

\end{code}

The module `Locales.CompactRegular` is legacy code that will soon be removed
once I untangle the dependency graph. Please DO NOT use these modules for new
developments.

\begin{code}

-- ↓ DEPRECATED DO NOT USE ↓ --
import Locales.CompactRegular
-- ↑ DEPRECATED DO NOT USE ↑ --

\end{code}
