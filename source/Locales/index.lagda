Ayberk Tosun.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Locales.index where

import Locales.AdjointFunctorTheoremForFrames    -- (1)

import Locales.BooleanAlgebra                    -- (2)

import Locales.CharacterisationOfContinuity      -- (3)

import Locales.ClassificationOfScottOpens        -- (4)

import Locales.Clopen                            -- (5)

-- ↓ DEPRECATED DO NOT USE ↓ --
import Locales.CompactRegular                    -- (6)
-- ↑ DEPRECATED DO NOT USE ↑ --

import Locales.Compactness                       -- (7)

import Locales.Complements                       -- (8)

-- Distributive lattices
import Locales.DistributiveLattice.Definition
import Locales.DistributiveLattice.Homomorphism
import Locales.DistributiveLattice.Ideal
import Locales.DistributiveLattice.LocaleOfSpectra
import Locales.DistributiveLattice.Properties

import Locales.Frame                             -- (9)

import Locales.GaloisConnection                  -- (10)

import Locales.HeytingComplementation            -- (11)

import Locales.HeytingImplication                -- (12)

import Locales.InitialFrame                      -- (13)

import Locales.NotationalConventions             -- (14)

import Locales.Nucleus                           -- (15)

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

import Locales.SmallBasis                        -- (24)

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
import Locales.Spectrality.SpectralMapToLatticeHomomorphism

import Locales.Point.Definition                  -- (36)

import Locales.Point.Properties                  -- (37)

import Locales.TerminalLocale.Properties

import Locales.DiscreteLocale.Definition

import Locales.DiscreteLocale.Two
import Locales.DiscreteLocale.Two-Properties

\end{code}
