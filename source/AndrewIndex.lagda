
Andrew Sneap - 27th April 2021

This file contains an index of the modules I have produced as part of
my project.  In Emacs, with Agda Mode installed and running, you can
type-check the code by typing "C-c C-l". The "C-c" command is
performed by holding the control button, followed by the c button (and
similarly for "C-l"). At the bottom, you will notice Agda compiling
the code, and will eventually have a bracketed result that says
(Agda:Checked). If there are no problems, the code should be syntax
highlight, and you can navigate the files by hovering over the name of
the file and clicking the middle mouse button. You can switch between
buffers by typing "C-x left-arrow" or "C-x right-arrow".

You can split buffers by typing "C-x 2" or "C-x 3" to see horizontal
splits or vertical splits respectively. You can return to a single
buffer view by typing "C-x 1" in the buffer you want to see.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module AndrewIndex where

import MoreNaturalProperties
import NaturalsOrderExtended
import NaturalsMultiplication
import NaturalsDivision
import HCF

import IntegersB
import IntegersAbs
import IntegersAddition
import IntegersOrder
import IntegersDivision
import IntegersHCF
import IntegersMultiplication
import IntegersNegation

import ncRationals
import ncRationalsOperations
import ncRationalsOrder

import FieldAxioms

import Rationals
import RationalsAbs
import RationalsAddition
import RationalsExtension
import RationalsField
import RationalsLimits
import RationalsMinMax
import RationalsMultiplication
import RationalsNegation
import RationalsOrder

import DedekindReals
-- import DedekindRealsAddition
import DedekindRealsProperties
import DedekindRealsOrder

import MetricSpaceAltDef
import MetricSpaceRationals
-- import MetricSpaceDedekindReals

-- import ContinuousExtensionTheorem

import FieldRationals


\end{code}
