-- Martin Escardo and Paulo Oliva 2011
--
-- For a tutorial at MFPS XXVII, Pittburgh, 27th May 2011 "Programs
-- from proofs", by Ulrich Berger, Monika Seisenberger, Martin Escardo
-- and Paulo Oliva.
--
-- Here are the slides for Martin Escardo's part of the tutorial:
-- http://www.cs.bham.ac.uk/~mhe/.talks/mfps2011/mfps2011.pdf
--
-- There is also this web page:
-- https://www.cs.bham.ac.uk/~mhe/pigeon/
--
-- This file implements the part "Classical countable choice via
-- products of selections functions". But it also implements classical
-- countable choice via the mbr and the bbc functionals. All of the
-- three of them fundamentally require the option --no-termination-check.

{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Pigeon.index where

import Pigeon.Addition
import Pigeon.Cantor
import Pigeon.Choice
import Pigeon.DataStructures
import Pigeon.Equality
import Pigeon.Examples
import Pigeon.Finite-JK-Shifts
import Pigeon.Finite
import Pigeon.FinitePigeon
import Pigeon.InfinitePigeon
import Pigeon.InfinitePigeon2011-05-12
import Pigeon.InfinitePigeonLessEfficient
import Pigeon.InfinitePigeonOriginal
import Pigeon.J-AC-N
import Pigeon.J-DC
import Pigeon.J-Examples
import Pigeon.J-FinitePigeon
import Pigeon.J-InfinitePigeon
import Pigeon.J-PigeonProgram
import Pigeon.J-Shift-BBC
import Pigeon.J-Shift-Selection
import Pigeon.J-Shift
import Pigeon.JK-LogicalFacts
import Pigeon.JK-Monads
import Pigeon.K-AC-N
import Pigeon.K-DC
import Pigeon.K-Shift-BBC
import Pigeon.K-Shift-MBR
import Pigeon.K-Shift-Selection
import Pigeon.K-Shift-from-J-Shift
import Pigeon.K-Shift
import Pigeon.Logic
import Pigeon.LogicalFacts
import Pigeon.Naturals
import Pigeon.Order
import Pigeon.PigeonProgram
import Pigeon.ProgramsWithoutSpecification
import Pigeon.ProgramsWithoutSpecificationBis
import Pigeon.Two
