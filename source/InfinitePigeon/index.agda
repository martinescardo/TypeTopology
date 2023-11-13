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

{-# OPTIONS --without-K #-}

module InfinitePigeon.index where

import InfinitePigeon.Addition
import InfinitePigeon.Cantor
import InfinitePigeon.Choice
import InfinitePigeon.DataStructures
import InfinitePigeon.Equality
import InfinitePigeon.Examples
import InfinitePigeon.Finite-JK-Shifts
import InfinitePigeon.Finite
import InfinitePigeon.FinitePigeon
import InfinitePigeon.InfinitePigeon
import InfinitePigeon.InfinitePigeon2011-05-12
import InfinitePigeon.InfinitePigeonLessEfficient
import InfinitePigeon.InfinitePigeonOriginal
import InfinitePigeon.J-AC-N
import InfinitePigeon.J-DC
import InfinitePigeon.J-Examples
import InfinitePigeon.J-FinitePigeon
import InfinitePigeon.J-InfinitePigeon
import InfinitePigeon.J-PigeonProgram
import InfinitePigeon.J-Shift-BBC
import InfinitePigeon.J-Shift-Selection
import InfinitePigeon.J-Shift
import InfinitePigeon.JK-LogicalFacts
import InfinitePigeon.JK-Monads
import InfinitePigeon.K-AC-N
import InfinitePigeon.K-DC
import InfinitePigeon.K-Shift-BBC
import InfinitePigeon.K-Shift-MBR
import InfinitePigeon.K-Shift-Selection
import InfinitePigeon.K-Shift-from-J-Shift
import InfinitePigeon.K-Shift
import InfinitePigeon.Logic
import InfinitePigeon.LogicalFacts
import InfinitePigeon.Naturals
import InfinitePigeon.Order
import InfinitePigeon.PigeonProgram
import InfinitePigeon.ProgramsWithoutSpecification
import InfinitePigeon.ProgramsWithoutSpecificationBis
import InfinitePigeon.Two
