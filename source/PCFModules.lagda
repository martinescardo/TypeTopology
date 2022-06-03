Tom de Jong, 31 October 2019

The following modules develop PCF and a constructive version of the Scott model
of PCF. This includes a constructive and predicative (i.e. without assuming
propositional resizing) treatment of pointed dcpos. In particular, we exhibit
the lifting of a set as a pointed dcpo.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PCFModules where

import PCF
import ScottModelOfPCF

import Dcpo
import DcpoMiscelanea
import DcpoExponential
import DcpoLeastFixedPoint
import DcpoPCFCombinators

\end{code}
