Martin Escardo

The following imported files immplement the ideas advertised at the
Types 2019 meeting

  https://www.cs.bham.ac.uk/~mhe/papers/compact-ordinals-Types-2019-abstract.pdf

(navigate to them by clicking at their names).

As of 21st August 2019, this development has 9243 lines of code after
removing comments (and 13384 lines including the comments).

However, we rely on general results on other modules, including but
not limited to univalent foundations. The whole development has 25450
lines of code after removing comments (and 36006 including the
comments).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Types2019 where

import ADecidableQuantificationOverTheNaturals
import BasicDiscontinuityTaboo
import Compactness
import CompactTypes
import CoNaturalsArithmetic
import CoNaturalsExercise
import CoNaturals
import ConvergentSequenceCompact
import ConvergentSequenceInfCompact
import DecidabilityOfNonContinuity
import ExtendedSumCompact
import FailureOfTotalSeparatedness
import GenericConvergentSequence
import InfCompact
import InjectiveTypes
import LexicographicCompactness
import LexicographicOrder
import LPO
import OrdinalArithmetic
import OrdinalCodes
import OrdinalNotationInterpretation
import OrdinalNotions
import OrdinalOfOrdinals
import OrdinalOfTruthValues
import OrdinalsClosure
import Ordinals
import OrdinalsShulmanTaboo
import OrdinalsType
import OrdinalsWellOrderArithmetic
import PropInfTychonoff
import PropTychonoff
import SquashedCantor
import SquashedSum
import TotallySeparated
import WeaklyCompactTypes
import WLPO

\end{code}
