Tom de Jong, 31 October 2019

The following modules develop PCF and a constructive version of the Scott model
of PCF. This includes a constructive and predicative (i.e. without assuming
propositional resizing) treatment of dcpos with ⊥. In particular, we exhibit the
lifting of a set as a dcpo with ⊥.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PCFModules where

import PCF
import Dcpo
import DcpoConstructions
import ScottModelOfPCF

\end{code}
