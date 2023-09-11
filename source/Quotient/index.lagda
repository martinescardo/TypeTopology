\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Quotient.index where

import Quotient.Large
import Quotient.Type
import Quotient.FromSetReplacement
import Quotient.GivesSetReplacement
import Quotient.GivesPropTrunc
import Quotient.FromPropTrunc-F

\end{code}


 * Large

   Constructs large quotients from propositional truncations, function
   extensionality and propositional extensionality.

 * Type

   Defines small quotient type its basic theory.

 * FromSetReplacement

   Resizes down the above large quotients using set replacement to
   construct an element of the above type.

 * GivesSetReplacement

   Derives set replacement from quotients.

 * GivesPropTrunc

   Constructs propositional truncations from quotients and function
   extensionality.

 * FromPropTrunc-F

   Adds a parameter F to the large quotients module to control the
   universe where propositional truncation lives.
