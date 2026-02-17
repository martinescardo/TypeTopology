\begin{code}

{-# OPTIONS --safe --without-K #-}

module Quotient.index where

import Quotient.Type
import Quotient.Large
import Quotient.FromSetReplacement
import Quotient.GivesSetReplacement
import Quotient.GivesPropTrunc
import Quotient.Effectivity
import Quotient.Large-Variation

\end{code}

 * Type

   Defines the existence of small quotients type and its basic theory.

 * Large

   Constructs large, effective quotients from propositional
   truncations, function extensionality and propositional
   extensionality.

 * FromSetReplacement

   Resizes down the above large quotients using set replacement to
   construct an element of the above type.

 * GivesSetReplacement

   Derives set replacement from quotients.

 * GivesPropTrunc

   Constructs propositional truncations from quotients and function
   extensionality.

 * Effectivity

   Shows that all quotients are effective.

 * Large-Variation

   Adds a parameter to the large quotients module to control the
   universe where propositional truncation lives.
