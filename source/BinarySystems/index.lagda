Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module BinarySystems.index where

import BinarySystems.InitialBinarySystem
import BinarySystems.InitialBinarySystem2
-- import BinarySystems.CubicalBinarySystem

\end{code}

The first construction does more work than needed. The second one improves
it, as there is no need to work with the subtype of normal elements.

The third one, by Martin Escardo and Alex Rice, works with Agda 2.6.2 and
needs the Cubical Library. It is commented out because it currently breaks
the build, and for that reason it is not rendered either. It can be read at

https://github.com/martinescardo/TypeTopology/blob/master/source/BinarySystems/CubicalBinarySystem.lagda
