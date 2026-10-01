Martin Escardo, August 2020 and September 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module BinarySystems.index where

import BinarySystems.Type
import BinarySystems.Initiality
import BinarySystems.TypeOriginal

\end{code}

The construction in BinarySystems.TypeOriginal does more work than
needed, by working with a subtype of normal elements. The one in
BinarySystems.Type avoids this, giving rise to a more direct and
simpler construction.

A third one, by Martin Escardo and Alex Rice, works with Agda 2.6.2
and needs the Cubical Library. It currently breaks the build and so
cannot be rendered in html, which is also why it is not imported, but
it can be read at

https://github.com/martinescardo/TypeTopology/blob/master/source/BinarySystems/CubicalType.lagda
