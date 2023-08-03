Martin Escardo & Tom de Jong, June 2023.

Iterative multisets, iterative sets, and iterative ordinals.

For an exposition of what is done here, see this post:
https://mathstodon.xyz/@MartinEscardo/110753930251021051

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Iterative.index where

import Iterative.Multisets
import Iterative.Sets
import Iterative.Ordinals
import Iterative.Multisets-Addendum
import Iterative.Sets-Addendum
import Iterative.Ordinals-Addendum

\end{code}

Abstract. Some of the development of "Set-Theoretic and Type-Theoretic
Ordinals Coincide" is carried out but using Gylterud's construction of
the cumulative hierarchy 𝕍 as iterative sets, instead of
(axiomatically) working with the higher inductive presentation. The
type 𝕆 of hereditarily transitive sets is the type of iterative
ordinals and corresponds to 𝕍ᵒʳᵈ in the original development
Ordinals.CumulativeHierarchy.lagda.

References.

  * Peter Aczel. "The Type Theoretic Interpretation of Constructive
    Set Theory". Studies in Logic and the Foundations of Mathematics,
    Volume 96, 1978, Pages 55-66.
    https://doi.org/10.1016/S0049-237X(08)71989-X

  * Gerald Leversha. "Formal Systems for Constructive Mathematics".
    PhD Thesis, 1976, The University of Manchester (United
    Kingdom). Department of Pure and Applied Mathematics.
    https://www.librarysearch.manchester.ac.uk/permalink/44MAN_INST/1r887gn/alma992983521804701631

  * Håkon Gylterud. "Multisets in type theory".  Mathematical
    Proceedings of the Cambridge Philosophical Society, Volume 169,
    Issue 1, 2020, pp. 1-18. https://doi.org/10.1017/S0305004119000045

  * H. R. Gylterud, "From multisets to sets in homotopy type theory".
    The Journal of Symbolic Logic, vol. 83, no. 3, pp. 1132–1146,
    2018. https://doi.org/10.1017/jsl.2017.84

  * Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and
    Chuangjie Xu. "Set-Theoretic and Type-Theoretic Ordinals
    Coincide". To appear at LICS 2023, June 2023.
    https://arxiv.org/abs/2301.10696

  * Elisabeth Bonnevier, Håkon Robbestad Gylterud, Daniel Gratzer, and
    Anders Mörtberg, "The category of iterative sets in HoTT".
    Workshop on Homotopy Type Theory/ Univalent Foundations
    Vienna, Austria, April 22-23, 2023
    https://hott-uf.github.io/2023/
