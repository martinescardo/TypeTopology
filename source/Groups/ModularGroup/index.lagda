Lane Biocini
21 January 2026

The modular group PSL(2,ℤ) ≅ ⟨s, r | s² = r³ = 1⟩ as a mutual inductive type.
Rather than constructing PSL(2,ℤ) as a quotient of matrices or a free group
modulo relations, we encode the Cayley graph structure directly, making the
relations s² = 1 and r³ = 1 hold definitionally.

The key insight which proved formative for this approach comes from Alperin's
"Rationals and the Modular Group": canonical words in PSL(2,ℤ) arise from
mutual induction, where generators must strictly alternate (S cannot follow S,
R's cycle through two states). Taking influence from Escardó's
InitialBinarySystem2, we use helper functions s, r : PSL2Z → PSL2Z as "smart
constructors" that reduce automatically via the group relations. The resulting
type has remarkably smooth computational properties.

From the Bass-Serre perspective, PSL(2,ℤ) ≅ ℤ/2ℤ * ℤ/3ℤ, and our encoding
is precisely the Bass-Serre tree for this free product: S-edge and R-edge
are the two vertex types (cosets of ⟨s⟩ and ⟨r⟩), and the mutual recursion
enforces the bipartite structure S → R → S → R that makes normal forms unique.
I intend to explore a more systematic treatment of this perspective in another
development.

Main results: PSL2Z is a set with decidable equality (Properties); it forms a
group 𝓜 with multiplication via generator iteration (Group); it satisfies the
expected universal property as an initial algebra (UniversalProperty); and we
characterize its automorphisms including twist : 𝓜 ≅ 𝓜 swapping r ↔ r² and
the opposite group isomorphism transpose : 𝓜 ≅ 𝓜ᵒᵖ (Group).

References:
  Alperin, R. "Rationals and the Modular Group"
  Conrad, K. "SL₂(ℤ)" (expository notes)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Groups.ModularGroup.index where

import Groups.ModularGroup.Type
import Groups.ModularGroup.Base
import Groups.ModularGroup.Properties
import Groups.ModularGroup.Induction
import Groups.ModularGroup.Multiplication
import Groups.ModularGroup.Inverse
import Groups.ModularGroup.Twist
import Groups.ModularGroup.Transposition
import Groups.ModularGroup.Group
import Groups.ModularGroup.UniversalProperty

\end{code}
